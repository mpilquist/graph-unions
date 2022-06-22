# Disjoint Graph Unions: Performance Case Study

I recently came across an interesting problem:

> Given a set of directed graphs with the property that no two graphs share an edge, compute the set of graphs with the same total set of edges & vertices which has the additional property that no two graphs share a vertex.

That is, each graph in the output should be the union of the graphs from the input which have at least one vertex in common. In this article, we'll look at how to efficiently implement this computation in Scala.

For starters, we'll need a representation of a graph. One common implementation is an [adjacencty list](https://en.wikipedia.org/wiki/Adjacency_list), where an edge from `a` to `b` is represented as `b` being in the set under entry `a` in a map:

```scala mdoc
case class Vertex(id: Int)
case class Graph(adjacencies: Map[Vertex, Set[Vertex]]):
  override def toString: String =
    adjacencies
      .toVector
      .sortBy((k, _) => k.id)
      .map((k, vs) => (k, vs.toVector.sortBy(_.id)))
      .map((k, vs) => s"""${k.id} -> {${vs.map(_.id).mkString("\n")}}""")
      .mkString("Graph(", ", ", ")")

object Graph:
  def apply(edges: (Int, Int)*): Graph =
    withVertices(edges.map((f, t) => (Vertex(f), Vertex(t)))*)

  def withVertices(edges: (Vertex, Vertex)*): Graph =
    val adjacencies =
      edges.foldLeft(Map.empty[Vertex, Set[Vertex]]) { case (acc, (from, to)) =>
        acc.updated(from, acc.getOrElse(from, Set.empty) + to).updated(to, acc.getOrElse(to, Set.empty))
      }
    Graph(adjacencies)
```

```scala mdoc
val g1 = Graph(1 -> 2, 2 -> 3)
```

Our goal is to come up with an implementation of `union`:

```scala
def union(gs: Vector[Graph]): Vector[Graph] = ???
```

Let's consider a few examples. First, let's consider some simple cases:
- empty input: `union(Vector.empty) == Vector.empty`
- singleton input: `union(Vector(g)) == Vector(g)` for every graph `g`

And some examples that perform unions:
- `union(Vector(Graph(1 -> 2), Graph(2 -> 3))) == Vector(Graph(1 -> 2, 2 -> 3))`
- `union(Vector(Graph(1 -> 2), Graph(3 -> 4), Graph(2 -> 3)) == Vector(Graph(1 -> 2, 2 -> 3, 3 -> 4))`

And another that takes disjoint graphs as input:
- `union(Vector(Graph(1 -> 2), Graph(3 -> 4))) == Vector(Graph(1 -> 2), Graph(3 -> 4))`

We can generalize the two non-trivial examples to more general laws:
- given `gs: Vector[Graph]` such that all members have the same vertex set, `union(gs) = Vector(u)` where `u` is the union of all edge sets in `gs`
- given `gs: Vector[Graph]` such that all members have disjoint vertex sets, `union(gs) == gs`

We can also say that the union of input graphs must be equal to the union of all the output graphs (that is, the total set of edges & vertices are the same).

Let's write these laws as a [ScalaCheck](https://scalacheck.org/) test. For starters, we'll need a generator for graphs:

```scala mdoc
import org.scalacheck.{Arbitrary, Gen, Prop, Properties, Test}

def genGraph(edgeFactor: Double = 0.1, maxVertexId: Int = 1 << 15): Gen[Graph] =
  Gen.sized { size =>
    val genVertexId = Gen.long.map(x => (x % maxVertexId).abs.toInt)
    val genEdge = for
      f <- genVertexId
      t <- genVertexId
    yield (f, t)
    val maxEdges = (size * edgeFactor).toInt max 1
    for
      numEdges <- Gen.long.map(x => 1 + (x % maxEdges).abs.toInt)
      es <- Gen.listOfN(numEdges, genEdge)
    yield Graph(es*)
  }

given arbitraryGraph: Arbitrary[Graph] = Arbitrary(genGraph())
```

There's a bit of fine tuning going on here. The `edgeFactor` parameter, when multiplied by the configured generator size, specifies the maximum number of edges that should be included in each graph. The `maxVertexId` parameter specifies the maximum vertex id. If we keep `edgeFactor` constant while reducing `maxVertexId`, we increase the likelihood of vertex overlaps between generated graphs.

Given this generator, we can define various properties for each of the laws we came up with:

```scala mdoc
/** Returns true if the arguments have at least one vertex in common. */
def overlaps(g1: Graph, g2: Graph): Boolean =
  g1.adjacencies.keySet.exists(g2.adjacencies.keySet.contains)

def testUnion(union: Vector[Graph] => Vector[Graph]) = new Properties("union"):
  property("empty") = Prop.secure(union(Vector.empty) == Vector.empty)

  property("singleton") = Prop.forAll((g: Graph) => union(Vector(g)) == Vector(g))

  property("duplicates") = Prop.forAll((g: Graph) => union(Vector(g, g)) == Vector(g))

  property("outputs disjoint") = Prop.forAll { (gs: Vector[Graph]) =>
    val us = union(gs)
    us.forall(u => us.forall(u2 => (u eq u2) || !overlaps(u, u2)))
  }

  property("inputs disjoint") = Prop.forAll { (gs0: Vector[Graph]) =>
    // Re-index vertices so they don't overlap
    val gs = gs0.zipWithIndex.map { (g, idx) =>
      val offset = idx * 1000000
      Graph(g.adjacencies.map((k, vs) => (Vertex(k.id + offset), vs.map(v => Vertex(v.id + offset)))))
    }
    union(gs) == gs
  }

  property("same edges and vertices") = Prop.forAll { (gs: Vector[Graph]) =>
    import cats.syntax.all.*
    // adjacencies is a Map[Vertex, Set[Vertex]] so we can merge
    // all edges & vertices by folding with the map monoid
    gs.foldMap(_.adjacencies) == union(gs).foldMap(_.adjacencies)
  }
```

Note how the union of all edges & vertices was calculated in the final property -- using `foldMap`. We could further simplify this by defining a `Monoid[Graph]` instance and using `combineAll` in place of `foldMap(_.adjacencies)`:

```scala mdoc
import cats.Monoid
import cats.syntax.all.*

given Monoid[Graph] with
  def empty = Graph()
  def combine(x: Graph, y: Graph): Graph =
    Graph(x.adjacencies |+| y.adjacencies)

def alternateDefinition(union: Vector[Graph] => Vector[Graph]): Prop =
  Prop.forAll { (gs: Vector[Graph]) =>
    gs.combineAll == union(gs).combineAll
  }
```

Given this test definition, let's try testing with various wrong but instructive functions in place of union:
```scala mdoc
def runUnionTest(union: Vector[Graph] => Vector[Graph]): Unit =
  testUnion(union).check(
    Test.Parameters.default
      .withMinSuccessfulTests(200)
      .withInitialSeed(0L) // Generate same results on each run
  )

runUnionTest(identity)

runUnionTest(_ => Vector.empty)
```

## A First Solution

As an initial attempt at implementing `union`, let's try folding over each input graph, accumulating disjoint graphs. For each input graph, we can search the disjoint graphs, looking for overlap. If we find an overlap, then we replace that element with the merge of the input and the old element. Otherwise, we add the new graph as a new disjoint graph.

```scala mdoc
def unionFirst(gs: Vector[Graph]): Vector[Graph] =
  gs.foldLeft(Vector.empty[Graph]) { (acc, g) =>
    val idx = acc.indexWhere(overlaps(g, _))
    if idx < 0 then acc :+ g
    else acc.updated(idx, acc(idx) |+| g)
  }
```

An initial test look promising:

```scala mdoc
println(unionFirst(Vector(Graph(1 -> 2, 3 -> 4), Graph(2 -> 3))))
```

A more slightly more complicated test reveals an error though:

```scala mdoc
println(unionFirst(Vector(Graph(1 -> 2), Graph(3 -> 4), Graph(2 -> 3))))
```

When the second input graph is processed, it's disjoint with all the graphs processed so far (i.e., the first graph). When the third graph is processed, it's merged with the first, resulting in an output of two graphs. But those two graphs share a common vertex of 3. It seems that each time we merge graphs, we need to reconsider whether the disjoint set is still disjoint. More on that in a moment. First, let's run our test on this implementation and see if it also finds a counterexample:

```scala mdoc
runUnionTest(unionFirst)
```

Okay, so when we merge a graph in to the disjoint set, two entries that were previously disjoint may no longer be disjoint. We could fix our issue by recursively calling our union function after merging -- i.e. `unionFirst(acc.updated(idx, acc(idx) |+| g))` -- but doing so wouldn't be tail recursive. Instead, we could run the full fold and when it completes, check if we've done any merges. If so, we recurse and otherwise we return. We can test if we've done merges by comparing the size of the input to the size of the output.


```scala mdoc
def unionRecursive(gs: Vector[Graph]): Vector[Graph] =
  val out = gs.foldLeft(Vector.empty[Graph]) { (acc, g) =>
    val idx = acc.indexWhere(overlaps(g, _))
    if idx < 0 then acc :+ g
    else acc.updated(idx, acc(idx) |+| g)
  }
  if gs.size == out.size then out else unionRecursive(out)
```

This is the same implementation as `unionFirst` except the final statement, which compares the size of the input to the size of the output. If they are the same, then we've done no merges and we return the result. Otherwise, we recurse on the output.

This version works with our problematic example:

```scala mdoc
println(unionRecursive(Vector(Graph(1 -> 2), Graph(3 -> 4), Graph(2 -> 3))))
```

And it passes all of our laws:

```scala mdoc
runUnionTest(unionRecursive)
```

Let's see how it performs on large inputs. We'll need a way to time execution and a way to generate large inputs consistently (i.e., the same input run after run).

```scala mdoc
def time[A](a: => A): (Long, A) =
  import scala.concurrent.duration.*
  val started = System.nanoTime
  val result = a
  val elapsed = (System.nanoTime - started).nanos.toMillis
  (elapsed, result)

def generateGraphs(num: Int, maxVertexId: Int): Vector[Graph] =
  val seed = org.scalacheck.rng.Seed(0L)
  Gen.listOfN(num, genGraph(maxVertexId = maxVertexId))
    .pureApply(Gen.Parameters.default, seed).toVector

case class Stats(n: Int, min: Int, max: Int, mean: Double):
  override def toString: String =
    f"count $n min $min max $max mean $mean%.2f"

object Stats:
  def sample(x: Int) = Stats(1, x, x, x)

given Monoid[Stats] with
  def empty = Stats(0, Int.MaxValue, Int.MinValue, 0)
  def combine(x: Stats, y: Stats) =
    val n = x.n + y.n
    val mean = if n == 0 then 0 else (x.n / n.toDouble) * x.mean + (y.n / n.toDouble) * y.mean
    Stats(n, x.min min y.min, x.max max y.max, mean)

def describe(gs: Vector[Graph]): String =
  val (statsVertices, statsEdges) = gs.foldMap(g =>
    Stats.sample(g.adjacencies.size) -> Stats.sample(g.adjacencies.values.map(_.size).sum))
  s"Vertices: $statsVertices\nEdges: $statsEdges"

def performance(label: String, numGraphs: Int, maxVertexId: Int, union: Vector[Graph] => Vector[Graph]): Unit =
  val (elapsedGeneration, gs) = time(generateGraphs(numGraphs, maxVertexId))
  println(s"---- $label -----------------------------------------")
  println(s"Took $elapsedGeneration millis to generate")
  println(describe(gs))
  val (elapsedUnion, us) = time(union(gs))
  println(s"Reduced from ${gs.size} to ${us.size} in $elapsedUnion millis")

def runPerformanceSuite(union: Vector[Graph] => Vector[Graph]): Unit =
  performance("10K less disjoint", 10000, 1 << 15, union)
  performance("10K more disjoint", 10000, 1 << 20, union)
  performance("100K less disjoint", 100000, 1 << 20, union)

runPerformanceSuite(unionRecursive)
```

This initial algorithm seems to be pretty fast when there's a lot of overlap -- that is, when the final disjoint set has a small number of elements. This makes sense, as this algorithm makes use of an `indexWhere` on the accumulated disjoint set for each element. In the worst case, where the input set is fully disjoint, this algorithm is quadratic in the number of graphs. In the context I first encountered this problem, the input generally reduced by ~50% and the total input size was roughly 500K graphs with, on average, less than 10 vertices per graph. Hence, this solution was not suitable and I needed something that performed better for this data set.

## A Faster Solution

The key to a faster solution is avoiding a linear scan of the accumulated disjoint graphs on each iteration. The `indexWhere` is searching for overlapping graphs. Instead of searching, we can carry a lookup table that maps each vertex to an index in the accumulated disjoint graph vector. For example, if the disjoint graphs vector contains two graphs with vertices `{1, 2}, {3, 4}` then the lookup table would contain `{1 -> 0, 2 -> 0, 3 -> 1, 4 -> 1}`, indicating vertices 1 and 2 are at index 0 in the disjoint graphs vector while vertices 3 and 4 are at index 1.

With this lookup table, we can replace a linear scan (i.e. `indexWhere`) with an effective constant time lookup (per vertex in the graph in question). Determining the intersecting disjoint graphs can be accomplished by looking up each vertex in the index map and taking the union of the results. If the result is empty, then the graph in question is disjoint with all other accumulated graphs. If the result is non-empty, then the graph intersects each of the corresponding disjoint graphs. In this case, we must take the union of each of these graphs with the graph in question and store it at a new index. There's some bookkeeping in updating the lookup table for each vertex in the resulting merged graph. And we can be efficient about the bookkeeping by only computing new lookup table entries for the graphs which are changing positions (that is, there's no need to update the indices of the vertices of the graph that was at the target index, since those vertices aren't changing position). In the case of multiple matching indices, we choose the minimum index so that overall, smaller indices have larger vertex sets. There's one catch however -- when there are multiple intersecting disjoint graphs, what do we do with the *other* indices -- the ones that differ from the target index? We can update those entries to `null` and upon overall completion, filter out the `null` values.

```scala mdoc
def unionFast(gs: Vector[Graph]): Vector[Graph] =
  gs.foldLeft(Vector.empty[Graph], Map.empty[Vertex, Int]) { case ((acc, lookup), g) =>
    // Find indices of graphs with overlapping vertices
    val vertices = g.adjacencies.keySet
    val indices = vertices.flatMap(v => lookup.get(v))
    if indices.isEmpty then (acc :+ g, lookup ++ vertices.iterator.map(_ -> acc.size))
    else
      // Pick an index to be the target index for the merger of all intersecting graphs and g
      // We pick the minimum index so that smaller indices, on average, tend to be larger in vertex count
      val newIndex = indices.min
      val otherIndices = indices - newIndex
      val merged = otherIndices.foldLeft(acc(newIndex))((m, i) => m |+| acc(i)) |+| g
      // Null out each other index & fix up vertex lookup table to point to new index
      val newLookup = lookup ++ vertices.iterator.map(_ -> newIndex)
      otherIndices.foldLeft((acc.updated(newIndex, merged), newLookup)) { case ((newAcc, newLookup), idx) =>
        newAcc.updated(idx, null) -> (newLookup ++ acc(idx).adjacencies.keySet.iterator.map(_ -> newIndex))
      }
  }(0).filterNot(_ eq null)
```

The implementation passes all of our tests:
```scala mdoc
runUnionTest(unionFast)
```

How about performance?

```scala mdoc
runPerformanceSuite(unionFast)
```

This performs significantly faster than `unionRecursive`, especially when the input is mostly disjoint. In a real world data set, this implementation proved to be thousands of times faster than `unionRecursive`. This ended up being the difference between completely infeasible to pleasantly adequate.

## Final Thoughts

During the development of this algorithm, various profiling techniques were used, including the crude `println` and `time` based debugging used in this article as well as the use of industrial strength JVM profilers. Often the profilers would provide important clues as to where the issues were but would often also lead to micro-optimizations of existing implementations. As is often the case in performance work, a key technique in the development of this algorithm was determining what work we *did not* need to do, and devising ways to avoid doing that work.
