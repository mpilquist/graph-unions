# Graph Unions

I recently came across an interesting problem:

> Given a set of directed graphs with the property that no two graphs share an edge, compute the set of graphs with the same total set of edges & vertices which has the additional property that no two graphs share a vertex.

That is, each graph in the output should be the union of the graphs from the input which have at least one vertex in common. In this article, we'll look at how to efficiently implement this computation in Scala.

For starters, we'll need a representation of a graph. One common implementation is an [adjacencty list](https://en.wikipedia.org/wiki/Adjacency_list), where an edge from `a` to `b` is represented as `b` being in the set under entry `a` in a map:

```scala
case class Vertex(id: Int)
case class Graph(adjacencies: Map[Vertex, Set[Vertex]])

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

```scala
val g1 = Graph(1 -> 2, 2 -> 3)
// g1: Graph = Graph(
//   adjacencies = Map(
//     Vertex(id = 1) -> Set(Vertex(id = 2)),
//     Vertex(id = 2) -> Set(Vertex(id = 3)),
//     Vertex(id = 3) -> Set()
//   )
// )
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

```scala
import org.scalacheck.{Arbitrary, Gen, Prop, Properties}

def genGraph: Gen[Graph] = Gen.sized { size =>
  val maxVertexId = 2 * size
  val genEdge = for
    f <- Gen.chooseNum(0, maxVertexId)
    t <- Gen.chooseNum(0, maxVertexId)
  yield (f, t)
  Gen.listOf(genEdge)
    .filter(_.nonEmpty)
    .map(es => Graph(es*))
}

given arbitraryGraph: Arbitrary[Graph] = Arbitrary(genGraph)
```

Given this generator, we can define various properties for each of the laws we came up with:

```scala
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

```scala
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
```scala
testUnion(identity).check()
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 100 tests.
// failing seed for union.duplicates is NZOPbCUx94dKkILXjMh9mscZqthZiWuOtiBl77tk8HM=
// ! union.duplicates: Falsified after 0 passed tests.
// > ARG_0: Graph(Map(Vertex(1) -> Set(Vertex(0)), Vertex(0) -> Set()))
// failing seed for union.outputs disjoint is grZ0VNqnRZbCVw58MOxEm4AQTiLE9A5WdBRZyaCXrPF=
// ! union.outputs disjoint: Falsified after 2 passed tests.
// > ARG_0: Vector(Graph(Map(Vertex(1) -> Set(Vertex(3)), Vertex(3) -> Set(), 
//   Vertex(0) -> Set(Vertex(1)))), Graph(Map(Vertex(1) -> Set(Vertex(4)), Ver
//   tex(4) -> Set())))
// + union.inputs disjoint: OK, passed 100 tests.
// + union.same edges and vertices: OK, passed 100 tests.

testUnion(_ => Vector.empty).check()
// + union.empty: OK, proved property.
// failing seed for union.singleton is suf0_OOzVnELIzdY1Q7MlkdGnLfxeRce7KtPQ1dERoF=
// ! union.singleton: Falsified after 0 passed tests.
// > ARG_0: Graph(Map(Vertex(1) -> Set(), Vertex(6) -> Set(Vertex(3)), Vertex(
//   3) -> Set(), Vertex(0) -> Set()))
// failing seed for union.duplicates is 6P2nKX7NbidY5dotRmAXL2lQEmtLcSDolrm1WF_j1KB=
// ! union.duplicates: Falsified after 0 passed tests.
// > ARG_0: Graph(Map(Vertex(1) -> Set(Vertex(0)), Vertex(0) -> Set()))
// + union.outputs disjoint: OK, passed 100 tests.
// failing seed for union.inputs disjoint is xYg1KsquZltaU_wVzZK07DIetB7eMLTdRTo22gunptF=
// ! union.inputs disjoint: Falsified after 1 passed tests.
// > ARG_0: Vector(Graph(Map(Vertex(0) -> Set())))
// failing seed for union.same edges and vertices is zbvtL24xwgFEtt8Yg8GXSM9m__2cd9iWbYu0ulylMbA=
// ! union.same edges and vertices: Falsified after 2 passed tests.
// > ARG_0: Vector(Graph(Map(Vertex(0) -> Set(Vertex(1)), Vertex(1) -> Set()))
//   )
```

## A First Solution

As an initial attempt at implementing `union`, let's try folding over each input graph, accumulating disjoint graphs. For each input graph, we can search the disjoint graphs, looking for overlap. If we find an overlap, then we replace that element with the merge of the input and the old element. Otherwise, we add the new graph as a new disjoint graph.

```scala
def unionFirst(gs: Vector[Graph]): Vector[Graph] =
  gs.foldLeft(Vector.empty[Graph]) { (acc, g) =>
    val idx = acc.indexWhere(overlaps(g, _))
    if idx < 0 then acc :+ g
    else acc.updated(idx, acc(idx) |+| g)
  }
```

An initial test look promising:

```scala
println(unionFirst(Vector(Graph(1 -> 2, 3 -> 4), Graph(2 -> 3))))
// Vector(Graph(Map(Vertex(1) -> Set(Vertex(2)), Vertex(2) -> Set(Vertex(3)), Vertex(3) -> Set(Vertex(4)), Vertex(4) -> Set())))
```

A more slightly more complicated test reveals an error though:

```scala
println(unionFirst(Vector(Graph(1 -> 2), Graph(3 -> 4), Graph(2 -> 3))))
// Vector(Graph(Map(Vertex(2) -> Set(Vertex(3)), Vertex(3) -> Set(), Vertex(1) -> Set(Vertex(2)))), Graph(Map(Vertex(3) -> Set(Vertex(4)), Vertex(4) -> Set())))
```

When the second input graph is processed, it's disjoint with all the graphs processed so far (i.e., the first graph). When the third graph is processed, it's merged with the first, resulting in an output of two graphs. But those two graphs share a common vertex of 3. It seems that each time we merge graphs, we need to reconsider whether the disjoint set is still disjoint. More on that in a moment. First, let's run our test on this implementation and see if it also finds a counterexample:

```scala
testUnion(unionFirst).check()
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 100 tests.
// + union.duplicates: OK, passed 100 tests.
// + union.outputs disjoint: OK, passed 100 tests.
// + union.inputs disjoint: OK, passed 100 tests.
// + union.same edges and vertices: OK, passed 100 tests.
```

Okay, so when we merge a graph in to the disjoint set, two entries that were previously disjoint may no longer be disjoint. We could fix our issue by recursively calling our union function after merging -- i.e. `unionFirst(acc.updated(idx, acc(idx) |+| g))` -- but doing so wouldn't be tail recursive. Instead, we could run the full fold and when it completes, check if we've done any merges. If so, we recurse and otherwise we return. We can test if we've done merges by comparing the size of the input to the size of the output.


```scala
def unionRecursive(gs: Vector[Graph]): Vector[Graph] =
  val out = gs.foldLeft(Vector.empty[Graph]) { (acc, g) =>
    val idx = acc.indexWhere(overlaps(g, _))
    if idx < 0 then acc :+ g
    else acc.updated(idx, acc(idx) |+| g)
  }
  if gs.size == out.size then out else unionRecursive(out)
```

This is the same implementation as `unionFirst` except the final statement, which compares the size of the input to the size of the output. If they are the same, then we've done no merges and we return the result. Otherwise, we recurse on the output.

This version works with our problematice example:

```scala
println(unionRecursive(Vector(Graph(1 -> 2), Graph(3 -> 4), Graph(2 -> 3))))
// Vector(Graph(Map(Vertex(2) -> Set(Vertex(3)), Vertex(3) -> Set(Vertex(4)), Vertex(1) -> Set(Vertex(2)), Vertex(4) -> Set())))
```

And it passes all of our laws:

```scala
testUnion(unionRecursive).check()
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 100 tests.
// + union.duplicates: OK, passed 100 tests.
// + union.outputs disjoint: OK, passed 100 tests.
// + union.inputs disjoint: OK, passed 100 tests.
// + union.same edges and vertices: OK, passed 100 tests.
```

## A Faster Solution

TODO

```scala
def unionFast(gs: Vector[Graph]): Vector[Graph] =
  gs.foldLeft(Vector.empty[Graph], Map.empty[Vertex, Int]) { case ((acc, lookup), g) =>
    // Find indices of graphs with overlapping vertices
    val vertices = g.adjacencies.keySet
    val indices = vertices.flatMap(v => lookup.get(v))
    if indices.isEmpty then (acc :+ g, lookup ++ vertices.iterator.map(_ -> acc.size))
    else
      // Target index is the minimum index with
      val newIndex = indices.min
      val otherIndices = indices - newIndex
      val merged = otherIndices.foldLeft(acc(newIndex))((m, i) => m |+| acc(i)) |+| g
      // Null out each other index & fix up vertex lookup table to point to new index
      val newLookup = lookup ++ vertices.iterator.map(_ -> newIndex)
      otherIndices.foldLeft((acc.updated(newIndex, merged), newLookup)) { case ((newAcc, newLookup), idx) =>
        newAcc.updated(idx, null) -> (newLookup ++ acc(idx).adjacencies.keySet.iterator.map(_ -> newIndex))
      }
  }(0).filterNot(_ eq null)

testUnion(unionFast).check()
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 100 tests.
// + union.duplicates: OK, passed 100 tests.
// + union.outputs disjoint: OK, passed 100 tests.
// + union.inputs disjoint: OK, passed 100 tests.
// + union.same edges and vertices: OK, passed 100 tests.
```

