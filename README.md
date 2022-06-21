# Graph Unions

I recently came across an interesting problem:

> Given a set of directed graphs with the property that no two graphs share an edge, compute the set of graphs with the same total set of edges & vertices which has the additional property that no two graphs share a vertex.

That is, each graph in the output should be the union of the graphs from the input which have at least one vertex in common. In this article, we'll look at how to efficiently implement this computation in Scala.

For starters, we'll need a representation of a graph. One common implementation is an [adjacencty list](https://en.wikipedia.org/wiki/Adjacency_list), where an edge from `a` to `b` is represented as `b` being in the set under entry `a` in a map:

```scala
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
import org.scalacheck.{Arbitrary, Gen, Prop, Properties, Test}

def genGraph: Gen[Graph] =
  val maxVertexId = Int.MaxValue
  val genEdge = for
    f <- Gen.chooseNum(0, maxVertexId)
    t <- Gen.chooseNum(0, maxVertexId)
  yield (f, t)
  Gen.listOf(genEdge)
    .filter(_.nonEmpty)
    .map(es => Graph(es*))

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
def runUnionTest(union: Vector[Graph] => Vector[Graph]): Unit =
  testUnion(union).check(
    Test.Parameters.default
      .withMinSuccessfulTests(200)
      .withInitialSeed(0L) // Generate same results on each run
  )

runUnionTest(identity)
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 200 tests.
// failing seed for union.duplicates is F7AGdOeo9Gw8L_ZlIIKVdLkGItFMrNJCLCVq3d93PSC=
// ! union.duplicates: Falsified after 0 passed tests.
// > ARG_0: Graph(94077798 -> {2147483647}, 195329348 -> {355048233}, 35504823
//   3 -> {}, 2147483647 -> {})
// failing seed for union.outputs disjoint is JdYYw4z5v5nkiOzYxFiaMdO1VdY7WwSUfYrFqDP56LE=
// ! union.outputs disjoint: Falsified after 8 passed tests.
// > ARG_0: Vector(Graph(0 -> {236415665
// 733350614
// 2147483647}, 236415665 -> {}, 733350614 -> {}, 761876842 -> {836701853}, 83
//   6701853 -> {}, 2147483647 -> {}), Graph(1 -> {}, 1742466814 -> {214748364
//   7}, 2147483647 -> {1}))
// > ARG_0_ORIGINAL: Vector(Graph(0 -> {}, 1 -> {645059432}, 645059432 -> {}, 
//   759959740 -> {}, 1001598166 -> {}, 1893928099 -> {1001598166}, 2147483647
//    -> {759959740}), Graph(0 -> {236415665
// 733350614
// 2147483647}, 236415665 -> {}, 733350614 -> {}, 761876842 -> {836701853}, 83
//   6701853 -> {}, 2147483647 -> {}), Graph(1 -> {}, 1742466814 -> {214748364
//   7}, 2147483647 -> {1}))
// + union.inputs disjoint: OK, passed 200 tests.
// + union.same edges and vertices: OK, passed 200 tests.

runUnionTest(_ => Vector.empty)
// + union.empty: OK, proved property.
// failing seed for union.singleton is F7AGdOeo9Gw8L_ZlIIKVdLkGItFMrNJCLCVq3d93PSC=
// ! union.singleton: Falsified after 0 passed tests.
// > ARG_0: Graph(94077798 -> {2147483647}, 195329348 -> {355048233}, 35504823
//   3 -> {}, 2147483647 -> {})
// failing seed for union.duplicates is F7AGdOeo9Gw8L_ZlIIKVdLkGItFMrNJCLCVq3d93PSC=
// ! union.duplicates: Falsified after 0 passed tests.
// > ARG_0: Graph(94077798 -> {2147483647}, 195329348 -> {355048233}, 35504823
//   3 -> {}, 2147483647 -> {})
// + union.outputs disjoint: OK, passed 200 tests.
// failing seed for union.inputs disjoint is F7AGdOeo9Gw8L_ZlIIKVdLkGItFMrNJCLCVq3d93PSC=
// ! union.inputs disjoint: Falsified after 3 passed tests.
// > ARG_0: Vector(Graph(94077798 -> {2147483647}, 1915108540 -> {2147483647},
//    2147483647 -> {}))
// > ARG_0_ORIGINAL: Vector(Graph(94077798 -> {2147483647}, 1915108540 -> {214
//   7483647}, 2147483647 -> {}), Graph(1589642763 -> {1937867784}, 1937867784
//    -> {}))
// failing seed for union.same edges and vertices is F7AGdOeo9Gw8L_ZlIIKVdLkGItFMrNJCLCVq3d93PSC=
// ! union.same edges and vertices: Falsified after 3 passed tests.
// > ARG_0: Vector(Graph(94077798 -> {2147483647}, 1915108540 -> {2147483647},
//    2147483647 -> {}))
// > ARG_0_ORIGINAL: Vector(Graph(94077798 -> {2147483647}, 1915108540 -> {214
//   7483647}, 2147483647 -> {}), Graph(1589642763 -> {1937867784}, 1937867784
//    -> {}))
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
// Vector(Graph(1 -> {2}, 2 -> {3}, 3 -> {4}, 4 -> {}))
```

A more slightly more complicated test reveals an error though:

```scala
println(unionFirst(Vector(Graph(1 -> 2), Graph(3 -> 4), Graph(2 -> 3))))
// Vector(Graph(1 -> {2}, 2 -> {3}, 3 -> {}), Graph(3 -> {4}, 4 -> {}))
```

When the second input graph is processed, it's disjoint with all the graphs processed so far (i.e., the first graph). When the third graph is processed, it's merged with the first, resulting in an output of two graphs. But those two graphs share a common vertex of 3. It seems that each time we merge graphs, we need to reconsider whether the disjoint set is still disjoint. More on that in a moment. First, let's run our test on this implementation and see if it also finds a counterexample:

```scala
runUnionTest(unionFirst)
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 200 tests.
// + union.duplicates: OK, passed 200 tests.
// failing seed for union.outputs disjoint is -F6rV9Z_rr5kdDjSS6N2w3CeLgdPEg2pyo0rvV_y_PM=
// ! union.outputs disjoint: Falsified after 57 passed tests.
// > ARG_0: Vector(Graph(1 -> {1101052223
// 2147483647}, 889507963 -> {}, 892689410 -> {1072385597}, 992184819 -> {}, 1
//   072385597 -> {}, 1101052223 -> {}, 1387800248 -> {889507963}, 1445334849 
//   -> {992184819}, 2147483647 -> {}), Graph(0 -> {593351111}, 435977641 -> {
//   }, 593351111 -> {}, 834133036 -> {435977641}, 835874874 -> {1638351888}, 
//   1638351888 -> {}), Graph(0 -> {1
// 756281452
// 1522154439
// 2147483647}, 1 -> {}, 75575186 -> {1}, 129663476 -> {}, 756281452 -> {}, 12
//   34396351 -> {1973813032}, 1415829772 -> {0}, 1522154439 -> {}, 1529821256
//    -> {1}, 1542832868 -> {129663476}, 1725256721 -> {0}, 1804832322 -> {}, 
//   1973813032 -> {}, 2147483647 -> {1804832322}))
// > ARG_0_ORIGINAL: Vector(Graph(1 -> {1101052223
// 2147483647}, 889507963 -> {}, 892689410 -> {1072385597}, 992184819 -> {}, 1
//   072385597 -> {}, 1101052223 -> {}, 1387800248 -> {889507963}, 1445334849 
//   -> {992184819}, 2147483647 -> {}), Graph(0 -> {593351111}, 435977641 -> {
//   }, 593351111 -> {}, 834133036 -> {435977641}, 835874874 -> {1638351888}, 
//   1638351888 -> {}), Graph(0 -> {1
// 756281452
// 1522154439
// 2147483647}, 1 -> {}, 75575186 -> {1}, 129663476 -> {}, 756281452 -> {}, 12
//   34396351 -> {1973813032}, 1415829772 -> {0}, 1522154439 -> {}, 1529821256
//    -> {1}, 1542832868 -> {129663476}, 1725256721 -> {0}, 1804832322 -> {}, 
//   1973813032 -> {}, 2147483647 -> {1804832322}), Graph(0 -> {1
// 540545758
// 677247257
// 1058799948
// 1644140462
// 2126444234}, 1 -> {1220618353
// 1478357549
// 2046794673
// 2147483647}, 90071536 -> {}, 98038299 -> {}, 105056754 -> {0}, 337598213 ->
//    {}, 540545758 -> {}, 590254530 -> {98038299}, 677247257 -> {}, 689544229
//    -> {2147483647}, 821704892 -> {}, 869103361 -> {}, 1025863429 -> {1}, 10
//   58799948 -> {}, 1091536662 -> {}, 1119276974 -> {1122595516}, 1122595516 
//   -> {}, 1220618353 -> {}, 1361819771 -> {2147483647}, 1478357549 -> {}, 15
//   35108916 -> {90071536}, 1644140462 -> {}, 1863544590 -> {0}, 1890645765 -
//   > {0}, 2028961817 -> {821704892}, 2032001708 -> {0}, 2046794673 -> {}, 20
//   76456035 -> {}, 2126444234 -> {}, 2147483647 -> {337598213
// 869103361
// 1091536662
// 2076456035}), Graph(0 -> {196888504}, 1 -> {575446977}, 20201552 -> {189227
//   5067}, 196888504 -> {}, 575446977 -> {}, 696574642 -> {0}, 1774140150 -> 
//   {1}, 1892275067 -> {}), Graph(0 -> {828132337}, 412447466 -> {1966798050}
//   , 715035580 -> {}, 828132337 -> {}, 921555681 -> {}, 1958735074 -> {92155
//   5681}, 1966798050 -> {}, 2147483647 -> {0
// 715035580}), Graph(0 -> {31844466
// 927374390
// 995295706
// 1661271094}, 1 -> {1398962946
// 1884087407}, 31844466 -> {}, 63298995 -> {0}, 125790923 -> {0}, 261367302 -
//   > {}, 262633978 -> {}, 368666837 -> {}, 384477595 -> {1}, 454715966 -> {2
//   147483647}, 471566963 -> {}, 487242216 -> {}, 630550926 -> {2147483647}, 
//   927374390 -> {}, 995295706 -> {}, 1035947580 -> {368666837}, 1132275839 -
//   > {261367302}, 1333580229 -> {487242216}, 1370777095 -> {1781994495}, 139
//   8962946 -> {}, 1426031529 -> {1}, 1661271094 -> {}, 1725289011 -> {1}, 17
//   81994495 -> {}, 1884087407 -> {}, 1925058136 -> {1}, 2003655239 -> {}, 20
//   04318575 -> {0}, 2060868742 -> {471566963}, 2147483647 -> {0
// 262633978
// 2003655239}), Graph(0 -> {}, 476885837 -> {994160560}, 994160560 -> {}), Gr
//   aph(0 -> {703979985
// 950949088
// 1050455728}, 1 -> {178786197
// 1419714965
// 1445849326}, 3470459 -> {1057546828}, 178786197 -> {}, 703979985 -> {}, 846
//   602373 -> {2104603917}, 950949088 -> {}, 971965010 -> {}, 1003829093 -> {
//   971965010}, 1048790779 -> {0}, 1050455728 -> {}, 1057546828 -> {}, 113083
//   7101 -> {0}, 1369586431 -> {1}, 1419714965 -> {}, 1445849326 -> {}, 18727
//   05162 -> {1}, 1980593239 -> {2147483647}, 2104603917 -> {}, 2147483647 ->
//    {}), Graph(0 -> {306114117
// 352646320
// 421493327
// 2147483647}, 1 -> {780151214}, 1601494 -> {}, 149296161 -> {}, 306114117 ->
//    {}, 333125538 -> {}, 352646320 -> {}, 421493327 -> {}, 591574355 -> {125
//   7387812}, 609832497 -> {}, 780151214 -> {}, 1184389576 -> {1188215449}, 1
//   188215449 -> {}, 1208154254 -> {0}, 1257387812 -> {}, 1490905186 -> {1}, 
//   1509155605 -> {0}, 1688614006 -> {0}, 2138981714 -> {333125538}, 21474836
//   47 -> {0
// 1601494
// 149296161
// 609832497}))
// + union.inputs disjoint: OK, passed 200 tests.
// + union.same edges and vertices: OK, passed 200 tests.
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
// Vector(Graph(1 -> {2}, 2 -> {3}, 3 -> {4}, 4 -> {}))
```

And it passes all of our laws:

```scala
runUnionTest(unionRecursive)
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 200 tests.
// + union.duplicates: OK, passed 200 tests.
// + union.outputs disjoint: OK, passed 200 tests.
// + union.inputs disjoint: OK, passed 200 tests.
// + union.same edges and vertices: OK, passed 200 tests.
```

Let's see how it performs on large inputs. We'll need a way to time execution and a way to generate large inputs consistently (i.e., the same input run after run).

```scala
def time[A](a: => A): (Long, A) =
  import scala.concurrent.duration.*
  val started = System.nanoTime
  val result = a
  val elapsed = (System.nanoTime - started).nanos.toMillis
  (elapsed, result)

def generateGraphs(num: Int): Vector[Graph] =
  val seed = org.scalacheck.rng.Seed(0L)
  Gen.listOfN(num, genGraph)
    .pureApply(Gen.Parameters.default, seed).toVector

case class Stats(n: Int, min: Int, max: Int, mean: Int):
  override def toString: String =
    s"count: $n min: $min max: $max mean: $mean"

object Stats:
  def sample(x: Int) = Stats(1, x, x, x)

given Monoid[Stats] with
  def empty = Stats(0, Int.MaxValue, Int.MinValue, 0)
  def combine(x: Stats, y: Stats) =
    val mean = (((x.n / (x.n + y.n).toDouble) * x.mean) + ((y.n / (x.n + y.n).toDouble) * y.mean)).toInt
    Stats(x.n + y.n, x.min min y.min, x.max max y.max, mean)

def describe(gs: Vector[Graph]): String =
  val statsVertices = gs.foldMap(g => Stats.sample(g.adjacencies.size))
  val statsEdges = gs.foldMap(g => Stats.sample(g.adjacencies.values.map(_.size).sum))
  s"Vertices: $statsVertices\nEdges: $statsEdges"

def performance(numGraphs: Int, union: Vector[Graph] => Vector[Graph]): Unit =
  val (elapsedGeneration, gs) = time(generateGraphs(numGraphs))
  println(s"Took $elapsedGeneration millis to generate")
  println(describe(gs))
  val (elapsedUnion, us) = time(union(gs))
  println(s"Reduced from ${gs.size} to ${us.size} in $elapsedUnion millis")

performance(100000, unionRecursive)
// Took 11710 millis to generate
// Vertices: count: 100000 min: 1 max: 128 mean: 1
// Edges: count: 100000 min: 0 max: 92 mean: 0
// Reduced from 100000 to 373 in 7088 millis
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

runUnionTest(unionFast)
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 200 tests.
// + union.duplicates: OK, passed 200 tests.
// + union.outputs disjoint: OK, passed 200 tests.
// + union.inputs disjoint: OK, passed 200 tests.
// + union.same edges and vertices: OK, passed 200 tests.
```

