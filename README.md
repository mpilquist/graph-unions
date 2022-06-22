# Disjoint Graph Unions: Performance Case Study

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
// failing seed for union.duplicates is o5o47RoaxyZ-sW3SN3qKtuWEAj6T7LIBhwF9mHvR0VM=
// ! union.duplicates: Falsified after 0 passed tests.
// > ARG_0: Graph(17633 -> {}, 24582 -> {17633})
// failing seed for union.outputs disjoint is XLFhfdFdhZ1zoOOfTHJgTXUnsGMdyjtV8ntsO1YgZOK=
// ! union.outputs disjoint: Falsified after 64 passed tests.
// > ARG_0: Vector(Graph(1274 -> {}, 2908 -> {}, 9294 -> {1274}, 16459 -> {222
//   57}, 21082 -> {2908}, 22257 -> {}), Graph(16459 -> {}, 25239 -> {16459}))
// > ARG_0_ORIGINAL: Vector(Graph(3346 -> {26176}, 10150 -> {25634}, 25634 -> 
//   {}, 26176 -> {}, 30041 -> {32027}, 32027 -> {}), Graph(22371 -> {}, 24910
//    -> {22371}), Graph(9589 -> {22346}, 20364 -> {}, 22346 -> {}, 26312 -> {
//   20364}), Graph(1274 -> {}, 2908 -> {}, 9294 -> {1274}, 16459 -> {22257}, 
//   21082 -> {2908}, 22257 -> {}), Graph(4361 -> {7477}, 7477 -> {}, 24499 ->
//    {27234}, 27234 -> {}), Graph(6779 -> {14352}, 14352 -> {}, 16977 -> {229
//   98}, 22998 -> {}), Graph(2324 -> {}, 23426 -> {2324}), Graph(947 -> {2781
//   8}, 8884 -> {}, 27818 -> {}, 30839 -> {8884}), Graph(14684 -> {}, 20158 -
//   > {32064}, 22033 -> {14684}, 32064 -> {}), Graph(13889 -> {}, 22082 -> {}
//   , 27653 -> {22082}, 28473 -> {13889}), Graph(12312 -> {14307}, 14307 -> {
//   }), Graph(16459 -> {}, 25239 -> {16459}), Graph(3466 -> {19070}, 10554 ->
//    {}, 16666 -> {17351}, 17351 -> {}, 19070 -> {}, 28406 -> {10554}), Graph
//   (5825 -> {}, 10175 -> {5825}), Graph(1313 -> {28433}, 23888 -> {}, 24524 
//   -> {23888}, 26821 -> {31446}, 28433 -> {}, 31446 -> {}), Graph(6630 -> {}
//   , 8731 -> {}, 11133 -> {}, 23141 -> {8731}, 26557 -> {11133}, 26845 -> {6
//   630}), Graph(10715 -> {}, 30617 -> {10715}), Graph(11004 -> {}, 12748 -> 
//   {11004}, 13399 -> {}, 27617 -> {13399}), Graph(2353 -> {}, 6685 -> {9609}
//   , 9609 -> {}, 31601 -> {2353}), Graph(3779 -> {}, 8992 -> {3779}, 9940 ->
//    {30327}, 21591 -> {27970}, 27970 -> {}, 30327 -> {}), Graph(3492 -> {144
//   93}, 3967 -> {}, 5868 -> {8569}, 8569 -> {}, 14493 -> {}, 29021 -> {3967}
//   ), Graph(14208 -> {29228}, 29228 -> {}), Graph(319 -> {}, 8653 -> {319}, 
//   25040 -> {25802}, 25802 -> {}), Graph(5603 -> {}, 27004 -> {5603}), Graph
//   (4352 -> {20689}, 20689 -> {}), Graph(1148 -> {}, 5853 -> {13086}, 7908 -
//   > {16848}, 13086 -> {}, 15652 -> {1148}, 16848 -> {}), Graph(963 -> {2774
//   }, 2774 -> {}, 22039 -> {32081}, 27577 -> {}, 28636 -> {27577}, 32081 -> 
//   {}), Graph(13148 -> {}, 17335 -> {13148}))
// + union.inputs disjoint: OK, passed 200 tests.
// + union.same edges and vertices: OK, passed 200 tests.

runUnionTest(_ => Vector.empty)
// + union.empty: OK, proved property.
// failing seed for union.singleton is o5o47RoaxyZ-sW3SN3qKtuWEAj6T7LIBhwF9mHvR0VM=
// ! union.singleton: Falsified after 0 passed tests.
// > ARG_0: Graph(17633 -> {}, 24582 -> {17633})
// failing seed for union.duplicates is o5o47RoaxyZ-sW3SN3qKtuWEAj6T7LIBhwF9mHvR0VM=
// ! union.duplicates: Falsified after 0 passed tests.
// > ARG_0: Graph(17633 -> {}, 24582 -> {17633})
// + union.outputs disjoint: OK, passed 200 tests.
// failing seed for union.inputs disjoint is F7AGdOeo9Gw8L_ZlIIKVdLkGItFMrNJCLCVq3d93PSC=
// ! union.inputs disjoint: Falsified after 3 passed tests.
// > ARG_0: Vector(Graph(700 -> {15548}, 15548 -> {}))
// > ARG_0_ORIGINAL: Vector(Graph(700 -> {15548}, 15548 -> {}), Graph(29732 ->
//    {31898}, 31898 -> {}))
// failing seed for union.same edges and vertices is F7AGdOeo9Gw8L_ZlIIKVdLkGItFMrNJCLCVq3d93PSC=
// ! union.same edges and vertices: Falsified after 3 passed tests.
// > ARG_0: Vector(Graph(700 -> {15548}, 15548 -> {}))
// > ARG_0_ORIGINAL: Vector(Graph(700 -> {15548}, 15548 -> {}), Graph(29732 ->
//    {31898}, 31898 -> {}))
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
// failing seed for union.outputs disjoint is qW-MYSqzBOkHi5NGPEP-ePItQPpYYbkf0SqIS5Eg7qL=
// ! union.outputs disjoint: Falsified after 136 passed tests.
// > ARG_0: Vector(Graph(978 -> {}, 4110 -> {}, 5400 -> {}, 9780 -> {26348}, 1
//   3258 -> {23049}, 21283 -> {5400}, 23049 -> {}, 24472 -> {30693}, 25476 ->
//    {4110}, 26348 -> {}, 28541 -> {978}, 30693 -> {}), Graph(1364 -> {7962},
//    1707 -> {}, 7962 -> {}, 9899 -> {}, 11409 -> {}, 15605 -> {1707}, 15991 
//   -> {}, 16454 -> {9899}, 23279 -> {}, 27113 -> {15991}, 28394 -> {11409}, 
//   28905 -> {23279}), Graph(506 -> {8608}, 8608 -> {}, 11409 -> {}, 11505 ->
//    {15014}, 12623 -> {}, 15014 -> {}, 22759 -> {}, 23385 -> {11409}, 26713 
//   -> {22759}, 30693 -> {12623}))
// > ARG_0_ORIGINAL: Vector(Graph(2485 -> {}, 2869 -> {22806}, 8471 -> {2485},
//    22806 -> {}), Graph(4247 -> {}, 8561 -> {32089}, 12169 -> {13617}, 12434
//    -> {15520}, 13617 -> {}, 15520 -> {}, 19498 -> {}, 24574 -> {4247}, 2786
//   9 -> {19498}, 32089 -> {}), Graph(9751 -> {}, 17353 -> {9751}), Graph(103
//   9 -> {}, 1593 -> {1039}, 8002 -> {}, 17144 -> {8002}, 21424 -> {23134}, 2
//   3134 -> {}, 23291 -> {28324}, 28324 -> {}), Graph(2451 -> {}, 12244 -> {2
//   451}), Graph(1255 -> {28316}, 2979 -> {}, 15188 -> {}, 24557 -> {2979}, 2
//   8316 -> {}, 30324 -> {15188}, 30901 -> {}, 32370 -> {30901}), Graph(596 -
//   > {}, 4596 -> {27355}, 9511 -> {10478}, 10116 -> {}, 10478 -> {}, 10878 -
//   > {23591}, 22944 -> {}, 23312 -> {22944}, 23591 -> {}, 27355 -> {}, 27971
//    -> {596}, 29016 -> {10116}), Graph(13451 -> {}, 16637 -> {13451}), Graph
//   (6 -> {}, 2646 -> {}, 12261 -> {28489}, 12915 -> {6}, 13830 -> {}, 15327 
//   -> {}, 21948 -> {15327}, 25027 -> {2646}, 28489 -> {}, 30624 -> {13830}),
//    Graph(477 -> {}, 5372 -> {477}, 6328 -> {15366}, 15366 -> {}, 18648 -> {
//   24734}, 24734 -> {}), Graph(650 -> {}, 18305 -> {20987}, 20987 -> {}, 229
//   17 -> {650}), Graph(1929 -> {}, 2798 -> {}, 3407 -> {}, 16307 -> {2798}, 
//   22004 -> {3407}, 28438 -> {1929}), Graph(463 -> {27071}, 4220 -> {}, 4856
//    -> {10582}, 9396 -> {}, 10582 -> {}, 14422 -> {31584}, 17887 -> {9396}, 
//   23598 -> {4220}, 25110 -> {29783}, 27071 -> {}, 29783 -> {}, 31584 -> {})
//   , Graph(2209 -> {}, 9529 -> {2209}, 13837 -> {}, 17407 -> {23028}, 19009 
//   -> {13837}, 23028 -> {}), Graph(5850 -> {27064}, 19655 -> {}, 25748 -> {1
//   9655}, 27064 -> {}), Graph(4565 -> {32512}, 8660 -> {}, 16107 -> {27200},
//    18175 -> {}, 21684 -> {18175}, 27200 -> {}, 31661 -> {8660}, 32512 -> {}
//   ), Graph(3452 -> {27201}, 7782 -> {21053}, 12423 -> {18202}, 14865 -> {15
//   871}, 15871 -> {}, 18202 -> {}, 21053 -> {}, 23698 -> {}, 27201 -> {}, 32
//   052 -> {23698}), Graph(1162 -> {5193}, 5193 -> {}, 9696 -> {24592}, 24592
//    -> {}), Graph(2062 -> {32459}, 10921 -> {15491}, 14447 -> {15872}, 15491
//    -> {}, 15872 -> {}, 23744 -> {}, 29951 -> {23744}, 32459 -> {}), Graph(9
//   54 -> {}, 1192 -> {}, 11307 -> {1192}, 18976 -> {954}), Graph(135 -> {280
//   90}, 3026 -> {17436}, 11372 -> {14637}, 11817 -> {17450}, 14637 -> {}, 17
//   436 -> {}, 17450 -> {}, 21984 -> {}, 22118 -> {}, 27488 -> {22118}, 28090
//    -> {}, 30079 -> {21984}), Graph(2950 -> {20249}, 20249 -> {}), Graph(193
//   8 -> {}, 8825 -> {22440}, 15389 -> {}, 15446 -> {1938}, 17244 -> {}, 2219
//   9 -> {17244}, 22440 -> {}, 32720 -> {15389}), Graph(5935 -> {}, 22843 -> 
//   {}, 23852 -> {22843}, 27386 -> {5935}), Graph(7128 -> {}, 7933 -> {}, 109
//   75 -> {7128}, 16756 -> {31992}, 23756 -> {7933}, 31992 -> {}), Graph(5156
//    -> {23554}, 5640 -> {}, 9496 -> {}, 11231 -> {}, 11298 -> {5640}, 12391 
//   -> {11231}, 22856 -> {9496}, 23554 -> {}), Graph(1878 -> {11738}, 5601 ->
//    {}, 11738 -> {}, 14105 -> {15315}, 15315 -> {}, 15486 -> {17667}, 17667 
//   -> {}, 18198 -> {32726}, 26716 -> {5601}, 32726 -> {}), Graph(13460 -> {}
//   , 18953 -> {26781}, 23079 -> {13460}, 26781 -> {}), Graph(13698 -> {}, 29
//   900 -> {13698}), Graph(692 -> {}, 3964 -> {7191}, 7191 -> {}, 7210 -> {69
//   2}, 26034 -> {29161}, 29161 -> {}), Graph(7538 -> {}, 10697 -> {7538}), G
//   raph(8251 -> {}, 22633 -> {8251}, 22995 -> {25638}, 23150 -> {}, 24133 ->
//    {}, 25638 -> {}, 29352 -> {23150}, 29836 -> {24133}), Graph(5470 -> {296
//   61}, 29661 -> {}), Graph(2549 -> {6904}, 6904 -> {}), Graph(2876 -> {}, 3
//   126 -> {}, 5627 -> {}, 10169 -> {3126}, 10803 -> {5627}, 11966 -> {}, 138
//   62 -> {11966}, 15876 -> {}, 19061 -> {19681}, 19681 -> {}, 20967 -> {1587
//   6}, 23542 -> {2876}), Graph(5585 -> {}, 10416 -> {31678}, 15455 -> {27778
//   }, 20403 -> {5585}, 27778 -> {}, 29695 -> {30765}, 30765 -> {}, 31678 -> 
//   {}), Graph(14713 -> {}, 30451 -> {14713}), Graph(658 -> {}, 5391 -> {7645
//   }, 6693 -> {}, 7645 -> {}, 18572 -> {658}, 24653 -> {6693}, 27266 -> {}, 
//   28261 -> {27266}), Graph(193 -> {30030}, 823 -> {5931}, 5931 -> {}, 16730
//    -> {}, 20499 -> {16730}, 30030 -> {}), Graph(4551 -> {25242}, 13854 -> {
//   }, 19555 -> {32021}, 22412 -> {28792}, 23169 -> {}, 25242 -> {}, 28549 ->
//    {23169}, 28792 -> {}, 31869 -> {13854}, 32021 -> {}), Graph(1939 -> {}, 
//   3943 -> {11537}, 9477 -> {1939}, 11537 -> {}, 26322 -> {31213}, 31213 -> 
//   {}), Graph(5514 -> {18505}, 7156 -> {32021}, 8503 -> {13689}, 13689 -> {}
//   , 18505 -> {}, 18703 -> {}, 20544 -> {18703}, 32021 -> {}), Graph(1474 ->
//    {}, 1824 -> {6305}, 6305 -> {}, 9906 -> {21502}, 11434 -> {}, 17413 -> {
//   17482}, 17482 -> {}, 20555 -> {22368}, 21331 -> {1474}, 21502 -> {}, 2190
//   8 -> {11434}, 22368 -> {}), Graph(11575 -> {}, 14922 -> {}, 16155 -> {195
//   88}, 19588 -> {}, 25710 -> {14922}, 25961 -> {11575}, 29040 -> {}, 29885 
//   -> {29040}), Graph(10947 -> {29249}, 29249 -> {}), Graph(2939 -> {12479},
//    6187 -> {9749}, 9749 -> {}, 12479 -> {}, 25706 -> {29424}, 29424 -> {}),
//    Graph(5756 -> {}, 6773 -> {}, 7241 -> {6773}, 12000 -> {}, 14271 -> {}, 
//   16901 -> {5756}, 18268 -> {12000}, 22989 -> {31264}, 29418 -> {14271}, 31
//   264 -> {}), Graph(1421 -> {32294}, 11441 -> {17124}, 11917 -> {20880}, 17
//   124 -> {}, 18882 -> {23625}, 20880 -> {}, 23625 -> {}, 25361 -> {}, 26066
//    -> {25361}, 32294 -> {}), Graph(978 -> {}, 4110 -> {}, 5400 -> {}, 9780 
//   -> {26348}, 13258 -> {23049}, 21283 -> {5400}, 23049 -> {}, 24472 -> {306
//   93}, 25476 -> {4110}, 26348 -> {}, 28541 -> {978}, 30693 -> {}), Graph(40
//   20 -> {}, 21193 -> {4020}), Graph(589 -> {}, 964 -> {589}, 1155 -> {3172}
//   , 1522 -> {25845}, 3172 -> {}, 5803 -> {}, 8574 -> {5803}, 17670 -> {}, 2
//   1640 -> {17670}, 25845 -> {}), Graph(9998 -> {12818}, 11660 -> {13944}, 1
//   2818 -> {}, 13057 -> {21517}, 13944 -> {}, 21134 -> {}, 21517 -> {}, 2218
//   4 -> {}, 31442 -> {21134}, 31562 -> {22184}), Graph(915 -> {31829}, 7376 
//   -> {9553}, 8572 -> {25718}, 8737 -> {}, 9553 -> {}, 17328 -> {23912}, 178
//   44 -> {8737}, 23912 -> {}, 25718 -> {}, 27001 -> {}, 31065 -> {27001}, 31
//   829 -> {}), Graph(4363 -> {}, 6522 -> {4363}, 7871 -> {24360}, 12600 -> {
//   }, 14153 -> {}, 14909 -> {23862}, 18586 -> {12600}, 20670 -> {28437}, 229
//   71 -> {14153}, 23862 -> {}, 24360 -> {}, 28437 -> {}), Graph(6989 -> {}, 
//   28817 -> {6989}), Graph(59 -> {6167}, 6167 -> {}), Graph(1364 -> {7962}, 
//   1707 -> {}, 7962 -> {}, 9899 -> {}, 11409 -> {}, 15605 -> {1707}, 15991 -
//   > {}, 16454 -> {9899}, 23279 -> {}, 27113 -> {15991}, 28394 -> {11409}, 2
//   8905 -> {23279}), Graph(6652 -> {13516}, 13516 -> {}, 14092 -> {}, 19528 
//   -> {26167}, 26167 -> {}, 30280 -> {14092}), Graph(10762 -> {21965}, 21067
//    -> {25297}, 21965 -> {}, 25297 -> {}, 29767 -> {31216}, 31216 -> {}), Gr
//   aph(3352 -> {}, 15083 -> {}, 23458 -> {15083}, 23715 -> {3352}, 27654 -> 
//   {}, 31543 -> {27654}), Graph(2781 -> {}, 3250 -> {}, 10928 -> {3250}, 135
//   63 -> {}, 15542 -> {13563}, 21578 -> {2781}), Graph(652 -> {28036}, 5546 
//   -> {18919}, 7959 -> {}, 8449 -> {7959}, 10541 -> {}, 17440 -> {}, 18919 -
//   > {}, 28036 -> {}, 28586 -> {17440}, 32221 -> {10541}), Graph(448 -> {}, 
//   2366 -> {21352}, 6690 -> {7532}, 7532 -> {}, 8513 -> {448}, 21352 -> {}),
//    Graph(136 -> {}, 1740 -> {25616}, 3700 -> {4717}, 4717 -> {}, 5451 -> {2
//   8081}, 5454 -> {}, 14362 -> {}, 16513 -> {136}, 18618 -> {5454}, 22609 ->
//    {14362}, 25616 -> {}, 28081 -> {}), Graph(21924 -> {26760}, 26760 -> {})
//   , Graph(7523 -> {10781}, 10781 -> {}, 29651 -> {}, 32510 -> {29651}), Gra
//   ph(64 -> {}, 9805 -> {}, 18407 -> {25052}, 22466 -> {}, 22877 -> {9805}, 
//   25052 -> {}, 30499 -> {22466}, 30697 -> {64}, 31952 -> {32722}, 32722 -> 
//   {}), Graph(506 -> {8608}, 8608 -> {}, 11409 -> {}, 11505 -> {15014}, 1262
//   3 -> {}, 15014 -> {}, 22759 -> {}, 23385 -> {11409}, 26713 -> {22759}, 30
//   693 -> {12623}))
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

This version works with our problematic example:

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
// ---- 10K less disjoint -----------------------------------------
// Took 86 millis to generate
// Vertices: count 10000 min 2 max 20 mean 10.97
// Edges: count 10000 min 1 max 10 mean 5.49
// Reduced from 10000 to 2 in 189 millis
// ---- 10K more disjoint -----------------------------------------
// Took 53 millis to generate
// Vertices: count 10000 min 2 max 20 mean 10.97
// Edges: count 10000 min 1 max 10 mean 5.49
// Reduced from 10000 to 4599 in 26644 millis
// ---- 100K less disjoint -----------------------------------------
// Took 423 millis to generate
// Vertices: count 100000 min 2 max 20 mean 10.99
// Edges: count 100000 min 1 max 10 mean 5.50
// Reduced from 100000 to 1353 in 43847 millis
```

This initial algorithm seems to be pretty fast when there's a lot of overlap -- that is, when the final disjoint set has a small number of elements. This makes sense, as this algorithm makes use of an `indexWhere` on the accumulated disjoint set for each element. In the worst case, where the input set is fully disjoint, this algorithm is quadratic in the number of graphs. In the context I first encountered this problem, the input generally reduced by ~50% and the total input size was roughly 500K graphs with, on average, less than 10 vertices per graph. Hence, this solution was not suitable and I needed something that performed better for this data set.

## A Faster Solution

The key to a faster solution is avoiding a linear scan of the accumulated disjoint graphs on each iteration. The `indexWhere` is searching for overlapping graphs. Instead of searching, we can carry a lookup table that maps each vertex to an index in the accumulated disjoint graph vector. For example, if the disjoint graphs vector contains two graphs with vertices `{1, 2}, {3, 4}` then the lookup table would contain `{1 -> 0, 2 -> 0, 3 -> 1, 4 -> 1}`, indicating vertices 1 and 2 are at index 0 in the disjoint graphs vector while vertices 3 and 4 are at index 1.

With this lookup table, we can replace a linear scan (i.e. `indexWhere`) with an effective constant time lookup (per vertex in the graph in question). Determining the intersecting disjoint graphs can be accomplished by looking up each vertex in the index map and taking the union of the results. If the result is empty, then the graph in question is disjoint with all other accumulated graphs. If the result is non-empty, then the graph intersects each of the corresponding disjoint graphs. In this case, we must take the union of each of these graphs with the graph in question and store it at a new index. There's some bookkeeping in updating the lookup table for each vertex in the resulting merged graph. And we can be efficient about the bookkeeping by only computing new lookup table entries for the graphs which are changing positions (that is, there's no need to update the indices of the vertices of the graph that was at the target index, since those vertices aren't changing position). In the case of multiple matching indices, we choose the minimum index so that overall, smaller indices have larger vertex sets. There's one catch however -- when there are multiple intersecting disjoint graphs, what do we do with the *other* indices -- the ones that differ from the target index? We can update those entries to `null` and upon overall completion, filter out the `null` values.

```scala
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
```scala
runUnionTest(unionFast)
// + union.empty: OK, proved property.
// + union.singleton: OK, passed 200 tests.
// + union.duplicates: OK, passed 200 tests.
// + union.outputs disjoint: OK, passed 200 tests.
// + union.inputs disjoint: OK, passed 200 tests.
// + union.same edges and vertices: OK, passed 200 tests.
```

How about performance?

```scala
runPerformanceSuite(unionFast)
// ---- 10K less disjoint -----------------------------------------
// Took 34 millis to generate
// Vertices: count 10000 min 2 max 20 mean 10.97
// Edges: count 10000 min 1 max 10 mean 5.49
// Reduced from 10000 to 2 in 178 millis
// ---- 10K more disjoint -----------------------------------------
// Took 32 millis to generate
// Vertices: count 10000 min 2 max 20 mean 10.97
// Edges: count 10000 min 1 max 10 mean 5.49
// Reduced from 10000 to 4599 in 141 millis
// ---- 100K less disjoint -----------------------------------------
// Took 322 millis to generate
// Vertices: count 100000 min 2 max 20 mean 10.99
// Edges: count 100000 min 1 max 10 mean 5.50
// Reduced from 100000 to 1353 in 2543 millis
```

This performs significantly faster than `unionRecursive`, especially when the input is mostly disjoint. In a real world data set, this implementation proved to be thousands of times faster than `unionRecursive`. This ended up being the difference between completely infeasible to pleasantly adequate.

## Final Thoughts

During the development of this algorithm, various profiling techniques were used, including the crude `println` and `time` based debugging used in this article as well as the use of industrial strength JVM profilers. Often the profilers would provide important clues as to where the issues were but would often also lead to micro-optimizations of existing implementations. As is often the case in performance work, a key technique in the development of this algorithm was determining what work we *did not* need to do, and devising ways to avoid doing that work.
