# Graph Unions

I recently came across an interesting problem:

> Given a set of directed graphs with the property that no two graphs share an edge, compute the set of graphs with the same total set of edges & vertices which has the additional property that no two graphs share a vertex.

That is, each graph in the output should be the union of the graphs from the input which have at least one vertex in common. In this article, we'll look at how to efficiently implement this computation in Scala.

For starters, we'll need a representation of a graph. One common implementation is an [adjacencty list](https://en.wikipedia.org/wiki/Adjacency_list), where an edge from `a` to `b` is represented as `b` being in the set under entry `a` in a map:

```scala mdoc
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
    gs.foldMap(_.adjacencies) == union(gs).foldMap(_.adjacencies)
  }
```

Given this test definition, let's try testing with various wrong but instructive functions in place of union:
```scala mdoc
testUnion(identity).check()

testUnion(_ => Vector.empty).check()
```

## TODO

```scala mdoc
def merge(g1: Graph, g2: Graph): Graph =
  import cats.syntax.all.*
  Graph(g1.adjacencies |+| g2.adjacencies)
```

```scala mdoc
def unionBruteForce(gs: Vector[Graph]): Vector[Graph] =
  val out = gs.foldLeft(Vector.empty[Graph]) { (acc, g) =>
    val idx = acc.indexWhere(overlaps(g, _))
    if idx < 0 then acc :+ g
    else acc.updated(idx, merge(acc(idx), g))
  }
  if gs.size == out.size then out else unionBruteForce(out)

println(unionBruteForce(Vector(Graph(1 -> 2, 3 -> 4), Graph(2 -> 3))))
testUnion(unionBruteForce).check()
```

```scala mdoc
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
      val merged = merge(otherIndices.foldLeft(acc(newIndex))((m, i) => merge(m, acc(i))), g)
      // Null out each other index & fix up vertex lookup table to point to new index
      val newLookup = lookup ++ vertices.iterator.map(_ -> newIndex)
      otherIndices.foldLeft((acc.updated(newIndex, merged), newLookup)) { case ((newAcc, newLookup), idx) =>
        newAcc.updated(idx, null) -> (newLookup ++ acc(idx).adjacencies.keySet.iterator.map(_ -> newIndex))
      }
  }(0).filterNot(_ eq null)

println(unionFast(Vector(Graph(1 -> 2, 3 -> 4), Graph(2 -> 3))))
testUnion(unionFast).check()
```
