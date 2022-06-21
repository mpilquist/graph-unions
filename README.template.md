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

Let's write these as a [ScalaCheck](https://scalacheck.org/) test:

```scala mdoc
import org.scalacheck.{Arbitrary, Gen, Prop}

def genGraph: Gen[Graph] = Gen.sized { size =>
  val genEdge = for
    f <- Gen.chooseNum(0, size)
    t <- Gen.chooseNum(0, size)
  yield (f, t)
  Gen.listOf(genEdge)
    .filter(_.nonEmpty)
    .map(es => Graph(es*))
}

given arbitraryGraph: Arbitrary[Graph] = Arbitrary(genGraph)

def overlaps(g1: Graph, g2: Graph): Boolean =
  g1.adjacencies.keySet.intersect(g2.adjacencies.keySet).nonEmpty

def testUnion(union: Vector[Graph] => Vector[Graph]) =
  Prop.secure(union(Vector.empty) == Vector.empty) :| "empty"
    && Prop.forAll((g: Graph) => union(Vector(g)) == Vector(g)) :| "singleton"
    && Prop.forAll((g: Graph) => union(Vector(g, g)) == Vector(g)) :| "duplicates"
    && Prop.forAll { (gs: Vector[Graph]) =>
      val us = union(gs)
      us.forall(u => us.forall(u2 => (u eq u2) || !overlaps(u, u2)))
    } :| "outputs disjoint"
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
