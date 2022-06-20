# Graph Unions

I recently came across an interesting problem:

> Given a set of directed graphs with the property that no two graphs share an edge, compute the set of graphs with the same total set of edges & vertices which has the additional property that no two graphs share a vertex.

That is, each graph in the output should be the union of the graphs from the input which have at least one vertex in common. In this article, we'll look at how to efficiently implement this computation in Scala.

For starters, we'll need a representation of a graph. One of the simplest representations is a set edges and vertices, where an edge is simply a pairing of two vertices:

```scala
case class Vertex(id: Int)
case class Edge(from: Vertex, to: Vertex)
case class Graph(edges: Set[Edge], vertices: Set[Vertex])
```

Let's also create a quick way to construct a graph throughout this article:

```scala
def graph(edges: (Int, Int)*): Graph =
  val es = edges.map((from, to) => Edge(Vertex(from), Vertex(to))).toSet
  val vs = es.flatMap(e => Set(e.from, e.to))
  Graph(es, vs)

val g1 = graph(1 -> 2, 2 -> 3)
// g1: Graph = Graph(
//   edges = Set(
//     Edge(from = Vertex(id = 1), to = Vertex(id = 2)),
//     Edge(from = Vertex(id = 2), to = Vertex(id = 3))
//   ),
//   vertices = Set(Vertex(id = 1), Vertex(id = 2), Vertex(id = 3))
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
- `union(Vector(graph(1 -> 2), graph(2 -> 3))) == Vector(graph(1 -> 2, 2 -> 3))`
- `union(Vector(graph(1 -> 2), graph(3 -> 4), graph(2 -> 3)) == Vector(graph(1 -> 2, 2 -> 3, 3 -> 4))`

And another that takes disjoint graphs as input:
- `union(Vector(graph(1 -> 2), graph(3 -> 4))) == Vector(graph(1 -> 2), graph(3 -> 4))`

We can generalize the two non-trivial examples to more general laws:
- given `gs: Vector[Graph]` such that every member has the same vertex set, `union(gs) = Vector(u)` where `u` is the union of all edge sets in `gs
- given `gs: Vector[Graph]` such that all members are disjoin, `union(gs) == gs`

