# Graph Unions

I recently came across an interesting problem:

> Given a set of directed graphs with the property that no two graphs share an edge, compute the set of graphs with the same total set of edges & vertices which has the additional property that no two graphs share a vertex.

That is, each graph in the output should be the union of the graphs from the input which have at least one vertex in common. In this article, we'll look at how to efficiently implement this computation in Scala.

For starters, we'll need a representation of a graph. One of the simplest representations is an [adjacency list](https://en.wikipedia.org/wiki/Adjacency_list).

```scala mdoc
case class Vertex(id: Int)
case class Edge(from: Vertex, to: Vertex)
case class Graph(edges: Vector[Edge])
```

Let's also create a quick way to construct a graph throughout this article:

```scala mdoc
def graph(edges: (Int, Int)*): Graph =
  Graph(edges.map { case (from, to) => Edge(Vertex(from), Vertex(to)) }.toVector)

val g1 = graph(1 -> 2, 2 -> 3)
```

Our goal is to come up with an implementation of `union`:

```scala
def union(gs: Vector[Graph]): Vector[Graph] = ???
```

Let's consider a few examples. First, let's consider some simple cases:
- empty input: `union(Vector.empty) == Vector.empty`
- singleton input: `union(Vector(g)) == Vector(g)` for every graph `g`

An example that unions a graph:
- `union(Vector(graph(1 -> 2), graph(2 -> 3))) == Vector(graph(1 -> 2, 2 -> 3))

And another that takes disjoint graphs as input:
- `union(Vector(graph(1 -> 2), graph(3 -> 4))) == Vector(graph(1 -> 2), graph(3 -> 4))

