# clrs

![Rust workflow](https://github.com/aradwann/algorithms-illuminated/actions/workflows/rust.yml/badge.svg)

my notes and implementation (in rust) of some algorithms in:

[Algorithms Illuminated](https://www.algorithmsilluminated.org/)

## Sort

   1. [merge sort](./src/sort/merge.rs)
   2. [heap sort](./src/sort/heap.rs)

## Graph

graphs are represented with adjancency list, currently (with two usize Vecs in Rust)
> at the moment: parallel edges aren't allowed
>
> at the moment: self-loops aren't allowed

   1. [undirected graph](./src/graph/undirected_graph.rs)
      1. [breadth-first search BFS](./src/graph/undirected_graph.rs#L80-L102)
      2. [undirected connected componenets UCC](./src/graph/undirected_graph.rs#L163-L189)
      3. [depth first search](./src/graph/undirected_graph.rs#L203-L224)
      4. [dijkstra](./src/graph/undirected_graph.rs#L272-L316)
   2. [directed graph](./src/graph/directed_graph.rs)
      1. depth-first search DFS ([iterative](./src/graph/directed_graph.rs#L57-L80) & [recursive](./src/graph/directed_graph.rs#L119-L123))
      2. [Topo Sort](./src/graph/directed_graph.rs#L190-L219)
      3. [kosaraju](./src/graph/directed_graph.rs#L357-L373)

TODO:

- [ ] track memory footprint
