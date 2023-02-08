# algorithms-illuminated
![Rust workflow](https://github.com/aradwann/algorithms-illuminated/actions/workflows/rust.yml/badge.svg)

my notes and implementation (in rust) of some algorithms in:

Algorithms Illuminated, a book series by Tim Roughgarden 

### Sort
   1. [merge sort](./src/sort/merge.rs)

### Graph
graphs are represented with adjancency list, currently (with two usize Vecs in Rust)
> at the moment: parallel edges aren't allowed 

> at the moment: self-loops aren't allowed 

   1. [undirected graph](./src/graph/undirected_graph.rs)
      1. [breadth-first search BFS](./src/graph/undirected_graph.rs#L89-L106)
      2. [undirected connected componenets UCC](./src/graph/undirected_graph.rs#L129-L154)
   2. [directed graph](./src/graph/directed_graph.rs) 
      1. depth-first search DFS ([iterative](./src/graph/directed_graph.rs#L88-L106) & [recursive](./src/graph/directed_graph.rs#L117-L129))
