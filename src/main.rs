use std::collections::HashSet;

use algorithms_illuminated::graph::{Graph, UndirectedGraph};
fn main() {
    let mut graph = UndirectedGraph::new();

    graph.add_vertex(0, 'S');
    graph.add_vertex(1, 'A');
    graph.add_vertex(2, 'B');
    graph.add_vertex(3, 'C');
    graph.add_vertex(4, 'D');
    graph.add_vertex(5, 'E');

    graph.add_edge(0, 1).unwrap();
    graph.add_edge(0, 2).unwrap();
    graph.add_edge(1, 3).unwrap();
    graph.add_edge(2, 3).unwrap();
    graph.add_edge(2, 4).unwrap();
    graph.add_edge(3, 4).unwrap();
    graph.add_edge(3, 5).unwrap();

    let mut visited = HashSet::new();
    let mut dfs_order = Vec::new();

    let connected_components = graph
        .dfs_recursive(0, &mut visited, &mut dfs_order)
        .unwrap();

    println!("{:?}", connected_components); // Output will be the order of traversal, e.g., [1, 2, 3, 4]
}
