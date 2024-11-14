use std::collections::HashSet;

use algorithms_illuminated::graph::DirectedGraph;
fn main() {
    let graph = DirectedGraph::build_from_file("src/graph/txt/graph_test2.txt").unwrap();
    graph.print_graph();
    let mut visited_set = HashSet::new();
    let mut dfs_order = Vec::new();
    let dfs_order = graph
        .dfs_recursive(0, &mut visited_set, &mut dfs_order)
        .unwrap();
    println!("{:?}", dfs_order);
}
