use algorithms_illuminated::graph::{Graph, UndirectedGraph};
fn main() {
    let mut graph = UndirectedGraph::new();
    graph.add_vertex(1, 'A');
    graph.add_vertex(2, 'B');
    graph.add_vertex(3, 'C');
    graph.add_vertex(4, 'D');

    let _ = graph.add_edge(1, 2);
    let _ = graph.add_edge(1, 3);
    let _ = graph.add_edge(2, 4);

    let bfs_result = graph.bfs(1);
    println!("{:?}", bfs_result); // Output will be the order of traversal, e.g., [1, 2, 3, 4]
}
