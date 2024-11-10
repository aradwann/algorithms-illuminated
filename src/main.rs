use algorithms_illuminated::graph::{Graph, UndirectedGraph};
fn main() {
    let mut graph = UndirectedGraph::new();

    graph.add_vertex(0, 'S');
    graph.add_vertex(1, 'A');
    graph.add_vertex(2, 'B');
    graph.add_vertex(3, 'C');
    graph.add_vertex(4, 'D');
    graph.add_vertex(5, 'E');
    graph.add_vertex(6, 'F');
    graph.add_vertex(7, 'G');
    graph.add_vertex(8, 'H');
    graph.add_vertex(9, 'L');

    graph.add_edge(0, 4).unwrap();
    graph.add_edge(0, 2).unwrap();
    graph.add_edge(1, 3).unwrap();
    graph.add_edge(2, 4).unwrap();
    graph.add_edge(4, 6).unwrap();
    graph.add_edge(4, 8).unwrap();
    graph.add_edge(5, 7).unwrap();
    graph.add_edge(5, 9).unwrap();

    let connected_components = graph.ucc();

    println!("{:?}", connected_components); // Output will be the order of traversal, e.g., [1, 2, 3, 4]
}
