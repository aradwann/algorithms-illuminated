use algorithms_illuminated::graph::DirectedGraph;
fn main() {
    let graph = DirectedGraph::build_from_file("src/graph/txt/graph_tet.txt").unwrap();
    graph.print_graph();
}
