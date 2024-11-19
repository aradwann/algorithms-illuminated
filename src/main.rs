use algorithms_illuminated::graph::DirectedGraph;
fn main() {
    let graph = DirectedGraph::build_from_file("src/graph/txt/scc_test1.txt", true).unwrap();
    let counts = graph.get_top_five_sccs();

    println!("{:?}", counts);
}
