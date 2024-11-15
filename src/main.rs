use algorithms_illuminated::graph::DirectedGraph;
fn main() {
    let graph = DirectedGraph::build_from_file("src/graph/txt/graph_test2.txt").unwrap();
    graph.print_graph();
    let topo_sort = graph.topo_sort();

    println!("{:?}", topo_sort);
}
