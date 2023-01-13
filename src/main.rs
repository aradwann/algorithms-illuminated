use algorithms_illuminated::graph::graph::UndirectedGraph;

fn main() {
    let mut graph = UndirectedGraph::new();
    println!("{:?}", graph);
    graph.add_node();
    graph.add_node();

    graph.add_edge(0, 1);
    println!("{:?}", graph);
}
