use algorithms_illuminated::graph::graph::UndirectedGraph;

fn main() {
    let mut graph = UndirectedGraph::new();
    println!("{:#?}", graph);
    graph.add_node('s');
    graph.add_node('a');
    graph.add_node('b');
    graph.add_node('c');
    graph.add_node('d');
    graph.add_node('e');

    graph.add_edge(0, 1);
    graph.add_edge(0, 2);
    graph.add_edge(1, 3);
    graph.add_edge(2, 3);
    graph.add_edge(2, 4);
    graph.add_edge(3, 4);
    graph.add_edge(3, 5);
    graph.add_edge(4, 5);
    println!("{:#?}", graph);

    graph.bfs('k');
}
