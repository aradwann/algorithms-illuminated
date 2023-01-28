use algorithms_illuminated::graph::DirectedGraph;
use algorithms_illuminated::graph::UndirectedGraph;

fn main() {
    let mut graph = UndirectedGraph::new();
    println!("{:#?}", graph);
    graph.add_vertex('s');
    graph.add_vertex('a');
    graph.add_vertex('b');
    graph.add_vertex('c');
    graph.add_vertex('d');
    graph.add_vertex('e');

    graph.add_edge(0, 1);
    graph.add_edge(0, 2);
    //  graph.add_edge(1, 3);
    //   graph.add_edge(2, 3);
    // graph.add_edge(2, 4);
    graph.add_edge(3, 4);
    graph.add_edge(3, 5);
    graph.add_edge(4, 5);
    println!("{:#?}", graph);

    graph.ucc();
}
