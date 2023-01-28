use algorithms_illuminated::graph::DirectedGraph;
use algorithms_illuminated::graph::UndirectedGraph;

fn main() {
    let mut graph = DirectedGraph::new();
    println!("{:#?}", graph);
    graph.add_vertex('s');
    graph.add_vertex('v');
    graph.add_vertex('w');
    graph.add_vertex('t');

    graph.add_edge(0, 1);
    graph.add_edge(0, 2);
    graph.add_edge(1, 3);
    graph.add_edge(2, 3);
    
    println!("{:#?}", graph);
}
