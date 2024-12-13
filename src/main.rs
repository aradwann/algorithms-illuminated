use algorithms_illuminated::graph::UndirectedGraph;
fn main() {
    let graph: UndirectedGraph = UndirectedGraph::from_file("src/graph/txt/dijkstra1.txt").unwrap();
    graph.print_graph();
    let result = graph.dijkstra(0).unwrap();
    println!("{:?}", result);
}
