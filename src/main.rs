use algorithms_illuminated::graph::UndirectedGraph;
fn main() {
    let graph: UndirectedGraph =
        UndirectedGraph::from_file("src/graph/txt/dijkstraData.txt").unwrap();
    let result = graph.dijkstra(0).unwrap();
    //   println!("{:?}", result);
    println!("{:?}", result.get(&6).unwrap());
    println!("{:?}", result.get(&36).unwrap());
    println!("{:?}", result.get(&58).unwrap());
    println!("{:?}", result.get(&81).unwrap());
    println!("{:?}", result.get(&98).unwrap());
    println!("{:?}", result.get(&114).unwrap());
    println!("{:?}", result.get(&132).unwrap());
    println!("{:?}", result.get(&164).unwrap());
    println!("{:?}", result.get(&187).unwrap());
    println!("{:?}", result.get(&196).unwrap());
}
