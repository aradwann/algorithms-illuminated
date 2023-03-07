use algorithms_illuminated::graph::DirectedGraphRc;

fn main() {
    let mut g = DirectedGraphRc::new();
    g.add_vertex('s');
    g.add_vertex('v');
    g.add_vertex('w');
    g.add_vertex('t');

    g.add_edge(0, 1, Some(1));
    g.add_edge(0, 2, Some(4));
    g.add_edge(1, 2, Some(2));
    g.add_edge(1, 3, Some(6));
    g.add_edge(2, 3, Some(3));
    println!("{:#?}", g);
}
