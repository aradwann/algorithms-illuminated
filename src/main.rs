use algorithms_illuminated::graph::DirectedGraphRc;

fn main() {
    let mut g = DirectedGraphRc::new();
    g.add_vertex();
    g.add_vertex();
    g.add_vertex();
    g.add_vertex();

    g.add_edge(0, 1);
    g.add_edge(0, 2);
    g.add_edge(1, 3);
    g.add_edge(2, 3);

    println!("{:#?}", &g);
}
