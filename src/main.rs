use algorithms_illuminated::graph::DirectedGraphRc;

fn main() {
    let mut g = DirectedGraphRc::new();
    g.add_vertex('s');
    g.add_vertex('v');
    g.add_vertex('w');
    g.add_vertex('t');

    g.add_edge(0, 1);
    g.add_edge(0, 2);
    g.add_edge(1, 3);
    g.add_edge(2, 3);

    let s = &g.vertices()[0];
    g.dfs_recursive(s);
}
