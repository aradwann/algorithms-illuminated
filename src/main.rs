use algorithms_illuminated::graph::utils::build_graph_rc_from_txt;

fn main() {
    // this is a bug in parital cyclics
    let g = build_graph_rc_from_txt("./src/graph/txt/scc_test1.txt");
    println!("{:#?}", g);
}
