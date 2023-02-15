use algorithms_illuminated::graph::utils::build_graph_from_txt;

fn main() {
    let g = build_graph_from_txt("./src/graph/txt/scc_test1.txt");

    println!("graph: {g:#?}");
}
