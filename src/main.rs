use algorithms_illuminated::graph::utils::build_graph_from_txt;

fn main() {
    let g = build_graph_from_txt("./src/graph/txt/graph_test2.txt");
    println!("{:#?}", g);
}
