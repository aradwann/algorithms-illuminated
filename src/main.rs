use clrs::graph::utils::build_graph_from_txt;

fn main() {
    let g = build_graph_from_txt("./src/graph/txt/graph_test.txt");
    println!("{:#?}", g);
}
