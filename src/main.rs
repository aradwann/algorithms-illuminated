use std::collections::HashMap;

use algorithms_illuminated::graph::DirectedGraph;
fn main() {
    let graph = DirectedGraph::build_from_file("src/graph/txt/scc_example_8_16.txt").unwrap();
    graph.print_graph();
    let scc = graph.reversed_topo_sort();
    // let counts = count_and_sort_top_five(scc);

    println!("{:?}", scc);
}

fn _count_and_sort_top_five(vec: Vec<usize>) -> Vec<(usize, usize)> {
    let mut counts = HashMap::new();

    // Count occurrences
    for &item in &vec {
        *counts.entry(item).or_insert(0) += 1;
    }

    // Convert to Vec<(usize, usize)> and sort by values (descending)
    let mut sorted_counts: Vec<(usize, usize)> = counts.into_iter().collect();
    sorted_counts.sort_by(|a, b| b.1.cmp(&a.1)); // Sort by value (descending)

    // Keep only the top 5
    sorted_counts.truncate(5);

    sorted_counts
}
