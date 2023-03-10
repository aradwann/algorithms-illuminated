use super::{DirectedGraph, DirectedGraphRc};
use std::fs;

pub fn build_graph_from_txt(path: &str) -> DirectedGraph {
    // read the text file
    let contents = fs::read_to_string(path).unwrap();

    let edges_tuple_vec = extract_edges(contents);

    // get the last vertex in the array
    let last_vertex = edges_tuple_vec[edges_tuple_vec.len() - 1].0;

    let mut graph = DirectedGraph::new();

    for _ in 0..=last_vertex {
        graph.add_vertex('i');
    }

    for &(tail, head) in &edges_tuple_vec {
        graph.add_edge(tail as usize, head as usize);
    }
    graph
}

pub fn build_graph_rc_from_txt(path: &str) -> DirectedGraphRc {
    // read the text file
    let contents = fs::read_to_string(path).unwrap();

    let edges_tuple_vec = extract_edges(contents);

    // get the last vertex in the array
    let last_vertex = edges_tuple_vec[edges_tuple_vec.len() - 1].0;

    let mut graph = DirectedGraphRc::new();

    for _ in 0..=last_vertex {
        graph.add_vertex('i');
    }

    for &(tail, head) in &edges_tuple_vec {
        graph.add_edge(tail as usize, head as usize, None);
    }
    graph
}

/// extract a Vec of tuples
///
/// each tuple represents an edge (tail, head)
fn extract_edges(contents: String) -> Vec<(u32, u32)> {
    // make a Vec of tuples describing edges
    let edges_tuple_vec: Vec<(u32, u32)> = contents
        .lines()
        .map(|line| {
            let mut c = line.chars();

            let v1 = c.next().unwrap();

            // skip the space between the two numbers
            c.next();

            let v2 = c.next().unwrap();
            // subtract as the assignments txt begin is 1 indexed not zero-indexed
            (v1.to_digit(10).unwrap() - 1, v2.to_digit(10).unwrap() - 1)
        })
        .collect();
    edges_tuple_vec
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_tuple_of_edges_from_txt() {
        let txt = String::from("1 3\n2 3\n2 4\n3 4\n4 1\n");
        let extracted_edges = extract_edges(txt);
        let expected: Vec<(u32, u32)> = vec![(0, 2), (1, 2), (1, 3), (2, 3), (3, 0)];

        assert_eq!(expected, extracted_edges)
    }

    #[test]
    fn test_build_graph_from_txt() {
        let mut expected_graph = DirectedGraph::new();
        for _ in 0..4 {
            expected_graph.add_vertex('i')
        }
        let expected_edges: Vec<(usize, usize)> = vec![(0, 2), (1, 2), (1, 3), (2, 3), (3, 0)];
        for (tail, head) in expected_edges {
            expected_graph.add_edge(tail, head);
        }
        let extracted_graph = build_graph_from_txt("./src/graph/txt/graph_test.txt");

        // LOL
        let exptected_string = format!("{expected_graph:#?}");
        let extracted_string = format!("{extracted_graph:#?}");

        assert_eq!(exptected_string, extracted_string)
    }
}
