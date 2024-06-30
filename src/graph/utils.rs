use super::DirectedGraph;
use std::fs;

pub fn build_graph_from_txt(path: &str) -> DirectedGraph {
    // Read the text file
    let contents = fs::read_to_string(path).expect("Failed to read the file");

    let edges = extract_edges(&contents);

    // Determine the highest vertex value
    let last_vertex = edges
        .iter()
        .flat_map(|&(v1, v2)| vec![v1, v2])
        .max()
        .unwrap_or(0);

    let mut graph = DirectedGraph::new();

    // Add vertices to the graph
    for _ in 0..=last_vertex {
        graph.add_vertex('i');
    }

    // Add edges to the graph
    for &(tail, head) in &edges {
        graph.add_edge(tail as usize, head as usize, None);
    }

    graph
}

/// Extract a Vec of tuples representing edges (tail, head)
fn extract_edges(contents: &str) -> Vec<(u32, u32)> {
    contents
        .lines()
        .map(|line| {
            let mut chars = line.chars();
            let v1 = chars.next().unwrap();
            let _ = chars.next(); // Skip the space
            let v2 = chars.next().unwrap();

            let v1 = v1.to_digit(10).unwrap() - 1;
            let v2 = v2.to_digit(10).unwrap() - 1;

            (v1, v2)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_edges() {
        let txt = "1 3\n2 3\n2 4\n3 4\n4 1\n";
        let extracted_edges = extract_edges(txt);
        let expected: Vec<(u32, u32)> = vec![(0, 2), (1, 2), (1, 3), (2, 3), (3, 0)];

        assert_eq!(expected, extracted_edges);
    }

    #[test]
    fn test_build_graph_from_txt() {
        let mut expected_graph = DirectedGraph::new();
        for _ in 0..4 {
            expected_graph.add_vertex('i');
        }
        let expected_edges: Vec<(usize, usize)> = vec![(0, 1), (0, 2), (1, 3), (2, 3)];
        for (tail, head) in expected_edges {
            expected_graph.add_edge(tail, head, None);
        }

        let extracted_graph = build_graph_from_txt("./src/graph/txt/graph_test2.txt");

        let expected_string = format!("{expected_graph:#?}");
        let extracted_string = format!("{extracted_graph:#?}");

        assert_eq!(expected_string, extracted_string);
    }
}
