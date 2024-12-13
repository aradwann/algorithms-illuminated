use std::io::Write;
use std::{env::temp_dir, fs::File};

use algorithms_illuminated::graph::{DirectedGraph, GraphError};

#[test]
fn test_add_vertex() {
    let mut graph = DirectedGraph::new();
    let vertex = graph.add_vertex();

    // Check that the vertex was added and its index is correct
    assert_eq!(vertex.borrow().get_index(), 0);
    assert_eq!(graph.vertices.len(), 1);
}

#[test]
fn test_with_vertices() {
    let graph = DirectedGraph::with_vertices(3);

    // Check that the specified number of vertices were created
    assert_eq!(graph.vertices.len(), 3);

    // Check that each vertex has the correct index
    for (i, vertex) in graph.vertices.iter().enumerate() {
        assert_eq!(vertex.borrow().get_index(), i);
    }
}

#[test]
fn test_add_edge_success() {
    let graph = DirectedGraph::with_vertices(2);

    // Add a valid edge from vertex 0 to vertex 1
    let result = graph.add_edge(0, 1);
    assert!(result.is_ok());

    // Verify that the edge exists in the outgoing and incoming edges
    assert_eq!(graph.vertices[0].borrow().outgoing_edges.len(), 1);
    assert_eq!(graph.vertices[1].borrow().incoming_edges.len(), 1);
}
// Comment out the test to solve the scc.text
// #[test]
// fn test_add_edge_self_loop() {
//     let graph = DirectedGraph::with_vertices(1);

//     // Try to add a self-loop from vertex 0 to itself
//     let result = graph.add_edge(0, 0);
//     assert_eq!(result, Err(GraphError::SelfLoop));

//     // Ensure no edges were added
//     assert_eq!(graph.vertices[0].borrow().outgoing_edges.len(), 0);
//     assert_eq!(graph.vertices[0].borrow().incoming_edges.len(), 0);
// }

#[test]
fn test_add_edge_parallel_edge() {
    let graph = DirectedGraph::with_vertices(2);

    // Add the first edge from vertex 0 to vertex 1
    let result1 = graph.add_edge(0, 1);
    assert!(result1.is_ok());

    // Attempt to add a parallel edge from vertex 0 to vertex 1
    let result2 = graph.add_edge(0, 1);
    assert_eq!(result2, Err(GraphError::ParallelEdge));

    // Verify only one edge exists between vertex 0 and vertex 1
    assert_eq!(graph.vertices[0].borrow().outgoing_edges.len(), 1);
    assert_eq!(graph.vertices[1].borrow().incoming_edges.len(), 1);
}

#[test]
fn test_add_edge_vertex_not_found() {
    let graph = DirectedGraph::with_vertices(2);

    // Attempt to add an edge with an invalid vertex index
    let result = graph.add_edge(0, 3); // vertex 3 doesn't exist
    assert_eq!(result, Err(GraphError::VertexNotFound));

    // Ensure no edges were added
    assert_eq!(graph.vertices[0].borrow().outgoing_edges.len(), 0);
    assert_eq!(graph.vertices[1].borrow().incoming_edges.len(), 0);
}

#[test]
fn test_add_multiple_edges() {
    let graph = DirectedGraph::with_vertices(3);

    // Add multiple valid edges
    let result1 = graph.add_edge(0, 1);
    let result2 = graph.add_edge(1, 2);
    let result3 = graph.add_edge(0, 2);

    assert!(result1.is_ok());
    assert!(result2.is_ok());
    assert!(result3.is_ok());

    // Check outgoing edges for each vertex
    assert_eq!(graph.vertices[0].borrow().outgoing_edges.len(), 2); // edges to vertex 1 and 2
    assert_eq!(graph.vertices[1].borrow().outgoing_edges.len(), 1); // edge to vertex 2
    assert_eq!(graph.vertices[2].borrow().outgoing_edges.len(), 0); // no outgoing edges

    // Check incoming edges for each vertex
    assert_eq!(graph.vertices[1].borrow().incoming_edges.len(), 1); // edge from vertex 0
    assert_eq!(graph.vertices[2].borrow().incoming_edges.len(), 2); // edges from vertex 0 and 1
}

#[test]
fn test_dfs_recursive_traversal() {
    let graph = DirectedGraph::with_vertices(4);

    graph.add_edge(0, 1).unwrap();
    graph.add_edge(0, 2).unwrap();
    graph.add_edge(1, 3).unwrap();
    graph.add_edge(2, 3).unwrap();

    let mut dfs_order = graph.dfs_recursive(0).unwrap();

    dfs_order.sort(); // sort as bfs orders isn't guranteed to be the same every run
    let expected_order: Vec<usize> = vec![0, 1, 2, 3];
    // this test essentially ensures that all vertices are explored
    assert_eq!(dfs_order, expected_order);
}
#[test]
fn test_dfs_iterative_traversal() {
    let graph = DirectedGraph::with_vertices(4);

    graph.add_edge(0, 1).unwrap();
    graph.add_edge(0, 2).unwrap();
    graph.add_edge(1, 3).unwrap();
    graph.add_edge(2, 3).unwrap();

    let mut dfs_order = graph.dfs_iterative(0).unwrap();

    dfs_order.sort(); // sort as bfs orders isn't guranteed to be the same every run
    let expected_order: Vec<usize> = vec![0, 1, 2, 3];
    // this test essentially ensures that all vertices are explored
    assert_eq!(dfs_order, expected_order);
}

#[test]
fn test_topo_sort() {
    // Create a new graph with vertices (0, 1, 2, 3, 4)
    let graph = DirectedGraph::with_vertices(5);

    // Add directed edges to create a Directed Acyclic Graph (DAG)
    // 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3, 3 -> 4
    graph.add_edge(0, 1).unwrap();
    graph.add_edge(0, 2).unwrap();
    graph.add_edge(1, 3).unwrap();
    graph.add_edge(2, 3).unwrap();
    graph.add_edge(3, 4).unwrap();

    // Perform topological sort
    let topo_sort_result = graph.topo_sort(false);

    // Verify the result
    // Expected order: 0, 1, 2, 3, 4 or any valid topological order
    for (from, to) in [
        (0, 1), // 0 -> 1
        (0, 2), // 0 -> 2
        (1, 3), // 1 -> 3
        (2, 3), // 2 -> 3
        (3, 4), // 3 -> 4
    ] {
        assert!(
            topo_sort_result[from] < topo_sort_result[to],
            "Vertex {} should come before vertex {} in topological sort",
            from,
            to
        );
    }
}

#[test]
fn test_kosaraju() {
    let graph = DirectedGraph::build_from_file("src/graph/txt/scc_test5.txt", true).unwrap();

    let count = graph.get_top_five_sccs();

    assert_eq!(count, vec![(4, 6), (2, 3), (3, 2), (1, 1)]);
}

#[test]
fn test_build_from_file() {
    // Create a temporary file path in the system's temp directory
    let mut path = temp_dir();
    path.push("test_graph.txt");

    // Create the file and write graph edges to it
    let mut file = File::create(&path).expect("Failed to create temporary file");

    // Writing directed edges (tail to head)
    writeln!(file, "1 3").unwrap();
    writeln!(file, "2 3").unwrap();
    writeln!(file, "2 4").unwrap();
    writeln!(file, "3 4").unwrap();
    writeln!(file, "4 1").unwrap();

    // Build the graph from the file
    let graph = DirectedGraph::build_from_file(&path, false).expect("Failed to build graph");

    // Check vertices
    assert_eq!(graph.vertices.len(), 4); // Max index is 4, so 5 vertices (0 through 4)

    // Check edges for correctness
    assert_eq!(graph.vertices[0].borrow().outgoing_edges.len(), 1);
    assert_eq!(graph.vertices[1].borrow().outgoing_edges.len(), 2);
    assert_eq!(graph.vertices[2].borrow().outgoing_edges.len(), 1);
    assert_eq!(graph.vertices[3].borrow().outgoing_edges.len(), 1);

    // Validate specific edges
    assert!(graph.vertices[0]
        .borrow()
        .outgoing_edges
        .iter()
        .any(|v| v.borrow().get_index() == 2));
    assert!(graph.vertices[1]
        .borrow()
        .outgoing_edges
        .iter()
        .any(|v| v.borrow().get_index() == 2));
    assert!(graph.vertices[1]
        .borrow()
        .outgoing_edges
        .iter()
        .any(|v| v.borrow().get_index() == 3));
    assert!(graph.vertices[2]
        .borrow()
        .outgoing_edges
        .iter()
        .any(|v| v.borrow().get_index() == 3));
    assert!(graph.vertices[3]
        .borrow()
        .outgoing_edges
        .iter()
        .any(|v| v.borrow().get_index() == 0));

    // Clean up: Remove the temporary file after test
    std::fs::remove_file(&path).expect("Failed to delete temporary file");
}
