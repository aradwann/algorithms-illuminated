use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

type VertexIndex = usize;
type VertexRef = Arc<Mutex<Vertex>>;
#[derive(Debug, PartialEq)]
enum GraphError {
    SelfLoop,
    ParallelEdge,
    Cycle,
    VertexNotFound,
}
struct Vertex {
    value: char,
    edges: HashSet<VertexIndex>,
}

trait Graph {
    fn add_vertex(&mut self, index: VertexIndex, value: char) -> VertexRef;
    fn add_edge(&mut self, from: VertexIndex, to: VertexIndex) -> Result<(), GraphError>;
    fn get_neighbors(&self, index: VertexIndex) -> Vec<VertexIndex>;
}

struct DirectedGraph {
    vertices: HashMap<VertexIndex, VertexRef>,
}

struct UndirectedGraph {
    vertices: HashMap<VertexIndex, VertexRef>,
}

impl DirectedGraph {
    fn new() -> Self {
        Self {
            vertices: HashMap::new(),
        }
    }
}

impl UndirectedGraph {
    fn new() -> Self {
        Self {
            vertices: HashMap::new(),
        }
    }
}

impl Graph for DirectedGraph {
    fn add_vertex(&mut self, index: VertexIndex, value: char) -> VertexRef {
        let vertex = Arc::new(Mutex::new(Vertex {
            value,
            edges: HashSet::new(),
        }));
        self.vertices.insert(index, Arc::clone(&vertex));
        vertex
    }
    fn add_edge(&mut self, from: VertexIndex, to: VertexIndex) -> Result<(), GraphError> {
        // Check for self-loop
        if from == to {
            return Err(GraphError::SelfLoop);
        }

        // Check if the edge already exists
        if let Some(vertex) = self.vertices.get(&from) {
            if vertex.lock().unwrap().edges.contains(&to) {
                return Err(GraphError::ParallelEdge);
            }
            // Temporarily add the edge to check for cycles
            vertex.lock().unwrap().edges.insert(to);
        } else {
            return Err(GraphError::VertexNotFound);
        }

        // TODO: Check for cycles
        // if self.has_cycle() {
        //     // Remove the edge if it creates a cycle
        //     if let Some(vertex) = self.vertices.get(&from) {
        //         vertex.lock().unwrap().edges.remove(&to);
        //     }
        //     return Err(GraphError::Cycle);
        // }

        Ok(())
    }

    fn get_neighbors(&self, index: VertexIndex) -> Vec<VertexIndex> {
        self.vertices.get(&index).map_or(vec![], |v| {
            v.lock().unwrap().edges.iter().cloned().collect()
        })
    }
}

impl Graph for UndirectedGraph {
    fn add_vertex(&mut self, index: VertexIndex, value: char) -> VertexRef {
        let vertex = Arc::new(Mutex::new(Vertex {
            value,
            edges: HashSet::new(),
        }));
        self.vertices.insert(index, Arc::clone(&vertex));
        vertex
    }

    fn add_edge(&mut self, from: VertexIndex, to: VertexIndex) -> Result<(), GraphError> {
        // Check for self-loop
        if from == to {
            return Err(GraphError::SelfLoop);
        }

        // Check if the edge already exists
        if let Some(vertex) = self.vertices.get(&from) {
            if vertex.lock().unwrap().edges.contains(&to) {
                return Err(GraphError::ParallelEdge);
            }
            // Temporarily add the edge to check for cycles
            vertex.lock().unwrap().edges.insert(to);
        } else {
            return Err(GraphError::VertexNotFound);
        }

        // Check the other vertex
        if let Some(vertex) = self.vertices.get(&to) {
            if vertex.lock().unwrap().edges.contains(&from) {
                return Err(GraphError::ParallelEdge);
            }
            vertex.lock().unwrap().edges.insert(from);
        } else {
            // If the second vertex doesn't exist, remove the edge from the first vertex
            if let Some(vertex) = self.vertices.get(&from) {
                vertex.lock().unwrap().edges.remove(&to);
            }
            return Err(GraphError::VertexNotFound);
        }

        Ok(())
    }

    fn get_neighbors(&self, index: VertexIndex) -> Vec<VertexIndex> {
        self.vertices.get(&index).map_or(vec![], |v| {
            v.lock().unwrap().edges.iter().cloned().collect()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn directed_graph_add_vertex() {
        let mut graph = DirectedGraph::new();
        let vertex = graph.add_vertex(1, 'A');
        assert!(graph.vertices.contains_key(&1));
        assert_eq!(vertex.lock().unwrap().value, 'A');
    }

    #[test]
    fn directed_graph_add_edge() {
        let mut graph = DirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_edge(1, 2);

        let neighbors = graph.get_neighbors(1);
        assert_eq!(neighbors, vec![2]);

        let neighbors_2 = graph.get_neighbors(2);
        assert!(
            neighbors_2.is_empty(),
            "There should be no outgoing edge from vertex 2 in a directed graph"
        );
    }

    #[test]
    fn directed_graph_get_neighbors() {
        let mut graph = DirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_vertex(3, 'C');
        graph.add_edge(1, 2);
        graph.add_edge(1, 3);

        let neighbors = graph.get_neighbors(1);
        assert_eq!(neighbors, vec![2, 3]);
    }

    #[test]
    fn undirected_graph_add_vertex() {
        let mut graph = UndirectedGraph::new();
        let vertex = graph.add_vertex(1, 'A');
        assert!(graph.vertices.contains_key(&1));
        assert_eq!(vertex.lock().unwrap().value, 'A');
    }

    #[test]
    fn undirected_graph_add_edge() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_edge(1, 2);

        let neighbors_1 = graph.get_neighbors(1);
        let neighbors_2 = graph.get_neighbors(2);

        assert_eq!(neighbors_1, vec![2]);
        assert_eq!(
            neighbors_2,
            vec![1],
            "In an undirected graph, edge should exist in both directions"
        );
    }

    #[test]
    fn undirected_graph_get_neighbors() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_vertex(3, 'C');
        graph.add_edge(1, 2);
        graph.add_edge(1, 3);

        let mut actual_neighbors = graph.get_neighbors(1);
        let mut expected_neighbors = vec![2, 3];

        // Sort both vectors to ensure order doesn't cause assertion failure
        expected_neighbors.sort();
        actual_neighbors.sort();

        assert_eq!(actual_neighbors, expected_neighbors);
    }

    #[test]
    fn undirected_graph_bidirectional_edges() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_edge(1, 2);

        // Verify that the edge exists in both directions
        let neighbors_1 = graph.get_neighbors(1);
        let neighbors_2 = graph.get_neighbors(2);

        assert!(neighbors_1.contains(&2));
        assert!(neighbors_2.contains(&1));
    }

    #[test]
    fn directed_graph_no_bidirectional_edges() {
        let mut graph = DirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_edge(1, 2);

        // Verify that the edge does not exist in the reverse direction
        let neighbors_1 = graph.get_neighbors(1);
        let neighbors_2 = graph.get_neighbors(2);

        assert!(neighbors_1.contains(&2));
        assert!(
            !neighbors_2.contains(&1),
            "Directed graph should not have bidirectional edges"
        );
    }

    #[test]
    fn test_prevent_self_loops_and_parallel_edges() {
        let mut graph = DirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');

        // Test adding a valid edge
        assert!(
            graph.add_edge(1, 2).is_ok(),
            "Edge from 1 to 2 should be added"
        );

        // Test self-loop prevention
        assert_eq!(graph.add_edge(1, 1), Err(GraphError::SelfLoop));

        // Test parallel edge prevention
        assert_eq!(graph.add_edge(1, 2), Err(GraphError::ParallelEdge));

        // Add another edge and check
        assert!(
            graph.add_edge(2, 1).is_ok(),
            "Edge from 2 to 1 should be added"
        );

        // Confirm edges are correct
        assert_eq!(graph.get_neighbors(1), vec![2]);
        assert_eq!(graph.get_neighbors(2), vec![1]);
    }
    #[test]
    fn test_prevent_self_loops_and_parallel_edges_undirected() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');

        // Test adding a valid edge
        assert!(
            graph.add_edge(1, 2).is_ok(),
            "Edge between 1 and 2 should be added"
        );

        // Test self-loop prevention
        assert_eq!(graph.add_edge(1, 1), Err(GraphError::SelfLoop));

        // Test parallel edge prevention
        assert_eq!(graph.add_edge(1, 2), Err(GraphError::ParallelEdge));

        // Add another edge and check
        assert!(
            graph.add_edge(2, 1).is_err(),
            "Adding edge 2 to 1 should return error due to parallel edge"
        );

        // Confirm edges are correct
        assert_eq!(graph.get_neighbors(1), vec![2]);
        assert_eq!(graph.get_neighbors(2), vec![1]);
    }
}
