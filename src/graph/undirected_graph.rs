use std::{
    collections::HashMap,
    sync::{Arc, Mutex},
};

use super::{Graph, GraphError, Vertex, VertexIndex, VertexRef};

/// representing a graph using an adjacency list which is
/// 1) An array containing the graph vertices
/// 2) An array containing the graph edges
/// 3) For each edge, a pointer to each of its two endpoints
/// 4) for each vertex, a pointer to each of the incident edges

struct UndirectedGraph {
    vertices: HashMap<VertexIndex, VertexRef>,
}
impl Graph for UndirectedGraph {
    fn add_vertex(&mut self, index: VertexIndex, value: char) -> VertexRef {
        let vertex = Arc::new(Mutex::new(Vertex::new(value)));
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

impl UndirectedGraph {
    fn new() -> Self {
        Self {
            vertices: HashMap::new(),
        }
    }
    /// Pseudocode
    /// Input: graph G=(V,E) in adjancency list representation and a vertex s ∈ V
    /// postcondition: a vertex is reachabele from s if and only f it is marked as explored
    /// -----------------------------------------------------------------------------------
    /// mark s as explored, all other vertices as unexplored
    /// Q := a queue data structure, intialized with s
    /// while Q is not empty do
    ///     remove the vertex from the front of the Q, call it v
    ///     for each edge (v,w) in v's adjacency list do
    ///         if w is unexplored then
    ///         mark w as explored
    ///         add w to the end of Q
    pub fn bfs(&mut self, _start_vertex: VertexIndex) {
        unimplemented!()
    }

    /// Pseudocode
    /// Input: undirected graph G=(V,E) in adjancency list representation with V = {1,2,3,4,...,n}
    /// postcondition: for every u, v ∈ V, cc(u) = cc(v) if and only if u, v are in the same connected graph
    /// -----------------------------------------------------------------------------------
    /// mark s as explored, all other vertices as unexplored
    /// numCC := 0
    /// for i := 1 to n do
    ///     if i is unexplored then
    ///         numCC := numCC + 1
    ///         // call BFS starting at i (lines 2-8)
    ///         Q := a queue data structure, intialized with i
    ///         while Q is not empty do
    ///             remove the vertex from the front of the Q, call it v
    ///             cc(v) := numCC
    ///             for each edge (v,w) in v's adjacency list do
    ///                 if w is unexplored then
    ///                 mark w as explored
    ///                 add w to the end of Q
    pub fn ucc(&mut self) {
        unimplemented!()
    }

    /// DFS (iterative version) Pseudocode
    /// Input: graph G= (V, E) in adjancency list representation, and a vertex s ∈ V
    /// postcondition: a vertex is reachabele from s if and only if it is marked as "explored".
    /// -------------------------------------------------------------------------------------
    /// mark all vertices as unexplored
    /// S := a stack data structure, initialized with s     
    /// while S is not empty do
    ///     remove("pop") the vertex v from the front of S
    ///     if v is unexplored then
    ///         mark v as explored
    ///         for each edge (v,w) in v's adjancency list do
    ///             add("push") w to the front of S
    pub fn dfs_iterative() {
        unimplemented!()
    }

    fn clear_exploration(&mut self) {
        unimplemented!()
    }
}

impl Default for UndirectedGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let _ = graph.add_edge(1, 2);

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
        let _ = graph.add_edge(1, 2);
        let _ = graph.add_edge(1, 3);

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
        let _ = graph.add_edge(1, 2);

        // Verify that the edge exists in both directions
        let neighbors_1 = graph.get_neighbors(1);
        let neighbors_2 = graph.get_neighbors(2);

        assert!(neighbors_1.contains(&2));
        assert!(neighbors_2.contains(&1));
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
