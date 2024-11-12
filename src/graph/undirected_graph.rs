use std::collections::{HashMap, HashSet};

use super::{Graph, GraphError, VertexIndex};
use std::collections::VecDeque;

#[derive(Debug)]
struct Vertex {
    pub value: char,
    pub edges: HashSet<VertexIndex>,
}

impl Vertex {
    fn new(value: char) -> Self {
        Self {
            value,
            edges: HashSet::new(),
        }
    }
}

/// representing a graph using an adjacency list which is
/// 1) An array containing the graph vertices
/// 2) An array containing the graph edges
/// 3) For each edge, a pointer to each of its two endpoints
/// 4) for each vertex, a pointer to each of the incident edges

/// An undirected graph represented using an adjacency list.
pub struct UndirectedGraph {
    vertices: HashMap<VertexIndex, Vertex>,
}

impl Graph for UndirectedGraph {
    fn add_vertex(&mut self, index: VertexIndex, value: char) {
        self.vertices.insert(index, Vertex::new(value));
    }
    fn add_edge(&mut self, from: VertexIndex, to: VertexIndex) -> Result<(), GraphError> {
        if from == to {
            return Err(GraphError::SelfLoop);
        }

        if let Some(from_vertex) = self.vertices.get_mut(&from) {
            if from_vertex.edges.contains(&to) {
                return Err(GraphError::ParallelEdge);
            }
            from_vertex.edges.insert(to);
        } else {
            return Err(GraphError::VertexNotFound);
        }

        if let Some(to_vertex) = self.vertices.get_mut(&to) {
            if to_vertex.edges.contains(&from) {
                return Err(GraphError::ParallelEdge);
            }
            to_vertex.edges.insert(from);
        } else {
            self.vertices.get_mut(&from).unwrap().edges.remove(&to);
            return Err(GraphError::VertexNotFound);
        }

        Ok(())
    }
}

impl UndirectedGraph {
    pub fn new() -> Self {
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
    ///             mark w as explored
    ///             add w to the end of Q
    pub fn bfs(&self, start: VertexIndex) -> Result<Vec<VertexIndex>, GraphError> {
        if !self.vertices.contains_key(&start) {
            return Err(GraphError::VertexNotFound);
        }

        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        let mut bfs_order = Vec::new();

        queue.push_back(start);
        visited.insert(start);

        while let Some(current) = queue.pop_front() {
            bfs_order.push(current);

            if let Some(vertex) = self.vertices.get(&current) {
                for &neighbor in &vertex.edges {
                    if !visited.contains(&neighbor) {
                        visited.insert(neighbor);
                        queue.push_back(neighbor);
                    }
                }
            }
        }

        Ok(bfs_order)
    }

    /// Pseudocode
    /// Input: graph G=(V,E) in adjancency list representation and a vertex s ∈ V
    /// postcondition: for every vertex v ∈ V, the value l(v) equals the true shortest path distance dist(s,v)
    /// -----------------------------------------------------------------------------------
    /// mark s as explored, all other vertices as unexplored
    /// l(s):=0, l(v):= +infinity for every v != s
    /// Q := a queue data structure, intialized with s
    /// while Q is not empty do
    ///     remove the vertex from the front of the Q, call it v
    ///     for each edge (v,w) in v's adjacency list do
    ///         if w is unexplored then
    ///             mark w as explored
    ///             add w to the end of Q
    pub fn shortest_path_bfs(&self, start: usize) -> Result<HashMap<usize, usize>, GraphError> {
        if !self.vertices.contains_key(&start) {
            return Err(GraphError::VertexNotFound);
        }
        let mut dist = HashMap::new();
        let mut queue = VecDeque::new();

        // Start by setting the distance to the start node as 0
        dist.insert(start, 0);
        queue.push_back(start);

        while let Some(current) = queue.pop_front() {
            let current_distance = dist[&current];

            for neighbor in self.get_neighbors(current) {
                // If the neighbor hasn't been visited (i.e., it has no distance assigned)
                if !dist.contains_key(&neighbor) {
                    dist.insert(neighbor, current_distance + 1);
                    queue.push_back(neighbor);
                }
            }
        }

        Ok(dist)
    }

    /// Pseudocode undirect connected components
    /// Input: undirected graph G=(V,E) in adjancency list representation with V = {1,2,3,4,...,n}
    /// postcondition: for every u, v ∈ V, cc(u) = cc(v) if and only if u, v are in the same connected graph
    /// -----------------------------------------------------------------------------------
    /// mark s vertices as unexplored
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
    ///                     mark w as explored
    ///                     add w to the end of Q
    pub fn ucc(&mut self) -> HashMap<usize, Vec<usize>> {
        let mut visited = HashSet::new();
        let mut num_cc: usize = 0;
        let mut connected_components = HashMap::new();
        for (&v, _) in self.vertices.iter() {
            if !visited.contains(&v) {
                num_cc += 1;
                let mut queue = VecDeque::new();
                queue.push_back(v);
                visited.insert(v);

                while let Some(current) = queue.pop_front() {
                    let cc_vec = connected_components.entry(num_cc).or_insert_with(Vec::new);
                    cc_vec.push(current);
                    if let Some(vertex) = self.vertices.get(&current) {
                        for &neighbor in &vertex.edges {
                            if !visited.contains(&neighbor) {
                                visited.insert(neighbor);
                                queue.push_back(neighbor);
                            }
                        }
                    }
                }
            }
        }
        connected_components
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
    pub fn dfs_iterative(&self, start: VertexIndex) -> Result<Vec<VertexIndex>, GraphError> {
        if !self.vertices.contains_key(&start) {
            return Err(GraphError::VertexNotFound);
        }

        let mut visited = HashSet::new();
        let mut stack = Vec::new();
        let mut dfs_order = Vec::new();
        stack.push(start);

        while let Some(current) = stack.pop() {
            if !visited.contains(&current) {
                visited.insert(current);
                dfs_order.push(current);
                for v in self.get_neighbors(current) {
                    stack.push(v);
                }
            }
        }

        Ok(dfs_order)
    }

    /// DFS (recursive version) Pseudocode
    /// Input: graph G= (V, E) in adjancency list representation, and a vertex s ∈ V
    /// postcondition: a vertex is reachabele from s if and only if it is marked as "explored".
    /// -------------------------------------------------------------------------------------
    /// // all vertices unexplored before outer call mark s as explored
    /// mark s as explored
    /// for each edge (s,v) in s's adjancency list do
    ///     if v is unexplored then
    ///         DFS(G, v)
    pub fn dfs_recursive(
        &self,
        start: VertexIndex,
        visited_set: &mut HashSet<usize>,
        dfs_order: &mut Vec<usize>,
    ) -> Result<Vec<VertexIndex>, GraphError> {
        // Check if the starting vertex exists in the graph
        if !self.vertices.contains_key(&start) {
            return Err(GraphError::VertexNotFound);
        }

        // Mark the current vertex as visited
        visited_set.insert(start);

        // Recurse for each unvisited neighbor
        for neighbor in self.get_neighbors(start) {
            if !visited_set.contains(&neighbor) {
                self.dfs_recursive(neighbor, visited_set, dfs_order)?;
            }
        }

        dfs_order.push(start);
        Ok(dfs_order.to_vec())
    }

    fn get_neighbors(&self, index: VertexIndex) -> Vec<VertexIndex> {
        self.vertices
            .get(&index)
            .map_or(vec![], |v| v.edges.iter().cloned().collect())
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
        graph.add_vertex(1, 'A');
        assert!(graph.vertices.contains_key(&1));
        assert_eq!(graph.vertices.get(&1).unwrap().value, 'A');
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
    fn undirected_graph_add_parallel_edge() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        let _ = graph.add_edge(1, 2);

        // Attempt to add a parallel edge
        let result = graph.add_edge(1, 2);
        assert_eq!(result, Err(GraphError::ParallelEdge));
    }

    #[test]
    fn undirected_graph_add_self_loop() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(1, 'A');

        // Attempt to add a self-loop
        let result = graph.add_edge(1, 1);
        assert_eq!(result, Err(GraphError::SelfLoop));
    }

    #[test]
    fn test_bfs_traversal() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_vertex(3, 'C');
        graph.add_vertex(4, 'D');
        graph.add_vertex(5, 'E');
        let _ = graph.add_edge(1, 2);
        let _ = graph.add_edge(1, 3);
        let _ = graph.add_edge(2, 4);
        let _ = graph.add_edge(3, 5);

        let mut bfs_result = graph.bfs(1).unwrap();
        bfs_result.sort(); // sort as bfs orders isn't guranteed to be the same every run
        let expected_order = vec![1, 2, 3, 4, 5];
        // this test essentially ensures that all vertices are explored
        assert_eq!(bfs_result, expected_order);
    }

    #[test]
    fn test_dfs_iterative_traversal() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(0, 'S');
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_vertex(3, 'C');
        graph.add_vertex(4, 'D');
        graph.add_vertex(5, 'E');

        graph.add_edge(0, 1).unwrap();
        graph.add_edge(0, 2).unwrap();
        graph.add_edge(1, 3).unwrap();
        graph.add_edge(2, 3).unwrap();
        graph.add_edge(2, 4).unwrap();
        graph.add_edge(3, 4).unwrap();
        graph.add_edge(3, 5).unwrap();

        let mut bfs_result = graph.dfs_iterative(0).unwrap();
        bfs_result.sort(); // sort as bfs orders isn't guranteed to be the same every run
        let expected_order = vec![0, 1, 2, 3, 4, 5];
        // this test essentially ensures that all vertices are explored
        assert_eq!(bfs_result, expected_order);
    }
    #[test]
    fn test_dfs_recursive_traversal() {
        let mut graph = UndirectedGraph::new();

        graph.add_vertex(0, 'S');
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_vertex(3, 'C');
        graph.add_vertex(4, 'D');
        graph.add_vertex(5, 'E');

        graph.add_edge(0, 1).unwrap();
        graph.add_edge(0, 2).unwrap();
        graph.add_edge(1, 3).unwrap();
        graph.add_edge(2, 3).unwrap();
        graph.add_edge(2, 4).unwrap();
        graph.add_edge(3, 4).unwrap();
        graph.add_edge(3, 5).unwrap();

        let mut visited = HashSet::new();
        let mut dfs_order = Vec::new();

        let mut bfs_result = graph
            .dfs_recursive(0, &mut visited, &mut dfs_order)
            .unwrap();

        bfs_result.sort(); // sort as bfs orders isn't guranteed to be the same every run
        let expected_order = vec![0, 1, 2, 3, 4, 5];
        // this test essentially ensures that all vertices are explored
        assert_eq!(bfs_result, expected_order);
    }

    #[test]
    fn test_bfs_traversal_disconnected_graph() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_vertex(3, 'C');
        graph.add_vertex(4, 'D');

        let _ = graph.add_edge(1, 2);
        let _ = graph.add_edge(2, 3);

        let bfs_result = graph.bfs(1).unwrap();
        let expected_order = vec![1, 2, 3];
        assert_eq!(bfs_result, expected_order);
    }

    #[test]
    fn test_bfs_traversal_empty_graph() {
        let graph = UndirectedGraph::new();
        let bfs_result = graph.bfs(1);
        assert_eq!(bfs_result, Err(GraphError::VertexNotFound));
    }

    #[test]
    fn test_shortest_path_bfs() {
        let mut graph = UndirectedGraph::new();

        graph.add_vertex(0, 'S');
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_vertex(3, 'C');
        graph.add_vertex(4, 'D');
        graph.add_vertex(5, 'E');

        graph.add_edge(0, 1).unwrap();
        graph.add_edge(0, 2).unwrap();
        graph.add_edge(1, 3).unwrap();
        graph.add_edge(2, 3).unwrap();
        graph.add_edge(2, 4).unwrap();
        graph.add_edge(3, 4).unwrap();
        graph.add_edge(3, 5).unwrap();

        let shortest_paths = graph.shortest_path_bfs(0).unwrap();

        assert_eq!(shortest_paths.get(&0), Some(&0));
        assert_eq!(shortest_paths.get(&1), Some(&1));
        assert_eq!(shortest_paths.get(&2), Some(&1));
        assert_eq!(shortest_paths.get(&3), Some(&2));
        assert_eq!(shortest_paths.get(&4), Some(&2));
        assert_eq!(shortest_paths.get(&5), Some(&3));
    }

    #[test]
    fn test_shortest_path_bfs_no_path() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex(0, 'A');
        graph.add_vertex(1, 'B');
        graph.add_vertex(2, 'C');

        let shortest_paths = graph.shortest_path_bfs(0).unwrap();

        // Only vertex 0 should have a distance of 0, others should not be reachable
        assert_eq!(shortest_paths.get(&0), Some(&0));
        assert_eq!(shortest_paths.get(&1), None);
        assert_eq!(shortest_paths.get(&2), None);
    }

    #[test]
    fn test_disconnected_graph_shortest_path_bfs() {
        let mut graph = UndirectedGraph::new();

        graph.add_vertex(0, 'A');
        graph.add_vertex(1, 'B');
        graph.add_vertex(2, 'C');
        graph.add_vertex(3, 'D');

        graph.add_edge(0, 1).unwrap();
        graph.add_edge(2, 3).unwrap();

        let shortest_paths = graph.shortest_path_bfs(0).unwrap();

        // Expect distances only for vertices connected to 0
        assert_eq!(shortest_paths.get(&0), Some(&0));
        assert_eq!(shortest_paths.get(&1), Some(&1));
        assert_eq!(shortest_paths.get(&2), None);
        assert_eq!(shortest_paths.get(&3), None);
    }

    #[test]
    fn test_ucc() {
        // example 8.3.4 in the book
        let mut graph = UndirectedGraph::new();

        graph.add_vertex(0, 'S');
        graph.add_vertex(1, 'A');
        graph.add_vertex(2, 'B');
        graph.add_vertex(3, 'C');
        graph.add_vertex(4, 'D');
        graph.add_vertex(5, 'E');
        graph.add_vertex(6, 'F');
        graph.add_vertex(7, 'G');
        graph.add_vertex(8, 'H');
        graph.add_vertex(9, 'L');

        graph.add_edge(0, 4).unwrap();
        graph.add_edge(0, 2).unwrap();
        graph.add_edge(1, 3).unwrap();
        graph.add_edge(2, 4).unwrap();
        graph.add_edge(4, 6).unwrap();
        graph.add_edge(4, 8).unwrap();
        graph.add_edge(5, 7).unwrap();
        graph.add_edge(5, 9).unwrap();

        let connected_components = graph.ucc();

        // Define the expected connected components based on the graph structure.
        // Here, we expect three connected components:
        // - Component 1: {0, 2, 4, 6, 8}
        // - Component 2: {1, 3}
        // - Component 3: {5, 7, 9}
        let expected_components = vec![vec![0, 2, 4, 6, 8], vec![1, 3], vec![5, 7, 9]];

        // Extract the vectors from the tuples, sort each component, and then sort the outer list
        let mut sorted_components: Vec<Vec<usize>> = connected_components
            .into_iter()
            .map(|(_, mut comp)| {
                comp.sort_unstable();
                comp
            })
            .collect();
        sorted_components.sort();

        let mut expected_sorted: Vec<Vec<usize>> = expected_components
            .into_iter()
            .map(|mut comp| {
                comp.sort_unstable();
                comp
            })
            .collect();
        expected_sorted.sort();

        assert_eq!(sorted_components, expected_sorted);
    }
}
