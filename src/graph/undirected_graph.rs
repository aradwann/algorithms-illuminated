use std::collections::{BTreeMap, HashMap, HashSet};

use super::{Graph, GraphError, Length, VertexIndex};
use std::collections::VecDeque;

#[derive(Debug, PartialEq)]
struct Vertex {
    index: VertexIndex,
    pub edges: Vec<(VertexIndex, Length)>,
}

impl Vertex {
    /// Creates a new [`Vertex`].
    fn new(index: VertexIndex) -> Self {
        Self {
            edges: Vec::new(),
            index, // NOTE: this is has to be updated if the graph vertices indexes are updated
        }
    }
}

/// representing a graph using an adjacency list which is
/// 1) An array containing the graph vertices
/// 2) An array containing the graph edges
/// 3) For each edge, a pointer to each of its two endpoints
/// 4) for each vertex, a pointer to each of the incident edges
///
/// An undirected graph represented using an adjacency list.
pub struct UndirectedGraph {
    vertices: Vec<Vertex>,
}

impl Graph for UndirectedGraph {
    fn add_vertex(&mut self) {
        self.vertices.push(Vertex::new(self.vertices.len()));
    }

    fn add_edge(
        &mut self,
        from: VertexIndex,
        to: VertexIndex,
        length: Length,
    ) -> Result<(), GraphError> {
        if from == to {
            return Err(GraphError::SelfLoop);
        }
        if !self.is_valid_vertex(from) || !self.is_valid_vertex(to) {
            return Err(GraphError::VertexNotFound);
        }
        if self.vertices[from].edges.iter().any(|&(v, _)| v == to) {
            return Err(GraphError::ParallelEdge);
        }

        self.vertices[from].edges.push((to, length));
        self.vertices[to].edges.push((from, length));
        Ok(())
    }
    fn add_unit_edge(&mut self, from: VertexIndex, to: VertexIndex) -> Result<(), GraphError> {
        self.add_edge(from, to, 1)
    }
}
impl UndirectedGraph {
    pub fn new() -> Self {
        Self {
            vertices: Vec::new(),
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
        if !self.is_valid_vertex(start) {
            return Err(GraphError::VertexNotFound);
        }

        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        let mut result = Vec::new();

        queue.push_back(start);
        visited.insert(start);

        while let Some(current) = queue.pop_front() {
            result.push(current);
            for &(neighbor, _) in &self.vertices[current].edges {
                if visited.insert(neighbor) {
                    queue.push_back(neighbor);
                }
            }
        }

        Ok(result)
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
    pub fn shortest_path_bfs(
        &self,
        start: VertexIndex,
    ) -> Result<HashMap<VertexIndex, usize>, GraphError> {
        if !self.is_valid_vertex(start) {
            return Err(GraphError::VertexNotFound);
        }

        let mut distances = HashMap::new();
        let mut queue = VecDeque::new();

        distances.insert(start, 0);
        queue.push_back(start);

        while let Some(current) = queue.pop_front() {
            let current_distance = distances[&current];
            for &(neighbor, _) in &self.vertices[current].edges {
                if *distances.entry(neighbor).or_insert(current_distance + 1)
                    == &current_distance + 1
                {
                    queue.push_back(neighbor);
                }
            }
        }

        Ok(distances)
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
    pub fn connected_components(&self) -> HashMap<usize, Vec<usize>> {
        let mut visited = HashSet::new();
        let mut components = HashMap::new();
        let mut component_id = 0;

        for vertex in &self.vertices {
            if visited.insert(vertex.index) {
                component_id += 1;
                let mut queue = VecDeque::new();
                queue.push_back(vertex.index);

                while let Some(current) = queue.pop_front() {
                    components
                        .entry(component_id)
                        .or_insert_with(Vec::new)
                        .push(current);
                    for &(neighbor, _) in &self.vertices[current].edges {
                        if visited.insert(neighbor) {
                            queue.push_back(neighbor);
                        }
                    }
                }
            }
        }

        components
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
        if !self.is_valid_vertex(start) {
            return Err(GraphError::VertexNotFound);
        }

        let mut visited = HashSet::new();
        let mut stack = Vec::new();
        let mut result = Vec::new();

        stack.push(start);

        while let Some(current) = stack.pop() {
            if visited.insert(current) {
                result.push(current);
                for &(neighbor, _) in self.vertices[current].edges.iter().rev() {
                    stack.push(neighbor);
                }
            }
        }

        Ok(result)
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
        visited: &mut HashSet<usize>,
        dfs_order: &mut Vec<usize>,
    ) -> Result<Vec<VertexIndex>, GraphError> {
        // Check if the starting vertex exists in the graph
        if self.vertices.get(start).is_none() {
            return Err(GraphError::VertexNotFound);
        }

        visited.insert(start);

        for &(neighbor, _) in &self.vertices[start].edges {
            if visited.insert(neighbor) {
                self.dfs_recursive(neighbor, visited, dfs_order)?;
            }
        }

        dfs_order.push(start);
        Ok(dfs_order.to_vec())
    }

    /// Dijkstra Pseudocode
    /// Input: directed graph G= (V, E) in adjancency list representation and a vertex s ∈ V,
    ///        a length le >= 0 for each e ∈ E
    /// postcondition: for every vertex v, the value len(v)
    ///                equals the true shortest-path distance dist(s,v)
    /// -------------------------------------------------------------------------------------
    /// // Initialization
    /// X := {s}
    /// len(s) := 0, len(v) := +∞ for every v != s
    /// // Main loop
    /// while there is an edge (v,w) with v ∈ X, w ∉ X do
    ///     (v*,w*) := such an edge minimizing len(v) + lvw
    ///     add w* to X
    ///     len(w*) := len(v*) + lv*w*
    pub fn dijkstra(
        &self,
        start: VertexIndex,
    ) -> Result<BTreeMap<VertexIndex, Length>, GraphError> {
        if !self.is_valid_vertex(start) {
            return Err(GraphError::VertexNotFound);
        }
        // using BTreeMap instead of a hashmap to get a result sorted by key order
        let mut distances: BTreeMap<VertexIndex, Length> = BTreeMap::new();

        // Initialize distances to infinity and start vertex to 0.
        for vertex in 0..self.vertices.len() {
            distances.insert(vertex, usize::MAX);
        }
        distances.insert(start, 0);

        // Set of vertices for which the shortest distance is finalized.
        let mut x: HashSet<VertexIndex> = HashSet::new();
        x.insert(start);

        while x.len() < self.vertices.len() {
            let mut candidate_edge: Option<(VertexIndex, VertexIndex, Length)> = None;

            // Find the edge (v*, w*) minimizing len(v) + lvw.
            for &v in &x {
                for &(w, weight) in &self.vertices[v].edges {
                    if !x.contains(&w) {
                        let new_distance = distances[&v].saturating_add(weight);
                        if candidate_edge.is_none() || new_distance < candidate_edge.unwrap().2 {
                            candidate_edge = Some((v, w, new_distance));
                        }
                    }
                }
            }

            if let Some((_, w_star, len_w_star)) = candidate_edge {
                x.insert(w_star);
                distances.insert(w_star, len_w_star);
            } else {
                break; // No more edges to process.
            }
        }

        Ok(distances)
    }

    /// Validates if a vertex index exists
    fn is_valid_vertex(&self, index: VertexIndex) -> bool {
        index < self.vertices.len()
    }

    /// Creates a graph from a text file containing an adjacency list.
    /// Each line of the file represents a vertex and its edges in the format:
    /// "<vertex> <neighbor1,length1> <neighbor2,length2> ..."
    ///
    /// For example:
    /// "6 141,8200 74,510 ..." means vertex 6 is connected to 141 with weight 8200, and 74 with weight 510.
    pub fn from_file(file_path: &str) -> Result<Self, std::io::Error> {
        use std::fs::File;
        use std::io::{BufRead, BufReader};

        let file = File::open(file_path)?;
        let reader = BufReader::new(file);

        let mut graph = UndirectedGraph::new();

        for line in reader.lines() {
            let line = line?;
            let parts: Vec<&str> = line.split_whitespace().collect();

            if parts.is_empty() {
                continue;
            }

            let vertex: usize = parts[0].parse().expect("Invalid vertex index");

            while graph.vertices.len() < vertex {
                graph.add_vertex();
            }

            for edge in &parts[1..] {
                let edge_parts: Vec<&str> = edge.split(',').collect();
                if edge_parts.len() != 2 {
                    continue;
                }

                let neighbor: usize = edge_parts[0].parse().expect("Invalid neighbor index");
                let length: Length = edge_parts[1].parse().expect("Invalid edge length");

                while graph.vertices.len() < neighbor {
                    graph.add_vertex();
                }

                if !graph.vertices[vertex - 1]
                    .edges
                    .iter()
                    .any(|&(v, _)| v == neighbor - 1)
                {
                    graph.add_edge(vertex - 1, neighbor - 1, length).unwrap();
                }
            }
        }

        Ok(graph)
    }
    /// Prints the graph in a readable format.
    pub fn print_graph(&self) {
        for (index, vertex) in self.vertices.iter().enumerate() {
            print!("{}:", index + 1);
            for &(neighbor, length) in &vertex.edges {
                print!(" {}({})", neighbor + 1, length);
            }
            println!();
        }
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
        graph.add_vertex();
        assert!(!graph.vertices.is_empty());
    }

    #[test]
    fn test_add_edge() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_unit_edge(0, 1).unwrap();
        assert_eq!(graph.vertices[0].edges, vec![(1, 1)]);
        assert_eq!(graph.vertices[1].edges, vec![(0, 1)]);
    }

    #[test]
    fn undirected_graph_add_parallel_edge() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex();
        graph.add_vertex();
        let _ = graph.add_unit_edge(0, 1);

        // Attempt to add a parallel edge
        let result = graph.add_unit_edge(0, 1);
        assert_eq!(result, Err(GraphError::ParallelEdge));
    }

    #[test]
    fn undirected_graph_add_self_loop() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex();

        // Attempt to add a self-loop
        let result = graph.add_unit_edge(0, 0);
        assert_eq!(result, Err(GraphError::SelfLoop));
    }

    #[test]
    fn test_bfs_traversal() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        let _ = graph.add_unit_edge(0, 1);
        let _ = graph.add_unit_edge(0, 2);
        let _ = graph.add_unit_edge(1, 3);
        let _ = graph.add_unit_edge(2, 4);

        let mut bfs_result = graph.bfs(0).unwrap();
        bfs_result.sort(); // sort as bfs orders isn't guranteed to be the same every run
        let expected_order = vec![0, 1, 2, 3, 4];
        // this test essentially ensures that all vertices are explored
        assert_eq!(bfs_result, expected_order);
    }

    #[test]
    fn test_dfs_iterative_traversal() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();

        graph.add_unit_edge(0, 1).unwrap();
        graph.add_unit_edge(0, 2).unwrap();
        graph.add_unit_edge(1, 3).unwrap();
        graph.add_unit_edge(2, 3).unwrap();
        graph.add_unit_edge(2, 4).unwrap();
        graph.add_unit_edge(3, 4).unwrap();
        graph.add_unit_edge(3, 5).unwrap();

        let mut bfs_result = graph.dfs_iterative(0).unwrap();
        bfs_result.sort(); // sort as bfs orders isn't guranteed to be the same every run
        let expected_order = vec![0, 1, 2, 3, 4, 5];
        // this test essentially ensures that all vertices are explored
        assert_eq!(bfs_result, expected_order);
    }
    #[test]
    fn test_dfs_recursive_traversal() {
        let mut graph = UndirectedGraph::new();

        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();

        graph.add_unit_edge(0, 1).unwrap();
        graph.add_unit_edge(0, 2).unwrap();
        graph.add_unit_edge(1, 3).unwrap();
        graph.add_unit_edge(2, 3).unwrap();
        graph.add_unit_edge(2, 4).unwrap();
        graph.add_unit_edge(3, 4).unwrap();
        graph.add_unit_edge(3, 5).unwrap();

        let mut visited: HashSet<usize> = HashSet::new();
        let mut dfs_order = Vec::new();

        let mut bfs_result: Vec<usize> = graph
            .dfs_recursive(0, &mut visited, &mut dfs_order)
            .unwrap();

        bfs_result.sort(); // sort as bfs orders isn't guranteed to be the same every run
        let expected_order: Vec<usize> = vec![0, 1, 2, 3, 4, 5];
        // this test essentially ensures that all vertices are explored
        assert_eq!(bfs_result, expected_order);
    }

    #[test]
    fn test_bfs_traversal_disconnected_graph() {
        let mut graph = UndirectedGraph::new();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();

        let _ = graph.add_unit_edge(0, 1);
        let _ = graph.add_unit_edge(1, 2);

        let bfs_result = graph.bfs(0).unwrap();
        let expected_order = vec![0, 1, 2];
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

        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();

        graph.add_unit_edge(0, 1).unwrap();
        graph.add_unit_edge(0, 2).unwrap();
        graph.add_unit_edge(1, 3).unwrap();
        graph.add_unit_edge(2, 3).unwrap();
        graph.add_unit_edge(2, 4).unwrap();
        graph.add_unit_edge(3, 4).unwrap();
        graph.add_unit_edge(3, 5).unwrap();

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
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();

        let shortest_paths = graph.shortest_path_bfs(0).unwrap();

        // Only vertex 0 should have a distance of 0, others should not be reachable
        assert_eq!(shortest_paths.get(&0), Some(&0));
        assert_eq!(shortest_paths.get(&1), None);
        assert_eq!(shortest_paths.get(&2), None);
    }

    #[test]
    fn test_disconnected_graph_shortest_path_bfs() {
        let mut graph = UndirectedGraph::new();

        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();

        graph.add_unit_edge(0, 1).unwrap();
        graph.add_unit_edge(2, 3).unwrap();

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

        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();
        graph.add_vertex();

        graph.add_unit_edge(0, 4).unwrap();
        graph.add_unit_edge(0, 2).unwrap();
        graph.add_unit_edge(1, 3).unwrap();
        graph.add_unit_edge(2, 4).unwrap();
        graph.add_unit_edge(4, 6).unwrap();
        graph.add_unit_edge(4, 8).unwrap();
        graph.add_unit_edge(5, 7).unwrap();
        graph.add_unit_edge(5, 9).unwrap();

        let connected_components = graph.connected_components();

        // Define the expected connected components based on the graph structure.
        // Here, we expect three connected components:
        // - Component 1: {0, 2, 4, 6, 8}
        // - Component 2: {1, 3}
        // - Component 3: {5, 7, 9}
        let expected_components = vec![vec![0, 2, 4, 6, 8], vec![1, 3], vec![5, 7, 9]];

        // Extract the vectors from the tuples, sort each component, and then sort the outer list
        let mut sorted_components: Vec<Vec<usize>> = connected_components
            .into_values()
            .map(|mut comp| {
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

    #[test]
    fn test_dijkstra() {
        // Create a simple graph
        let mut graph = UndirectedGraph::new();
        for _ in 0..5 {
            graph.add_vertex();
        }

        // Add edges
        graph.add_edge(0, 1, 4).unwrap();
        graph.add_edge(0, 2, 1).unwrap();
        graph.add_edge(2, 1, 2).unwrap();
        graph.add_edge(1, 3, 1).unwrap();
        graph.add_edge(3, 4, 3).unwrap();
        graph.add_edge(2, 4, 10).unwrap();

        // Run Dijkstra's algorithm from vertex 0
        let distances = graph.dijkstra(0).expect("Dijkstra failed");

        // Expected distances
        let expected_distances = vec![
            (0, 0), // Distance to itself is 0
            (1, 3), // Path: 0 -> 2 -> 1
            (2, 1), // Direct edge: 0 -> 2
            (3, 4), // Path: 0 -> 2 -> 1 -> 3
            (4, 7), // Path: 0 -> 2 -> 1 -> 3 -> 4
        ];

        for (vertex, expected_distance) in expected_distances {
            assert_eq!(distances[&vertex], expected_distance, "Vertex: {}", vertex);
        }
    }
    #[test]
    fn test_dijkstra_no_path() {
        // Create a graph with disconnected components
        let mut graph = UndirectedGraph::new();
        for _ in 0..6 {
            graph.add_vertex();
        }

        // Add edges only between some vertices
        graph.add_edge(0, 1, 3).unwrap();
        graph.add_edge(1, 2, 5).unwrap();
        graph.add_edge(3, 4, 2).unwrap();
        // Vertex 5 is completely disconnected

        // Run Dijkstra's algorithm from vertex 0
        let distances = graph.dijkstra(0).expect("Dijkstra failed");

        // Expected distances
        let expected_distances = vec![
            (0, 0),          // Distance to itself is 0
            (1, 3),          // Direct edge: 0 -> 1
            (2, 8),          // Path: 0 -> 1 -> 2
            (3, usize::MAX), // No path to vertex 3
            (4, usize::MAX), // No path to vertex 4
            (5, usize::MAX), // No path to vertex 5 (completely disconnected)
        ];

        for (vertex, expected_distance) in expected_distances {
            assert_eq!(distances[&vertex], expected_distance, "Vertex: {}", vertex);
        }
    }
}
