use std::{
    cell::RefCell,
    collections::HashSet,
    fs::File,
    io::{self, BufRead},
    path::Path,
    rc::{Rc, Weak},
};

use super::{GraphError, VertexIndex};

/// representing a graph using an adjacency list which is
/// 1) An array containing the graph vertices
/// 2) An array containing the graph edges
/// 3) For each edge, a pointer to each of its two endpoints
/// 4) for each vertex, a pointer to each of the incident edges
///
/// for directed graph:
/// each edge keeps track of which endpoint is tail and which endpoint is head
/// each vertex maintains two arrays of pointers, one for the outgoing edges and one for the incoming edges
///

type VertexRc = Rc<RefCell<Vertex>>;
type VertexWeak = Weak<RefCell<Vertex>>;

/// vec of topological order of the vertices
/// where the index in the vector reporesent the vertex index
/// and the value represent its topological order
type TopologicalSort = Vec<usize>;

#[derive(Debug)]
pub struct Vertex {
    index: VertexIndex,
    outgoing_edges: Vec<VertexRc>,
    incoming_edges: Vec<VertexWeak>, // Weak to avoid cycles
}

impl Vertex {
    fn new(index: VertexIndex) -> Self {
        Vertex {
            index,
            outgoing_edges: vec![],
            incoming_edges: vec![],
        }
    }
    fn get_index(&self) -> VertexIndex {
        self.index
    }

    // this should be used whenver it is required to change the vertex index in the graph
    fn _set_index(&mut self, index: VertexIndex) {
        self.index = index;
    }
}

#[derive(Debug)]
pub struct DirectedGraph {
    vertices: Vec<VertexRc>,
}

impl DirectedGraph {
    pub fn new() -> Self {
        DirectedGraph { vertices: vec![] }
    }

    pub fn add_vertex(&mut self) -> VertexRc {
        let vertex = Rc::new(RefCell::new(Vertex::new(self.vertices.len())));
        self.vertices.push(Rc::clone(&vertex));
        vertex
    }

    /// Initialize the graph with the specified number of vertices.
    pub fn with_vertices(num_vertices: usize) -> Self {
        let mut graph = DirectedGraph::new();
        for _ in 0..num_vertices {
            graph.add_vertex();
        }
        graph
    }

    /// Adds an edge from the vertex at `tail_index` to `head_index` if valid.
    /// Returns `Ok(())` if the edge is successfully added, or a `GraphError` if there's an error.
    pub fn add_edge(
        &self,
        tail_index: VertexIndex,
        head_index: VertexIndex,
    ) -> Result<(), GraphError> {
        // Check for self-loop
        if tail_index == head_index {
            return Err(GraphError::SelfLoop);
        }

        // Ensure tail and head are valid indices in the graph
        if tail_index >= self.vertices.len() || head_index >= self.vertices.len() {
            return Err(GraphError::VertexNotFound);
        }

        // Get the vertices for the tail and head indices
        let tail = &self.vertices[tail_index];
        let head = &self.vertices[head_index];

        // Check for parallel edge
        if tail
            .borrow()
            .outgoing_edges
            .iter()
            .any(|edge| Rc::ptr_eq(edge, head))
        {
            return Err(GraphError::ParallelEdge);
        }

        // If validations pass, add the edge
        tail.borrow_mut().outgoing_edges.push(Rc::clone(head));
        head.borrow_mut().incoming_edges.push(Rc::downgrade(tail));

        Ok(())
    }

    pub fn dfs_recursive(&self, start: VertexIndex) -> Result<Vec<usize>, GraphError> {
        let mut visited: HashSet<usize> = HashSet::new();
        let mut dfs_order = Vec::new();
        self.dfs_recursive_subroutine(start, &mut visited, &mut dfs_order)
    }
    /// DFS (recursive version) Pseudocode
    /// Input: graph G= (V, E) in adjancency list representation, and a vertex s ∈ V
    /// postcondition: a vertex is reachabele from s if and only if it is marked as "explored".
    /// -------------------------------------------------------------------------------------
    /// // all vertices unexplored before outer call
    /// mark s as explored
    /// for each edge (s,v) in s's adjacency list do
    ///     if v is unexplored then
    ///         dfs(G, v)
    fn dfs_recursive_subroutine(
        &self,
        start: VertexIndex,
        visited: &mut HashSet<usize>,
        order: &mut Vec<usize>,
    ) -> Result<Vec<usize>, GraphError> {
        // Ensure the starting vertex exists
        let vertex = self.vertices.get(start).ok_or(GraphError::VertexNotFound)?;

        // Mark the current vertex as visited
        visited.insert(start);

        // Recurse for unvisited neighbors
        for neighbor in &vertex.borrow().outgoing_edges {
            let neighbor_index = neighbor.borrow().index;
            if !visited.contains(&neighbor_index) {
                self.dfs_recursive_subroutine(neighbor_index, visited, order)?;
            }
        }

        // Record the vertex in the DFS order
        order.push(start);
        Ok(order.to_vec())
    }

    /// TopoSort Pseudocode
    /// Input: directed acyclic graph G= (V, E) in adjancency list representation
    /// postcondition: the f-values of vertices constitute a topological ordering of G.
    /// -------------------------------------------------------------------------------------
    /// mark all vertices as unexplored
    /// curLabel := |V| // keeps track of ordering
    /// for every v ∈ V do
    ///     if v is unexplored then // in a prior DFS
    ///         DFS-Topo(G, v)
    pub fn topo_sort(&self, reversed: bool) -> Vec<(usize, usize)> {
        let vertices = &self.vertices;
        let vertcies_num = vertices.len();
        let mut current_label = vertcies_num;
        let mut visited_set = HashSet::new();
        let mut topological_sort = vec![0; vertcies_num];
        for v in vertices {
            let vertex_index = &v.borrow().get_index();
            if !visited_set.contains(vertex_index) {
                self.dfs_topo(
                    *vertex_index,
                    &mut visited_set,
                    &mut topological_sort,
                    &mut current_label,
                    reversed,
                );
            }
        }
        // topological_sort

        let mut sorted_vertices: Vec<(usize, usize)> = topological_sort
            .iter()
            .enumerate() // Produces (index, &label)
            .map(|(index, &label)| (label, index))
            .collect();

        // Sort the pairs by label (ascending order)
        sorted_vertices.sort_by_key(|&(label, _)| label);

        sorted_vertices
    }

    /// DFS-Topo Pseudocode
    /// Input: graph G= (V, E) in adjancency list representation and a vertex s ∈ V
    /// postcondition: every vertex reachable from s is marked as 'explored' and has an assigned f-value
    /// -------------------------------------------------------------------------------------
    /// mark s as explored
    ///
    /// for each edge (s,v) in s's outgoing adjacency list do
    ///     if v is unexplored then
    ///         DFS-Topo(G,v)
    /// f(s) := curLabel    // s's position in ordering
    /// curLabel := curLabel -1 // work right-to-left
    fn dfs_topo(
        &self,
        vertex_index: VertexIndex,
        visited: &mut HashSet<usize>,
        topological_sort: &mut TopologicalSort,
        current_label: &mut usize,
        reversed: bool,
    ) {
        let vertex = self.vertices.get(vertex_index).unwrap();

        // Mark the current vertex as visited
        visited.insert(vertex_index);

        if !reversed {
            // Recurse for unvisited neighbors
            for neighbor in &vertex.borrow().outgoing_edges {
                let neighbor_index = neighbor.borrow().get_index();
                if !visited.contains(&neighbor_index) {
                    self.dfs_topo(
                        neighbor_index,
                        visited,
                        topological_sort,
                        current_label,
                        reversed,
                    );
                }
            }
        } else {
            // Recurse for unvisited vertices that have edges pointing to this vertex (incoming edges)
            for neighbor_weak in &vertex.borrow().incoming_edges {
                if let Some(neighbor_rc) = neighbor_weak.upgrade() {
                    // Upgrade the Weak reference to Rc
                    let neighbor_index = neighbor_rc.borrow().get_index();
                    if !visited.contains(&neighbor_index) {
                        // Visit the incoming vertex
                        self.dfs_topo(
                            neighbor_index,
                            visited,
                            topological_sort,
                            current_label,
                            reversed,
                        );
                    }
                }
            }
        }

        topological_sort[vertex_index] = *current_label;
        *current_label -= 1;
    }

    /// Kosaraju Pseudocode
    /// Input: graph G= (V, E) in adjancency list representation, with V = {1,2,3,...,n}
    /// postcondition: for every v,w ∈ V, scc(v) = scc(w) if and only if v,w are in the same SCC of G
    /// -------------------------------------------------------------------------------------
    /// G_rev := G with all edges reversed
    ///
    /// // first pass of depth-first search
    /// // (computes f(v)'s, the magical ordering)
    /// TopoSort(G_rev)
    ///
    /// // second pass of depth-first search
    /// // (finds SCCs in reverse topological order)
    /// mark all vertices of G as unexplored
    /// numSCC := 0
    /// for each v ∈ V, in increasing order of f(v) do
    ///     if v is unexplored then
    ///         numSCC := numSCC +1
    ///         // assign scc-values
    ///         DFS-SCC(G, v)
    ///
    pub fn kosaraju(&self) -> Vec<usize> {
        // returns a vector where the index is the index of the vertex the element represents the scc id
        let reversed_topo = self.topo_sort(true);
        let mut num_scc: usize = 0;
        let mut visited_set = HashSet::new();
        let vertcies_num = self.vertices.len();
        let mut scc_vec = vec![0; vertcies_num];

        for (_, vertex_index) in reversed_topo {
            if !visited_set.contains(&vertex_index) {
                num_scc += 1;
                self.dfs_scc(vertex_index, &mut scc_vec, num_scc, &mut visited_set);
            }
        }

        scc_vec
    }

    /// DSF-SCC Pseudocode
    /// Input: directed graph G= (V, E) in adjancency list representation and a vertex s ∈ V
    /// postcondition: every vertex reachable from s is marked as 'explored' and has an assigned scc-value
    /// -------------------------------------------------------------------------------------
    /// mark s as explored
    /// scc(s) := numSCC // global variable above
    /// for each edge (s,v) in s's outgoing adjacency list do
    ///     if v is unexplored then
    ///         DFS-SCC (G,v)
    ///
    fn dfs_scc(
        &self,
        vertex_index: usize,
        scc_vec: &mut Vec<usize>,
        num_scc: usize,
        visted_set: &mut HashSet<usize>,
    ) {
        visted_set.insert(vertex_index);
        scc_vec[vertex_index] = num_scc;

        let vertex = &self.vertices[vertex_index];
        for neighbor in &vertex.borrow().outgoing_edges {
            let neighbor_index = neighbor.borrow().get_index();
            if !visted_set.contains(&neighbor_index) {
                self.dfs_scc(neighbor_index, scc_vec, num_scc, visted_set);
            }
        }
    }

    // /// Dijkstra Pseudocode
    // /// Input: directed graph G= (V, E) in adjancency list representation and a vertex s ∈ V,
    // ///        a length le >= 0 for each e ∈ E
    // /// postcondition: for every vertex v, the value len(v)
    // ///                equals the true shortest-path distance dist(s,v)
    // /// -------------------------------------------------------------------------------------
    // /// // Initialization
    // /// X := {s}
    // /// len(s) := 0, len(v) := +∞ for every v != s
    // /// // Main loop
    // /// while there is an edge (v,w) with v ∈ X, w ∉ X do
    // ///     (v*,w*) := such an edge minimizing len(v) + lvw
    // ///     add w* to X
    // ///     len(w*) := len(v*) + lv*w*
    // pub fn dijkstra(&self, s: &VertexRc, num_scc: &mut usize) {
    //     s.borrow_mut().explored = true;
    //     s.borrow_mut().scc = Some(*num_scc);

    //     for v in &s.borrow().outgoing_edges {
    //         if !v.destination.borrow().explored {
    //             self.dfs_topo(&v.destination, num_scc);
    //         }
    //     }
    // }

    // ////////////////// helpers /////////////////////
    // fn has_cycle(&self) -> bool {
    //     for vertex in &self.vertices {
    //         if self.detect_cycle(vertex, &mut vec![false; self.vertices.len()]) {
    //             return true;
    //         }
    //     }
    //     false
    // }

    // fn detect_cycle(&self, vertex: &VertexRc, visited: &mut Vec<bool>) -> bool {
    //     let vertex_index = self.get_vertex_index(vertex);
    //     if visited[vertex_index] {
    //         return true;
    //     }
    //     visited[vertex_index] = true;
    //     for edge in &vertex.borrow().outgoing_edges {
    //         if self.detect_cycle(&edge.destination, visited) {
    //             return true;
    //         }
    //     }
    //     visited[vertex_index] = false;
    //     false
    // }

    pub fn print_graph(&self) {
        println!("Graph:");
        for vertex in &self.vertices {
            let vertex_borrowed = vertex.borrow();
            print!("  Vertex {}:", vertex_borrowed.get_index());
            if vertex_borrowed.outgoing_edges.is_empty() {
                println!(" No outgoing edges");
            } else {
                println!();
                for edge in &vertex_borrowed.outgoing_edges {
                    let edge_value = edge.borrow().get_index();
                    println!("    └──> Vertex {}", edge_value);
                }
            }
        }
    }

    /// Builds a directed graph from a text file with edges in the format "tail head"
    pub fn build_from_file<P: AsRef<Path>>(
        file_path: P,
        reversed: bool,
    ) -> Result<Self, GraphError> {
        let mut graph = DirectedGraph::new();

        // Track maximum vertex index to know how many vertices to add
        let mut max_vertex_index = 0;

        // Open the file in read-only mode (ignoring errors).
        let file = File::open(file_path).map_err(|_| GraphError::FileNotFound)?;
        for line in io::BufReader::new(file).lines() {
            let line = line.map_err(|_| GraphError::VertexNotFound)?;

            // Parse each line as two integers (tail and head)
            let mut parts = line.split_whitespace();
            let mut tail: usize = parts
                .next()
                .ok_or(GraphError::VertexNotFound)?
                .parse()
                .unwrap();
            tail -= 1; // because text files are 1-indexed
            let mut head: usize = parts
                .next()
                .ok_or(GraphError::VertexNotFound)?
                .parse()
                .unwrap();
            head -= 1; // because text files are 1-indexed

            // Update max vertex index to determine the number of vertices needed
            max_vertex_index = max_vertex_index.max(tail).max(head);

            // Ensure all vertices up to the max index are created
            while graph.vertices.len() <= max_vertex_index {
                graph.add_vertex();
            }
            if reversed {
                (tail, head) = (head, tail) // swap head and tail to reverse the graph
            }
            // Add edge to the graph
            graph.add_edge(tail, head)?;
        }

        Ok(graph)
    }
}
impl Default for DirectedGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use std::env::temp_dir;
    use std::io::Write;

    use super::*;

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

    #[test]
    fn test_add_edge_self_loop() {
        let graph = DirectedGraph::with_vertices(1);

        // Try to add a self-loop from vertex 0 to itself
        let result = graph.add_edge(0, 0);
        assert_eq!(result, Err(GraphError::SelfLoop));

        // Ensure no edges were added
        assert_eq!(graph.vertices[0].borrow().outgoing_edges.len(), 0);
        assert_eq!(graph.vertices[0].borrow().incoming_edges.len(), 0);
    }

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
}
