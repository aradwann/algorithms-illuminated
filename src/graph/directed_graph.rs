use std::{
    cell::RefCell,
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

///  holds the reference to the destination vertex (Rc) and the length of the edge
// #[derive(Debug)]
// struct OutgoingEdge {
//     destination: VertexRc,
//     length: Option<usize>,
// }

///  holds the reference to the source vertex (Weak) and the length of the edge
// #[derive(Debug)]
// struct IncomingEdge {
//     source: VertexWeak,
//     length: Option<usize>,
// }

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
    fn set_index(&mut self, index: VertexIndex) {
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
    pub fn build_from_file<P: AsRef<Path>>(file_path: P) -> Result<Self, GraphError> {
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

            // Add edge to the graph
            graph.add_edge(tail, head)?;
        }

        Ok(graph)
    }

    // /// DFS (recursive version) Pseudocode
    // /// Input: graph G= (V, E) in adjancency list representation, and a vertex s ∈ V
    // /// postcondition: a vertex is reachabele from s if and only if it is marked as "explored".
    // /// -------------------------------------------------------------------------------------
    // /// // all vertices unexplored before outer call
    // /// mark s as explored
    // /// for each edge (s,v) in s's adjacency list do
    // ///     if v is unexplored then
    // ///         dfs(G, v)
    // pub fn dfs_recursive(&self, s: &VertexRc) {
    //     // vertices must be marked unexplored before calling this function
    //     println!("exploring {:#?}", s.borrow().value);
    //     s.borrow_mut().explored = true;

    //     for edge in &s.borrow().outgoing_edges {
    //         if !edge.destination.borrow().explored {
    //             self.dfs_recursive(&edge.destination);
    //         }
    //     }
    // }

    // /// TopoSort Pseudocode
    // /// Input: directed acyclic graph G= (V, E) in adjancency list representation
    // /// postcondition: the f-values of vertices constitute a topological ordering of G.
    // /// -------------------------------------------------------------------------------------
    // /// mark all vertices as unexplored
    // /// curLabel := |V| // keeps track of ordering
    // /// for every v ∈ V do
    // ///     if v is unexplored then // in a prior DFS
    // ///         DFS-Topo(G, v)
    // pub fn topo_sort(&self) {
    //     // self.mark_all_vertices_unexplored();
    //     let vertices = &self.vertices;
    //     let mut current_label = vertices.len();

    //     for v in vertices {
    //         if !v.borrow().explored {
    //             self.dfs_topo(v, &mut current_label);
    //         }
    //     }
    // }

    // fn topo_sort_reversed(&mut self) {
    //     let vertices = &self.vertices;
    //     let mut current_label = vertices.len();

    //     for v in vertices {
    //         if !v.borrow().explored {
    //             self.dfs_topo_reversed(v, &mut current_label);
    //         }
    //     }

    //     let mut sorted_vertices = vec![Rc::new(RefCell::new(Vertex::new(' '))); vertices.len()];
    //     for v in vertices {
    //         sorted_vertices[v.borrow().topo_order.unwrap() - 1] = Rc::clone(v);
    //     }
    //     self.vertices = sorted_vertices;
    // }

    // /// DFS-Topo Pseudocode
    // /// Input: graph G= (V, E) in adjancency list representation and a vertex s ∈ V
    // /// postcondition: every vertex reachable from s is marked as 'explored' and has an assigned f-value
    // /// -------------------------------------------------------------------------------------
    // /// mark s as explored
    // ///
    // /// for each edge (s,v) in s's outgoing adjacency list do
    // ///     if v is unexplored then
    // ///         DFS-Topo(G,v)
    // /// f(s) := curLabel    // s's position in ordering
    // /// curLabel := curLabel -1 // work right-to-left
    // fn dfs_topo(&self, vertex: &VertexRc, current_label: &mut usize) {
    //     vertex.borrow_mut().explored = true;

    //     for edge in &vertex.borrow().outgoing_edges {
    //         let destination = &edge.destination;
    //         if !destination.borrow().explored {
    //             self.dfs_topo(destination, current_label);
    //         }
    //     }

    //     vertex.borrow_mut().topo_order = Some(*current_label);
    //     *current_label -= 1;
    // }

    // fn dfs_topo_reversed(&self, vertex: &VertexRc, current_label: &mut usize) {
    //     vertex.borrow_mut().explored = true;

    //     for incoming_edge in &vertex.borrow().incoming_edges {
    //         if let Some(incoming_edge_tail) = incoming_edge.source.upgrade() {
    //             if !incoming_edge_tail.borrow().explored {
    //                 self.dfs_topo_reversed(&incoming_edge_tail, current_label);
    //             }
    //         }
    //     }

    //     vertex.borrow_mut().topo_order = Some(*current_label);
    //     *current_label -= 1;
    //     println!(
    //         "vertex index is {} and its topo order is {}",
    //         vertex.borrow().value,
    //         vertex.borrow().topo_order.unwrap()
    //     );
    // }

    // /// Kosaraju Pseudocode
    // /// Input: graph G= (V, E) in adjancency list representation, with V = {1,2,3,...,n}
    // /// postcondition: for every v,w ∈ V, scc(v) = scc(w) if and only if v,w are in the same SCC of G
    // /// -------------------------------------------------------------------------------------
    // /// G_rev := G with all edges reversed
    // ///
    // /// // first pass of depth-first search
    // /// // (computes f(v)'s, the magical ordering)
    // /// TopoSort(G_rev)
    // ///
    // /// // second pass of depth-first search
    // /// // (finds SCCs in reverse topological order)
    // /// mark all vertices of G as unexplored
    // /// numSCC := 0
    // /// for each v ∈ V, in increasing order of f(v) do
    // ///     if v is unexplored then
    // ///         numSCC := numSCC +1
    // ///         // assign scc-values
    // ///         DFS-SCC(G, v)
    // ///
    // pub fn kosaraju(&mut self) -> usize {
    //     self.mark_all_vertices_unexplored();
    //     self.topo_sort_reversed();
    //     self.mark_all_vertices_unexplored();
    //     let mut num_scc: usize = 0;

    //     for v in self.vertices() {
    //         if !v.borrow().explored {
    //             num_scc += 1;
    //             self.dfs_scc(v, &mut num_scc);
    //         }
    //     }

    //     num_scc
    // }

    // /// DSF-SCC Pseudocode
    // /// Input: directed graph G= (V, E) in adjancency list representation and a vertex s ∈ V
    // /// postcondition: every vertex reachable from s is marked as 'explored' and has an assigned scc-value
    // /// -------------------------------------------------------------------------------------
    // /// mark s as explored
    // /// scc(s) := numSCC // global variable above
    // /// for each edge (s,v) in s's outgoing adjacency list do
    // ///     if v is unexplored then
    // ///         DFS-SCC (G,v)
    // ///
    // fn dfs_scc(&self, vertex: &VertexRc, num_scc: &mut usize) {
    //     vertex.borrow_mut().explored = true;
    //     vertex.borrow_mut().scc = Some(*num_scc);

    //     for outgoing_edge in &vertex.borrow().outgoing_edges {
    //         if !outgoing_edge.destination.borrow().explored {
    //             self.dfs_scc(&outgoing_edge.destination, num_scc);
    //         }
    //     }
    // }

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
    // fn mark_all_vertices_unexplored(&self) {
    //     self.vertices
    //         .iter()
    //         .for_each(|v| v.borrow_mut().explored = false);
    // }

    // fn vertices(&self) -> &[VertexRc] {
    //     self.vertices.as_ref()
    // }

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

    // fn get_vertex_index(&self, vertex: &VertexRc) -> usize {
    //     self.vertices
    //         .iter()
    //         .position(|v| Rc::ptr_eq(v, vertex))
    //         .unwrap()
    // }
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
        let graph = DirectedGraph::build_from_file(&path).expect("Failed to build graph");

        // Check vertices
        assert_eq!(graph.vertices.len(), 5); // Max index is 4, so 5 vertices (0 through 4)

        // Check edges for correctness
        assert_eq!(graph.vertices[1].borrow().outgoing_edges.len(), 1);
        assert_eq!(graph.vertices[2].borrow().outgoing_edges.len(), 2);
        assert_eq!(graph.vertices[3].borrow().outgoing_edges.len(), 1);
        assert_eq!(graph.vertices[4].borrow().outgoing_edges.len(), 1);

        // Validate specific edges
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
        assert!(graph.vertices[2]
            .borrow()
            .outgoing_edges
            .iter()
            .any(|v| v.borrow().get_index() == 4));
        assert!(graph.vertices[3]
            .borrow()
            .outgoing_edges
            .iter()
            .any(|v| v.borrow().get_index() == 4));
        assert!(graph.vertices[4]
            .borrow()
            .outgoing_edges
            .iter()
            .any(|v| v.borrow().get_index() == 1));

        // Clean up: Remove the temporary file after test
        std::fs::remove_file(&path).expect("Failed to delete temporary file");
    }
}
