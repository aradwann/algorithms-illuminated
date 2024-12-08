use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fs::File,
    io::{self, BufRead},
    path::Path,
    rc::{Rc, Weak},
};

use super::{GraphError, VertexIndex};

// representing a graph using an adjacency list which is
// 1) An array containing the graph vertices
// 2) An array containing the graph edges
// 3) For each edge, a pointer to each of its two endpoints
// 4) for each vertex, a pointer to each of the incident edges
//
// for directed graph:
// each edge keeps track of which endpoint is tail and which endpoint is head
// each vertex maintains two arrays of pointers, one for the outgoing edges and one for the incoming edges

type VertexRc = Rc<RefCell<Vertex>>;
type VertexWeak = Weak<RefCell<Vertex>>;

/// vec of topological order of the vertices
/// where the index in the vector reporesent the vertex index
/// and the value represent its topological order
type TopologicalSort = Vec<usize>;

#[derive(Debug)]
pub struct Vertex {
    index: VertexIndex,
    pub outgoing_edges: Vec<VertexRc>,
    pub incoming_edges: Vec<VertexWeak>, // Weak to avoid cycles
}

impl Vertex {
    fn new(index: VertexIndex) -> Self {
        Vertex {
            index,
            outgoing_edges: vec![],
            incoming_edges: vec![],
        }
    }
    pub fn get_index(&self) -> VertexIndex {
        self.index
    }

    // this should be used whenver it is required to change the vertex index in the graph
    fn _set_index(&mut self, index: VertexIndex) {
        self.index = index;
    }
}

#[derive(Debug)]
pub struct DirectedGraph {
    pub vertices: Vec<VertexRc>,
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
        // Comment out the check to solve the scc.text
        // Check for self-loop
        // if tail_index == head_index {
        //     return Err(GraphError::SelfLoop);
        // }

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
    /// NOTE: if used for big graph will trigger stack overflow
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
        visited: &mut HashSet<VertexIndex>,
        order: &mut Vec<VertexIndex>,
    ) -> Result<Vec<VertexIndex>, GraphError> {
        // Ensure the starting vertex exists
        let vertex = self.vertices.get(start).ok_or(GraphError::VertexNotFound)?;

        // Mark the current vertex as visited
        visited.insert(start);

        // Recurse for unvisited neighbors
        for neighbor in &vertex.borrow().outgoing_edges {
            let neighbor_index = neighbor.borrow().get_index();
            if !visited.contains(&neighbor_index) {
                self.dfs_recursive_subroutine(neighbor_index, visited, order)?;
            }
        }

        // Record the vertex in the DFS order
        order.push(start);
        Ok(order.to_vec())
    }
    pub fn dfs_iterative(&self, start: VertexIndex) -> Result<Vec<VertexIndex>, GraphError> {
        let mut visited = HashSet::new();
        let mut stack = Vec::new();
        let mut dfs_order = Vec::new();
        stack.push(start);

        while let Some(current) = stack.pop() {
            if !visited.contains(&current) {
                visited.insert(current);
                dfs_order.push(current);
                let vertex = self
                    .vertices
                    .get(current)
                    .ok_or(GraphError::VertexNotFound)?;

                for neighbor in &vertex.borrow().outgoing_edges {
                    let neighbor_index = neighbor.borrow().get_index();
                    stack.push(neighbor_index);
                }
            }
        }

        Ok(dfs_order)
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
    pub fn topo_sort(&self, reversed: bool) -> Vec<(usize, VertexIndex)> {
        let vertices = &self.vertices;
        let vertcies_num = vertices.len();
        let mut current_label = vertcies_num;
        let mut visited_set = HashSet::new();
        let mut topological_sort = vec![0; vertcies_num];
        for v in vertices {
            let vertex_index = &v.borrow().get_index();
            if !visited_set.contains(vertex_index) {
                self._dfs_topo_iterative(
                    *vertex_index,
                    &mut visited_set,
                    &mut topological_sort,
                    &mut current_label,
                    reversed,
                );
            }
        }

        let mut sorted_vertices: Vec<(usize, VertexIndex)> = topological_sort
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
    fn _dfs_topo(
        &self,
        vertex_index: VertexIndex,
        visited: &mut HashSet<VertexIndex>,
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
                    self._dfs_topo(
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
                        self._dfs_topo(
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

    // alternate implmentation to avoid stack overflow
    fn _dfs_topo_iterative(
        &self,
        vertex_index: VertexIndex,
        visited: &mut HashSet<VertexIndex>,
        topological_sort: &mut TopologicalSort,
        current_label: &mut usize,
        reversed: bool,
    ) {
        let mut stack: Vec<(VertexIndex, bool)> = Vec::new();
        stack.push((vertex_index, false));

        while let Some((current_vertex_index, processed)) = stack.pop() {
            if processed {
                // Post-processing step
                topological_sort[current_vertex_index] = *current_label;
                *current_label -= 1;
                continue;
            }

            if visited.contains(&current_vertex_index) {
                continue;
            }

            // Mark the current vertex as visited
            visited.insert(current_vertex_index);

            // Push the current vertex back onto the stack for post-processing
            stack.push((current_vertex_index, true));

            let vertex = self.vertices.get(current_vertex_index).unwrap();

            if !reversed {
                // Push unvisited neighbors (outgoing edges) onto the stack
                for neighbor in &vertex.borrow().outgoing_edges {
                    let neighbor_index = neighbor.borrow().get_index();
                    if !visited.contains(&neighbor_index) {
                        stack.push((neighbor_index, false));
                    }
                }
            } else {
                // Push unvisited incoming vertices onto the stack
                for neighbor_weak in &vertex.borrow().incoming_edges {
                    if let Some(neighbor_rc) = neighbor_weak.upgrade() {
                        let neighbor_index = neighbor_rc.borrow().get_index();
                        if !visited.contains(&neighbor_index) {
                            stack.push((neighbor_index, false));
                        }
                    }
                }
            }
        }
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
                self._dfs_scc_iterative(vertex_index, &mut scc_vec, num_scc, &mut visited_set);
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
    fn _dfs_scc(
        &self,
        vertex_index: VertexIndex,
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
                self._dfs_scc(neighbor_index, scc_vec, num_scc, visted_set);
            }
        }
    }

    fn _dfs_scc_iterative(
        &self,
        vertex_index: VertexIndex,
        scc_vec: &mut [usize],
        num_scc: usize,
        visited: &mut HashSet<usize>,
    ) {
        let mut stack = Vec::new();
        stack.push(vertex_index);

        while let Some(current) = stack.pop() {
            if !visited.contains(&current) {
                visited.insert(current);
                scc_vec[current] = num_scc;

                let vertex = self.vertices.get(current).unwrap();

                for neighbor in &vertex.borrow().outgoing_edges {
                    let neighbor_index = neighbor.borrow().get_index();
                    stack.push(neighbor_index);
                }
            }
        }
    }

    /// get the top five strongly connected componenets accroding to their sizes
    /// returns vector of tuples such that every tuple is (scc_id, scc_size)
    pub fn get_top_five_sccs(&self) -> Vec<(usize, usize)> {
        let vec = self.kosaraju();
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
    // pub fn dijkstra(&self, s: VertexIndex, ) {
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
mod tests {}
