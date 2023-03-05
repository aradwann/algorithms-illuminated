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
type VertexIndex = usize;

#[derive(Debug, Clone)]
struct VertexData {
    outgoing_edges: Vec<EdgeIndex>,
    incoming_edges: Vec<EdgeIndex>,
    value: char,
    explored: bool,
    cc_value: usize,
    topo_order: usize,
    scc: usize,
}

type EdgeIndex = usize;

#[derive(Debug, Clone)]
struct EdgeData(VertexIndex, VertexIndex);
impl EdgeData {
    fn new(tail: VertexIndex, head: VertexIndex) -> Self {
        if tail == head {
            panic!("self-loops aren't allowed atm")
        }
        EdgeData(tail, head)
    }
}

#[derive(Debug)]
pub struct DirectedGraph {
    vertices: Vec<VertexData>,
    edges: Vec<EdgeData>,
}

impl DirectedGraph {
    pub fn new() -> Self {
        DirectedGraph {
            vertices: vec![],
            edges: vec![],
        }
    }

    pub fn add_vertex(&mut self, value: char) {
        self.vertices.push(VertexData {
            outgoing_edges: vec![],
            incoming_edges: vec![],
            value,
            explored: false,
            cc_value: 0,   // 0 means no cc value yet
            topo_order: 0, // means no value yet
            scc: 0,        // means no value yet
        });
    }

    pub fn add_edge(&mut self, tail: VertexIndex, head: VertexIndex) -> EdgeIndex {
        for e in &self.edges {
            if e.0 == tail && e.1 == head {
                panic!("parallel edges aren't allowed atm")
            }
        }
        let edge_index = self.edges.len();
        self.edges.push(EdgeData::new(tail, head));

        let tail = &mut self.vertices[tail];
        tail.outgoing_edges.push(edge_index);

        let head = &mut self.vertices[head];
        head.incoming_edges.push(edge_index);
        edge_index
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
    pub fn dfs_iterative(&mut self, vertex_index: VertexIndex) {
        self.mark_all_vertices_unexplored();
        let mut stack = vec![];
        stack.push(vertex_index);

        while !stack.is_empty() {
            let v_index = stack.pop().unwrap();
            let v = &mut self.vertices[v_index];
            if !v.explored {
                v.explored = true;
                for edge_index in &v.outgoing_edges {
                    let edge = &self.edges[*edge_index];
                    let next_v_index = edge.1;
                    stack.push(next_v_index);
                }
            }
            println!("stack is {:?}", &stack);
        }
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
    pub fn dfs_recursive(&mut self, vertex_index: VertexIndex) {
        // vertices must be marked unexplored before calling this function
        let v = &mut self.vertices[vertex_index];
        v.explored = true;

        for edge_index in v.outgoing_edges.clone() {
            let edge = &self.edges[edge_index];
            let next_v_index = edge.1;
            if !self.vertices[next_v_index].explored {
                println!("vertex index is {:?}", &next_v_index);
                self.dfs_recursive(next_v_index);
            }
        }
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
    pub fn topo_sort(&mut self) {
        self.mark_all_vertices_unexplored();

        let mut current_label = self.vertices.len();

        for vertex_index in 0..self.vertices.len() {
            if !self.vertices[vertex_index].explored {
                self.dfs_topo(vertex_index, &mut current_label);
            }
        }
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
    fn dfs_topo(&mut self, vertex_index: VertexIndex, current_label: &mut usize) {
        // vertices must be marked unexplored before calling this function
        let v = &mut self.vertices[vertex_index];
        v.explored = true;

        for edge_index in v.outgoing_edges.clone() {
            let edge = &self.edges[edge_index];
            let next_v_index = edge.1;
            if !self.vertices[next_v_index].explored {
                self.dfs_topo(next_v_index, current_label);
            }
        }
        let v = &mut self.vertices[vertex_index];
        v.topo_order = *current_label;
        *current_label -= 1;
        println!(
            "vertex index is {} and its topo order is {} ",
            v.value, v.topo_order
        );
    }

    pub fn topo_sort_reversed(&mut self) {
        self.mark_all_vertices_unexplored();

        let mut current_label = self.vertices.len();

        for vertex_index in 0..self.vertices.len() {
            if !self.vertices[vertex_index].explored {
                self.dfs_topo_reversed(vertex_index, &mut current_label);
            }
        }
    }

    fn dfs_topo_reversed(&mut self, vertex_index: VertexIndex, current_label: &mut usize) {
        // vertices must be marked unexplored before calling this function
        let v = &mut self.vertices[vertex_index];
        v.explored = true;

        for edge_index in v.incoming_edges.clone() {
            let edge = &self.edges[edge_index];
            let next_v_index = edge.1;
            if !self.vertices[next_v_index].explored {
                self.dfs_topo(next_v_index, current_label);
            }
        }
        let v = &mut self.vertices[vertex_index];
        v.topo_order = *current_label;
        *current_label -= 1;
        println!(
            "vertex index is {} and its topo order is {} ",
            v.value, v.topo_order
        );
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
    pub fn kosaraju(&mut self) -> usize {
        self.mark_all_vertices_unexplored();

        // first dfs pass
        // reversed graph
        // let mut g_reversed = DirectedGraph::new();
        // g_reversed.vertices = self.vertices.clone();
        // g_reversed.edges = self
        //     .edges
        //     .clone()
        //     .iter_mut()
        //     .map(|e| EdgeData::new(e.1, e.0))
        //     .collect();
        // g_reversed.topo_sort();

        self.topo_sort_reversed();

        // second dfs pass

        self.mark_all_vertices_unexplored();
        let mut num_scc: usize = 0;

        for vertex_index in 0..self.vertices.len() {
            if !self.vertices[vertex_index].explored {
                num_scc += 1;
                self.dfs_scc(vertex_index, &mut num_scc);
            }
        }
        num_scc
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
    fn dfs_scc(&mut self, vertex_index: VertexIndex, num_scc: &mut usize) {
        let v = &mut self.vertices[vertex_index];
        v.explored = true;
        v.scc = *num_scc;

        for edge_index in v.outgoing_edges.clone() {
            let edge = &self.edges[edge_index];
            let next_v_index = edge.1;
            if !self.vertices[next_v_index].explored {
                self.dfs_scc(next_v_index, num_scc);
            }
        }
    }

    ////////////////// helpers /////////////////////
    fn mark_all_vertices_unexplored(&mut self) {
        self.vertices.iter_mut().map(|n| n.explored = false);
    }

    fn is_acyclic(&self) -> bool {
        // for v in &self.vertices {
        //     if v.incoming_edges.len() == 0 {
        //         return true;
        //     }
        // }
        // return false;
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "self-loops aren't allowed atm")]
    fn test_create_self_loop() {
        EdgeData::new(2, 2);
    }

    #[test]
    #[should_panic(expected = "parallel edges aren't allowed atm")]
    fn test_add_parallel_edge() {
        let mut graph = DirectedGraph::new();

        graph.add_vertex('s');
        graph.add_vertex('v');

        graph.add_edge(0, 1);
        graph.add_edge(0, 1);
    }

    #[test]
    fn test_create_directed_graph() {
        let mut graph = DirectedGraph::new();

        graph.add_vertex('s');
        graph.add_vertex('v');
        graph.add_vertex('w');
        graph.add_vertex('t');

        graph.add_edge(0, 1);
        graph.add_edge(0, 2);
        graph.add_edge(1, 3);
        graph.add_edge(2, 3);

        // assert graph has 4 vertices
        assert_eq!(graph.edges.len(), 4);
        // assert graph has 4 edges
        assert_eq!(graph.vertices.len(), 4);
        // assert first vertex is a source vertex as initialized
        assert_eq!(graph.vertices[0].incoming_edges.len(), 0);
    }

    #[test]
    fn test_topo_sort() {
        let mut graph = DirectedGraph::new();

        graph.add_vertex('s');
        graph.add_vertex('v');
        graph.add_vertex('w');
        graph.add_vertex('t');

        graph.add_edge(0, 1);
        graph.add_edge(0, 2);
        graph.add_edge(1, 3);
        graph.add_edge(2, 3);

        graph.topo_sort();

        assert_eq!(graph.vertices[0].topo_order, 1);
        assert_eq!(graph.vertices[1].topo_order, 3);
        assert_eq!(graph.vertices[2].topo_order, 2);
        assert_eq!(graph.vertices[3].topo_order, 4);
    }
}

impl Default for DirectedGraph {
    fn default() -> Self {
        Self::new()
    }
}
