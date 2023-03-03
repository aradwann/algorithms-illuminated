use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

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

#[derive(Debug)]
pub struct Vertex {
    outgoing_edges: Vec<Rc<RefCell<Vertex>>>,
    incoming_edges: Vec<Weak<RefCell<Vertex>>>,
    value: Option<char>,
    explored: bool,
    cc_value: Option<usize>,
    topo_order: Option<usize>,
}

impl Vertex {
    fn new() -> Self {
        Vertex {
            outgoing_edges: vec![],
            incoming_edges: vec![],
            value: None,
            explored: false,
            cc_value: None,
            topo_order: None,
        }
    }
}

#[derive(Debug)]
pub struct DirectedGraphRc {
    pub vertices: Vec<Rc<RefCell<Vertex>>>,
}

impl DirectedGraphRc {
    pub fn new() -> Self {
        DirectedGraphRc { vertices: vec![] }
    }

    pub fn add_vertex(&mut self) {
        let new_vertex = Rc::new(RefCell::new(Vertex::new()));
        self.vertices.push(new_vertex);
    }

    pub fn add_edge(&mut self, tail_index: usize, head_index: usize) {
        let tail = &self.vertices[tail_index];
        let head = &self.vertices[head_index];
        tail.borrow_mut().outgoing_edges.push(Rc::clone(head));
        head.borrow_mut().incoming_edges.push(Rc::downgrade(tail));
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
    pub fn dfs_recursive(&mut self, s: &Rc<RefCell<Vertex>>) {
        // vertices must be marked unexplored before calling this function
        // let s = self.vertices[vertex_index];
        s.borrow_mut().explored = true;

        for v in &s.borrow().outgoing_edges {
            if !v.borrow().explored {
                self.dfs_recursive(v);
            }
        }
    }

    ////////////////// helpers /////////////////////
    fn mark_all_vertices_unexplored(&mut self) {
        self.vertices
            .iter_mut()
            .map(|n| n.borrow_mut().explored = false);
    }
}

impl Default for DirectedGraphRc {
    fn default() -> Self {
        Self::new()
    }
}
