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
struct Vertex {
    outgoing_edges: RefCell<Vec<Rc<Vertex>>>,
    incoming_edges: RefCell<Vec<Weak<Vertex>>>,
    value: Option<char>,
    explored: bool,
    cc_value: Option<usize>,
    topo_order: Option<usize>,
}

impl Vertex {
    fn new() -> Self {
        Vertex {
            outgoing_edges: RefCell::new(vec![]),
            incoming_edges: RefCell::new(vec![]),
            value: None,
            explored: false,
            cc_value: None,
            topo_order: None,
        }
    }
}

#[derive(Debug)]
pub struct DirectedGraphRc {
    vertices: Vec<Rc<Vertex>>,
}

impl DirectedGraphRc {
    pub fn new() -> Self {
        DirectedGraphRc { vertices: vec![] }
    }

    pub fn add_vertex(&mut self) {
        let new_vertex = Rc::new(Vertex::new());
        self.vertices.push(new_vertex);
    }

    pub fn add_edge(&mut self, tail_index: usize, head_index: usize) {
        let tail = &self.vertices[tail_index];
        let head = &self.vertices[head_index];
        tail.outgoing_edges.borrow_mut().push(Rc::clone(&head));
        head.incoming_edges.borrow_mut().push(Rc::downgrade(&tail));
    }
}
