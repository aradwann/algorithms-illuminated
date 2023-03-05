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
    value: char,
    explored: bool,
    // cc_value: Option<usize>,
    topo_order: Option<usize>,
}

impl Vertex {
    fn new(value: char) -> Self {
        Vertex {
            outgoing_edges: vec![],
            incoming_edges: vec![],
            value,
            explored: false,
            // cc_value: None,
            topo_order: None,
        }
    }
}

#[derive(Debug)]
pub struct DirectedGraphRc {
    vertices: Vec<Rc<RefCell<Vertex>>>,
}

impl DirectedGraphRc {
    pub fn new() -> Self {
        DirectedGraphRc { vertices: vec![] }
    }

    pub fn add_vertex(&mut self, value: char) {
        let new_vertex = Rc::new(RefCell::new(Vertex::new(value)));
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
    pub fn dfs_recursive(&self, s: &Rc<RefCell<Vertex>>) {
        // vertices must be marked unexplored before calling this function
        println!("exploring {:#?}", s.borrow().value);
        s.borrow_mut().explored = true;

        for v in &s.borrow().outgoing_edges {
            if !v.borrow().explored {
                self.dfs_recursive(v);
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
        // self.mark_all_vertices_unexplored();
        let vertices = &self.vertices;
        let mut current_label = vertices.len();

        for v in vertices {
            if !v.borrow().explored {
                self.dfs_topo(v, &mut current_label);
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
    fn dfs_topo(&self, s: &Rc<RefCell<Vertex>>, current_label: &mut usize) {
        // vertices must be marked unexplored before calling this function

        s.borrow_mut().explored = true;

        for v in &s.borrow().outgoing_edges {
            if !v.borrow().explored {
                self.dfs_topo(v, current_label);
            }
        }

        s.borrow_mut().topo_order = Some(*current_label);
        *current_label -= 1;
        println!(
            "vertex index is {} and its topo order is {} ",
            s.borrow().value,
            s.borrow().topo_order.unwrap()
        );
    }

    ////////////////// helpers /////////////////////
    fn mark_all_vertices_unexplored(&mut self) {
        self.vertices
            .iter()
            .map(|n| n.borrow_mut().explored = false);
    }

    pub fn vertices(&self) -> &[Rc<RefCell<Vertex>>] {
        self.vertices.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // #[should_panic(expected = "self-loops aren't allowed atm")]
    // fn test_create_self_loop() {
    //     EdgeData::new(2, 2);
    // }

    // #[test]
    // #[should_panic(expected = "parallel edges aren't allowed atm")]
    // fn test_add_parallel_edge() {
    //     let mut graph = DirectedGraph::new();

    //     graph.add_vertex('s');
    //     graph.add_vertex('v');

    //     graph.add_edge(0, 1);
    //     graph.add_edge(0, 1);
    // }

    #[test]
    fn test_create_directed_graph() {
        let mut graph = DirectedGraphRc::new();

        graph.add_vertex('s');
        graph.add_vertex('v');
        graph.add_vertex('w');
        graph.add_vertex('t');

        graph.add_edge(0, 1);
        graph.add_edge(0, 2);
        graph.add_edge(1, 3);
        graph.add_edge(2, 3);

        // assert graph has 4 vertices
        assert_eq!(graph.vertices().len(), 4);
        // assert first vertex is a source vertex as initialized
        assert_eq!(graph.vertices[0].borrow().incoming_edges.len(), 0);
        assert_eq!(graph.vertices[0].borrow().outgoing_edges.len(), 2);
        // assert last vertex is a sink vertex as initialized
        assert_eq!(graph.vertices[3].borrow().incoming_edges.len(), 2);
        assert_eq!(graph.vertices[3].borrow().outgoing_edges.len(), 0);
    }

    #[test]
    fn test_dfs_topo() {
        let mut graph = DirectedGraphRc::new();

        graph.add_vertex('s');
        graph.add_vertex('v');
        graph.add_vertex('w');
        graph.add_vertex('t');

        graph.add_edge(0, 1);
        graph.add_edge(0, 2);
        graph.add_edge(1, 3);
        graph.add_edge(2, 3);

        let vertices = graph.vertices();
        let mut current_label = vertices.len();
        let s = &vertices[0];
        graph.dfs_topo(s, &mut current_label);

        assert_eq!(current_label, 0);
    }

    #[test]
    fn test_topo_sort() {
        let mut graph = DirectedGraphRc::new();

        graph.add_vertex('s');
        graph.add_vertex('v');
        graph.add_vertex('w');
        graph.add_vertex('t');

        graph.add_edge(0, 1);
        graph.add_edge(0, 2);
        graph.add_edge(1, 3);
        graph.add_edge(2, 3);

        graph.topo_sort();

        assert_eq!(graph.vertices()[0].borrow().topo_order, Some(1));
        assert_eq!(graph.vertices()[1].borrow().topo_order, Some(3));
        assert_eq!(graph.vertices()[2].borrow().topo_order, Some(2));
        assert_eq!(graph.vertices()[3].borrow().topo_order, Some(4));
    }
}

impl Default for DirectedGraphRc {
    fn default() -> Self {
        Self::new()
    }
}
