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
}

type EdgeIndex = usize;

#[derive(Debug)]
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
            cc_value: 0, // 0 means no cc value yet
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

        while stack.len() > 0 {
            let v_index = stack.pop().unwrap();
            let v = &mut self.vertices[v_index];
            if v.explored == false {
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
        let v = &mut self.vertices[vertex_index];
        v.explored = true;

        for edge_index in v.outgoing_edges.clone() {
            let edge = &self.edges[edge_index];
            let next_v_index = edge.1;
            if self.vertices[next_v_index].explored == false {
                println!("vertex index is {:?}", &next_v_index);
                self.dfs_recursive(next_v_index);
            }
        }
    }

    fn mark_all_vertices_unexplored(&mut self) {
        self.vertices.iter_mut().map(|n| n.explored = false);
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
}
