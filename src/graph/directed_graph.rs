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
