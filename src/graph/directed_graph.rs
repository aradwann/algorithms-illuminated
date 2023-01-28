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
        EdgeData(tail, head)
    }
}


#[derive(Debug)]
pub struct DirectedGraph {
    vertices: Vec<VertexData>,
    edges: Vec<EdgeData>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_directed_graoh() {
        todo!()
    }
}
