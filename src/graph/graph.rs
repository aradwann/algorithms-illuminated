/// representing a graph using adjancy list which is
/// 1) An array containing the graph nodes
/// 2) An array containing the graph edges
/// 3) For each edge, a pointer to each of its two endpoints
/// 4) for each vertex, a pointer to each of the incident edges

type NodeIndex = usize;

#[derive(Debug)]
struct NodeData {
    edges: Vec<EdgeIndex>,
}

type EdgeIndex = usize;

#[derive(Debug)]
struct UndirectedEdgeData(NodeIndex, NodeIndex);
impl UndirectedEdgeData {
    fn new(node_1: NodeIndex, node_2: NodeIndex) -> Self {
        if node_1 > node_2 {
            Self(node_2, node_1)
        } else {
            Self(node_1, node_2)
        }
    }
}
#[derive(Debug)]
pub struct UndirectedGraph {
    nodes: Vec<NodeData>,
    edges: Vec<UndirectedEdgeData>,
}
impl UndirectedGraph {
    pub fn new() -> Self {
        UndirectedGraph {
            nodes: vec![],
            edges: vec![],
        }
    }
    pub fn add_node(&mut self) -> NodeIndex {
        let index = self.nodes.len();
        self.nodes.push(NodeData { edges: vec![] });
        index
    }
    pub fn add_edge(&mut self, source: NodeIndex, target: NodeIndex) -> EdgeIndex {
        let edge_index = self.edges.len();
        self.edges.push(UndirectedEdgeData::new(source, target));

        let node_data_1 = &mut self.nodes[source];
        node_data_1.edges.push(edge_index);

        let node_data_2 = &mut self.nodes[target];
        node_data_2.edges.push(edge_index);
        edge_index
    }
}
