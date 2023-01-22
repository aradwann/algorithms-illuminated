use std::collections::VecDeque;

/// representing a graph using an adjacency list which is
/// 1) An array containing the graph nodes
/// 2) An array containing the graph edges
/// 3) For each edge, a pointer to each of its two endpoints
/// 4) for each vertex, a pointer to each of the incident edges

type NodeIndex = usize;

#[derive(Debug, Clone)]
struct NodeData {
    edges: Vec<EdgeIndex>,
    value: char,
    explored: bool,
}

type EdgeIndex = usize;

#[derive(Debug)]
struct UndirectedEdgeData(NodeIndex, NodeIndex);
impl UndirectedEdgeData {
    fn new(node_1: NodeIndex, node_2: NodeIndex) -> Self {
        // order of nodes does not matter as it is undirected
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
    pub fn add_node(&mut self, value: char) -> NodeIndex {
        let index = self.nodes.len();
        self.nodes.push(NodeData {
            edges: vec![],
            value,
            explored: false,
        });
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

    /// Pseudocode
    /// Input: graph G=(V,E) in adjancency list representation and a vertex s ∈ V
    /// postcondition: a vertex is reachabele from s if and only f it is marked as explored
    /// -----------------------------------------------------------------------------------
    /// mark s as explored, all other vertices as unexplored
    /// Q := a queue data structure, intialized with s
    /// while Q is not empty do
    ///     remove the vertex from the front of the Q, call it v
    ///     for each edge (v,w) in v's adjacency list do
    ///         if w is unexplored then
    ///         mark w as explored
    ///         add w to the end of Q
    pub fn bfs(&mut self, _value: char) {
        self.mark_all_nodes_unexplored();
        let mut queue = VecDeque::new();
        queue.push_back(self.edges[0].0); // push the first node data into the queue
        while queue.len() != 0 {
            let node_index = queue.pop_front().unwrap(); // the index of the node
            let node_data = self.nodes[node_index].clone();
            for edge_index in node_data.edges {
                let UndirectedEdgeData(_, node_index_2) = self.edges[edge_index];
                let node_2 = &mut self.nodes[node_index_2];
                if node_2.explored == false {
                    node_2.explored = true;
                    println!("exploring Node {:#?}", &node_2);
                    queue.push_back(node_index_2);
                }
            }
        }
    }
    fn mark_all_nodes_unexplored(&mut self) {
        self.nodes.iter_mut().map(|n| n.explored = false);
    }
}
