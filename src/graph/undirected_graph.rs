use std::collections::{HashSet, VecDeque};

/// representing a graph using an adjacency list which is
/// 1) An array containing the graph vertices
/// 2) An array containing the graph edges
/// 3) For each edge, a pointer to each of its two endpoints
/// 4) for each vertex, a pointer to each of the incident edges

type VertexIndex = usize;

/// Represents data associated with each vertex
#[derive(Debug, Clone)]
struct VertexData {
    neighbors: HashSet<VertexIndex>,
    _value: char,
    cc_value: Option<usize>,
}
impl VertexData {
    fn new(value: char) -> Self {
        VertexData {
            neighbors: HashSet::new(),
            _value: value,
            cc_value: None,
        }
    }
}

#[derive(Debug)]
pub struct UndirectedGraph {
    vertices: Vec<VertexData>,
}

impl UndirectedGraph {
    pub fn new() -> Self {
        UndirectedGraph { vertices: vec![] }
    }
    pub fn add_vertex(&mut self, value: char) -> VertexIndex {
        let index = self.vertices.len();
        self.vertices.push(VertexData::new(value));
        index
    }
    pub fn add_edge(&mut self, v1: VertexIndex, v2: VertexIndex) -> Result<(), &str> {
        if v1 == v2 {
            return Err("Self-loops are not allowed");
        }
        if self.vertices[v1].neighbors.contains(&v2) {
            return Err("Parallel edges are not allowed");
        }

        self.vertices[v1].neighbors.insert(v2);
        self.vertices[v2].neighbors.insert(v1);
        Ok(())
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
    pub fn bfs(&mut self, start_vertex: VertexIndex) {
        self.clear_exploration();

        let mut queue = VecDeque::new();
        queue.push_back(start_vertex);
        self.vertices[start_vertex].cc_value = Some(1);

        while let Some(v_index) = queue.pop_front() {
            // Clone neighbors to avoid borrowing issues
            let neighbors = self.vertices[v_index].neighbors.clone();
            for neighbor_index in neighbors {
                if self.vertices[neighbor_index].cc_value.is_none() {
                    self.vertices[neighbor_index].cc_value = Some(1);
                    println!("Exploring Vertex {:?}", self.vertices[neighbor_index]);
                    queue.push_back(neighbor_index);
                }
            }
        }
    }

    /// Pseudocode
    /// Input: undirected graph G=(V,E) in adjancency list representation with V = {1,2,3,4,...,n}
    /// postcondition: for every u, v ∈ V, cc(u) = cc(v) if and only if u, v are in the same connected graph
    /// -----------------------------------------------------------------------------------
    /// mark s as explored, all other vertices as unexplored
    /// numCC := 0
    /// for i := 1 to n do
    ///     if i is unexplored then
    ///         numCC := numCC + 1
    ///         // call BFS starting at i (lines 2-8)
    ///         Q := a queue data structure, intialized with i
    ///         while Q is not empty do
    ///             remove the vertex from the front of the Q, call it v
    ///             cc(v) := numCC
    ///             for each edge (v,w) in v's adjacency list do
    ///                 if w is unexplored then
    ///                 mark w as explored
    ///                 add w to the end of Q
    pub fn ucc(&mut self) {
        self.clear_exploration();
        let mut component_count = 0;

        for i in 0..self.vertices.len() {
            if self.vertices[i].cc_value.is_none() {
                component_count += 1;
                let mut queue = VecDeque::new();
                queue.push_back(i);
                self.vertices[i].cc_value = Some(component_count);

                while let Some(v_index) = queue.pop_front() {
                    // Clone neighbors to avoid borrowing issues
                    let neighbors = self.vertices[v_index].neighbors.clone();
                    for neighbor_index in neighbors {
                        if self.vertices[neighbor_index].cc_value.is_none() {
                            self.vertices[neighbor_index].cc_value = Some(component_count);
                            println!("Exploring vertex {:?}", self.vertices[neighbor_index]);
                            queue.push_back(neighbor_index);
                        }
                    }
                }
            }
        }
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
    pub fn dfs_iterative() {
        unimplemented!()
    }

    fn clear_exploration(&mut self) {
        self.vertices.iter_mut().for_each(|v| v.cc_value = None);
    }
}

impl Default for UndirectedGraph {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_self_loops() {
        let mut graph = UndirectedGraph::new();
        let v = graph.add_vertex('A');
        assert!(graph.add_edge(v, v).is_err());
    }

    #[test]
    fn test_no_parallel_edges() {
        let mut graph = UndirectedGraph::new();
        let v1 = graph.add_vertex('A');
        let v2 = graph.add_vertex('B');
        assert!(graph.add_edge(v1, v2).is_ok());
        assert!(graph.add_edge(v1, v2).is_err());
    }

    #[test]
    fn test_create_undirected_graph() {
        let mut graph = UndirectedGraph::new();

        // Adding vertices
        let v_s = graph.add_vertex('s');
        let v_a = graph.add_vertex('a');
        let v_b = graph.add_vertex('b');
        let v_c = graph.add_vertex('c');
        let v_d = graph.add_vertex('d');
        let v_e = graph.add_vertex('e');

        // Adding edges
        graph.add_edge(v_s, v_a).unwrap();
        graph.add_edge(v_s, v_b).unwrap();
        graph.add_edge(v_a, v_c).unwrap();
        graph.add_edge(v_b, v_c).unwrap();
        graph.add_edge(v_b, v_d).unwrap();
        graph.add_edge(v_c, v_d).unwrap();
        graph.add_edge(v_c, v_e).unwrap();
        graph.add_edge(v_d, v_e).unwrap();

        // Assert vertices count
        assert_eq!(graph.vertices.len(), 6);

        // Assert adjacency relationships
        assert!(graph.vertices[v_s].neighbors.contains(&v_a));
        assert!(graph.vertices[v_s].neighbors.contains(&v_b));
        assert!(graph.vertices[v_a].neighbors.contains(&v_c));
        assert!(graph.vertices[v_b].neighbors.contains(&v_c));
        assert!(graph.vertices[v_b].neighbors.contains(&v_d));
        assert!(graph.vertices[v_c].neighbors.contains(&v_d));
        assert!(graph.vertices[v_c].neighbors.contains(&v_e));
        assert!(graph.vertices[v_d].neighbors.contains(&v_e));

        // Test BFS from 's'
        graph.bfs(v_s);
        for vertex in &graph.vertices {
            assert_eq!(vertex.cc_value, Some(1)); // All vertices should be reachable from 's'
        }

        // Reset graph and test UCC (connected components)
        graph.clear_exploration();
        graph.ucc();

        // All vertices should belong to the same connected component
        let cc_value = graph.vertices[v_s].cc_value.unwrap();
        for vertex in &graph.vertices {
            assert_eq!(vertex.cc_value, Some(cc_value));
        }
    }
}
