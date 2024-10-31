use std::collections::VecDeque;

/// representing a graph using an adjacency list which is
/// 1) An array containing the graph vertices
/// 2) An array containing the graph edges
/// 3) For each edge, a pointer to each of its two endpoints
/// 4) for each vertex, a pointer to each of the incident edges

type VertexIndex = usize;

#[derive(Debug, Clone)]
struct VertexData {
    edges: Vec<EdgeIndex>,
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
        // order of vertices does not matter as it is undirected
        // so i order it that it begins always with the smaller
        if tail > head {
            Self(head, tail)
        } else {
            Self(tail, head)
        }
    }
}

#[derive(Debug)]
pub struct UndirectedGraph {
    vertices: Vec<VertexData>,
    edges: Vec<EdgeData>,
}
impl UndirectedGraph {
    pub fn new() -> Self {
        UndirectedGraph {
            vertices: vec![],
            edges: vec![],
        }
    }
    pub fn add_vertex(&mut self, value: char) -> VertexIndex {
        let index = self.vertices.len();
        self.vertices.push(VertexData {
            edges: vec![],
            value,
            explored: false,
            cc_value: 0, // 0 means no cc value yet
        });
        index
    }
    pub fn add_edge(&mut self, tail: VertexIndex, head: VertexIndex) -> EdgeIndex {
        for e in &self.edges {
            if e.0 == tail && e.1 == head {
                panic!("parallel edges aren't allowed atm")
            }
        }
        let edge_index = self.edges.len();
        self.edges.push(EdgeData::new(tail, head));

        let vertex_data_1 = &mut self.vertices[tail];
        vertex_data_1.edges.push(edge_index);

        let vertex_data_2 = &mut self.vertices[head];
        vertex_data_2.edges.push(edge_index);
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
        self.mark_all_vertices_unexplored();
        let mut queue = VecDeque::new();
        queue.push_back(self.edges[0].0); // push the first vertex data into the queue
        while !queue.is_empty() {
            let vertex_index = queue.pop_front().unwrap(); // the index of the vertex
            let vertex_data = self.vertices[vertex_index].clone();
            for edge_index in vertex_data.edges {
                let EdgeData(_, vertex_index_2) = self.edges[edge_index];
                let vertex_2 = &mut self.vertices[vertex_index_2];
                if !vertex_2.explored {
                    vertex_2.explored = true;
                    println!("exploring Vertex {:#?}", &vertex_2);
                    queue.push_back(vertex_index_2);
                }
            }
        }
    }
    fn mark_all_vertices_unexplored(&mut self) {
        self.vertices.iter_mut().for_each(|n| n.explored = false);
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
        self.mark_all_vertices_unexplored();
        let mut num_cc = 0;
        for i in 0..self.vertices.len() {
            if !self.vertices[i].explored {
                num_cc += 1;
                let mut queue = VecDeque::new();
                queue.push_back(i); // push the first vertex index into the queue
                while !queue.is_empty() {
                    let vertex_index = queue.pop_front().unwrap(); // the index of the vertex
                    let vertex_data = self.vertices[vertex_index].clone();

                    self.vertices[vertex_index].cc_value = num_cc;
                    for edge_index in vertex_data.edges {
                        let EdgeData(_, vertex_index_2) = self.edges[edge_index];
                        let vertex_2 = &mut self.vertices[vertex_index_2];
                        if !vertex_2.explored {
                            vertex_2.explored = true;
                            println!("exploring vertex {:#?}", &vertex_2);
                            queue.push_back(vertex_index_2);
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
    #[should_panic(expected = "self-loops aren't allowed atm")]
    fn test_create_self_loop() {
        EdgeData::new(2, 2);
    }

    #[test]
    #[should_panic(expected = "parallel edges aren't allowed atm")]
    fn test_add_parallel_edge() {
        let mut graph = UndirectedGraph::new();

        graph.add_vertex('s');
        graph.add_vertex('a');

        graph.add_edge(0, 1);
        graph.add_edge(0, 1);
    }

    #[test]
    fn test_create_undirected_graph() {
        let mut graph = UndirectedGraph::new();

        graph.add_vertex('s');
        graph.add_vertex('a');
        graph.add_vertex('b');
        graph.add_vertex('c');
        graph.add_vertex('d');
        graph.add_vertex('e');

        graph.add_edge(0, 1);
        graph.add_edge(0, 2);
        graph.add_edge(1, 3);
        graph.add_edge(2, 3);
        graph.add_edge(2, 4);
        graph.add_edge(3, 4);
        graph.add_edge(3, 5);
        graph.add_edge(4, 5);

        // assert graph has 8 vertices
        assert_eq!(graph.edges.len(), 8);
        // assert graph has 6 edges
        assert_eq!(graph.vertices.len(), 6);
    }
}
