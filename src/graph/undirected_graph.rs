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
    fn new(vertex_1: VertexIndex, vertex_2: VertexIndex) -> Self {
        // order of vertices does not matter as it is undirected
        if vertex_1 > vertex_2 {
            Self(vertex_2, vertex_1)
        } else {
            Self(vertex_1, vertex_2)
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
    pub fn add_edge(&mut self, source: VertexIndex, target: VertexIndex) -> EdgeIndex {
        let edge_index = self.edges.len();
        self.edges.push(EdgeData::new(source, target));

        let vertex_data_1 = &mut self.vertices[source];
        vertex_data_1.edges.push(edge_index);

        let vertex_data_2 = &mut self.vertices[target];
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
        while queue.len() != 0 {
            let vertex_index = queue.pop_front().unwrap(); // the index of the vertex
            let vertex_data = self.vertices[vertex_index].clone();
            for edge_index in vertex_data.edges {
                let EdgeData(_, vertex_index_2) = self.edges[edge_index];
                let vertex_2 = &mut self.vertices[vertex_index_2];
                if vertex_2.explored == false {
                    vertex_2.explored = true;
                    println!("exploring Vertex {:#?}", &vertex_2);
                    queue.push_back(vertex_index_2);
                }
            }
        }
    }
    fn mark_all_vertices_unexplored(&mut self) {
        self.vertices.iter_mut().map(|n| n.explored = false);
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
            if self.vertices[i].explored == false {
                num_cc += 1;
                let mut queue = VecDeque::new();
                queue.push_back(i); // push the first vertex index into the queue
                while queue.len() != 0 {
                    let vertex_index = queue.pop_front().unwrap(); // the index of the vertex
                    let vertex_data = self.vertices[vertex_index].clone();

                    self.vertices[vertex_index].cc_value = num_cc;
                    for edge_index in vertex_data.edges {
                        let EdgeData(_, vertex_index_2) = self.edges[edge_index];
                        let vertex_2 = &mut self.vertices[vertex_index_2];
                        if vertex_2.explored == false {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_undirected_graph() {
       unimplemented!()
    }
}
