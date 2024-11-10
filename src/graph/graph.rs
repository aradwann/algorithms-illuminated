use std::collections::HashSet;

pub type VertexIndex = usize;
#[derive(Debug, PartialEq)]
pub enum GraphError {
    SelfLoop,
    ParallelEdge,
    Cycle,
    VertexNotFound,
}

#[derive(Debug)]
pub struct Vertex {
    pub value: char,
    pub edges: HashSet<VertexIndex>,
}

impl Vertex {
    pub fn new(value: char) -> Self {
        Self {
            value,
            edges: HashSet::new(),
        }
    }
}
pub trait Graph {
    fn add_vertex(&mut self, index: VertexIndex, value: char);
    fn add_edge(&mut self, from: VertexIndex, to: VertexIndex) -> Result<(), GraphError>;
    fn get_neighbors(&self, index: VertexIndex) -> Vec<VertexIndex>;
}
