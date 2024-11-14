pub type VertexIndex = usize;
#[derive(Debug, PartialEq)]
pub enum GraphError {
    SelfLoop,
    ParallelEdge,
    Cycle,
    VertexNotFound,
    FileNotFound,
}

pub trait Graph {
    fn add_vertex(&mut self, index: VertexIndex, value: char);
    fn add_edge(&mut self, from: VertexIndex, to: VertexIndex) -> Result<(), GraphError>;
}
