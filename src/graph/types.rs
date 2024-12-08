pub type VertexIndex = usize;
pub type Length = usize;

#[derive(Debug, PartialEq)]
pub enum GraphError {
    SelfLoop,
    ParallelEdge,
    Cycle,
    VertexNotFound,
    FileNotFound,
}

pub trait Graph {
    fn add_vertex(&mut self);
    fn add_edge(
        &mut self,
        from: VertexIndex,
        to: VertexIndex,
        length: Length,
    ) -> Result<(), GraphError>;
    fn add_unit_edge(&mut self, from: VertexIndex, to: VertexIndex) -> Result<(), GraphError>;
}
