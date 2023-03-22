use std::{cmp::Reverse, collections::BinaryHeap, fmt::Debug};

/// Pseudocode
/// HeapSort
///     Input: array A of n distict integers
///     Output: array B with the same integers, sorted from smallest to largest
///--------------------------------------------------------------------------------    
///     H := empty heap
///     for i := 1 to n do
///         Insert A[i] into H
///     for i := 1 to n do
///         B[i] := ExtractMin from H
pub fn heap_sort<T>(arr: Vec<T>) -> Vec<T>
where
    T: Ord + Clone + Debug,
{
    let mut heap = BinaryHeap::new();
    let mut b = Vec::with_capacity(arr.len());

    for e in arr.clone() {
        // rust heap is max heap by default
        // Wrap values in `Reverse` to make it min heap
        heap.push(Reverse(e));
    }

    for _ in 0..(arr.len()) {
        b.push(heap.pop().unwrap().0);
    }

    b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_heap_sort() {
        let vec = vec![7, 3, 4, 5];
        let result_vec = heap_sort(vec);
        let sorted_vec = vec![3, 4, 5, 7];
        assert_eq!(result_vec, sorted_vec)
    }
}
