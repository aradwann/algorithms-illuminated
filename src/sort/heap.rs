use std::{
    cmp::{Ordering, Reverse},
    collections::BinaryHeap,
    fmt::Debug,
};

/// Pseudocode
/// HeapSort
///
///     Input: array A of n distict integers
///     Output: array B with the same integers, sorted from smallest to largest
///
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

/// solves the median maintenance problem using heap data structure
pub fn get_median(arr: Vec<i32>) -> f64 {
    assert!(!arr.is_empty());
    let mut max_heap = BinaryHeap::new();
    let mut min_heap = BinaryHeap::new();

    for e in arr {
        if max_heap.is_empty() || e < *max_heap.peek().unwrap() {
            max_heap.push(e);
        } else {
            // rust heap is max heap by default
            // Wrap values in `Reverse` to make it min heap
            min_heap.push(Reverse(e));
        }

        // balance heaps
        if max_heap.len() > min_heap.len() {
            min_heap.push(Reverse(max_heap.pop().unwrap()));
        } else if max_heap.len() > min_heap.len() {
            max_heap.push(min_heap.pop().unwrap().0);
        }
    }

    // return median
    match max_heap.len().cmp(&min_heap.len()) {
        Ordering::Greater => *max_heap.peek().unwrap() as f64,
        Ordering::Less => min_heap.peek().unwrap().0 as f64,
        Ordering::Equal => {
            (*max_heap.peek().unwrap() as f64 + min_heap.peek().unwrap().0 as f64) / 2.0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_heap_sort() {
        let vec = vec![7, 3, 4, 5];
        let result_vec = heap_sort(vec);
        let sorted_vec = vec![3, 4, 5, 7];
        assert_eq!(result_vec, sorted_vec);
    }

    #[test]
    #[should_panic]
    fn test_get_median_of_empty_arr() {
        let vec: Vec<i32> = vec![];
        get_median(vec);
    }
    #[test]
    fn test_get_median_of_even_arr() {
        let vec = vec![7, 4, 7, 3];
        let result = get_median(vec);
        let wanted = 5.5;
        assert_eq!(result, wanted);
    }
    #[test]
    fn test_get_median_of_odd_arr() {
        let vec = vec![9, 3, 2, 1, 6];
        let result = get_median(vec);
        let wanted = 3.0;
        assert_eq!(result, wanted);
    }
}
