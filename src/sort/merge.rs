/// Pseudocode
/// MergeSort
///     Input: array A of n distict integers
///     Output: array with the integers, sorted from smallest to largest
///    
///     //ignoring base case
///     C := recursively sort first half of A
///     D := recursively sort second half of A
///     return Merge(C, D)
///
/// Merge
///     Input: sorted arrays C and D (length n/2 each)
///     Output: sorted array B (length n)
///     Simplifying assumption: n is even
///    
///     i := 1
///     j := 1
///     for k := 1 to n do
///         if C[i] < D[j] then
///             B[k] := C[i]
///             i := i + 1
///     else
///         B[k] := D[j]
///         j := j + 1
///
pub fn merge_sort<T>(arr: &mut [T])
where
    T: Ord + Copy,
{
    let mid = arr.len() / 2;
    if mid == 0 {
        return;
    }

    merge_sort(&mut arr[..mid]);
    merge_sort(&mut arr[mid..]);

    let mut ret = arr.to_vec();

    merge(&arr[..mid], &arr[mid..], &mut ret[..]);

    arr.copy_from_slice(&ret);
}

fn merge<T>(left: &[T], right: &[T], ret: &mut [T])
where
    T: Ord + Copy,
{
    let mut left_cursor = 0;
    let mut right_cursor = 0;
    let mut ret_cursor = 0;

    while left_cursor < left.len() && right_cursor < right.len() {
        if left[left_cursor] <= right[right_cursor] {
            ret[ret_cursor] = left[left_cursor];
            left_cursor += 1;
        } else {
            ret[ret_cursor] = right[right_cursor];
            right_cursor += 1;
        }
        ret_cursor += 1;
    }

    if left_cursor < left.len() {
        ret[ret_cursor..].copy_from_slice(&left[left_cursor..]);
    }

    if right_cursor < right.len() {
        ret[ret_cursor..].copy_from_slice(&right[right_cursor..]);
    }
}

#[cfg(test)]
mod tests {
    // Import necessary items from the outer scope
    use super::*;

    #[test]
    fn test_merge_empty_arrays() {
        let left = [];
        let right = [];
        let mut ret = [0; 0];

        merge(&left, &right, &mut ret);
        assert_eq!(ret, []);
    }

    #[test]
    fn test_merge_one_empty_array() {
        let left = [1, 3, 5];
        let right = [];
        let mut ret = [0; 3];

        merge(&left, &right, &mut ret);
        assert_eq!(ret, [1, 3, 5]);

        let left = [];
        let right = [2, 4, 6];
        let mut ret = [0; 3];

        merge(&left, &right, &mut ret);
        assert_eq!(ret, [2, 4, 6]);
    }

    #[test]
    fn test_merge_sorted_arrays() {
        let left = [1, 3, 5];
        let right = [2, 4, 6];
        let mut ret = [0; 6];

        merge(&left, &right, &mut ret);
        assert_eq!(ret, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_merge_unsorted_arrays() {
        let left = [5, 3, 1];
        let right = [6, 4, 2];
        let mut ret = [0; 6];

        merge(&left, &right, &mut ret);
        assert_eq!(ret, [5, 3, 1, 6, 4, 2]);
    }

    #[test]
    fn test_merge_arrays_with_duplicates() {
        let left = [1, 3, 5, 5];
        let right = [2, 4, 6, 6];
        let mut ret = [0; 8];

        merge(&left, &right, &mut ret);
        assert_eq!(ret, [1, 2, 3, 4, 5, 5, 6, 6]);
    }
}
