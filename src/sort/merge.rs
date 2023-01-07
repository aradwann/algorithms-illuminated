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
pub fn merge_sort<T>(arr: Vec<T>) -> Vec<T>
where
    T: Ord + Copy,
{
    let len = arr.len();
    if len <= 1 {
        return arr;
    }

    let (first_half, second_half) = arr.split_at(len / 2);

    let sorted_left_arr = merge_sort(first_half.into());
    let sorted_right_arr = merge_sort(second_half.into());
    merge(sorted_left_arr, sorted_right_arr)
}

fn merge<T>(left_arr: Vec<T>, right_arr: Vec<T>) -> Vec<T>
where
    T: Ord + Copy,
{
    let len = left_arr.len();
    let mut merged_vec = vec![];
    let mut i = 0;
    let mut j = 0;
    // TODO: refactor
    while i < len && j < len {
        if left_arr[i] < right_arr[j] {
            merged_vec.push(left_arr[i]);
            i += 1;
        } else {
            merged_vec.push(right_arr[j]);
            j += 1;
        }
    }
    if i >= len {
        while j < len {
            merged_vec.push(right_arr[j]);
            j += 1;
        }
    } else {
        while i < len {
            merged_vec.push(left_arr[i]);
            i += 1;
        }
    }
    merged_vec
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merge_sort() {
        let vec = vec![7, 3, 4, 5];
        let result_vec = merge_sort(vec);
        let merged_vec = vec![3, 4, 5, 7];
        assert_eq!(result_vec, merged_vec)
    }

    #[test]
    fn test_merge() {
        let left_arr = vec![3, 5];
        let right_arr = vec![4, 7];
        let result_vec = merge(left_arr, right_arr);
        let merged_vec = vec![3, 4, 5, 7];
        assert_eq!(result_vec, merged_vec)
    }
}
