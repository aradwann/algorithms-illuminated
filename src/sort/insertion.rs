/// Pseudocode
/// InsertionSort(A, n)
/// for i = 2 to n
///     key = A[i]
///     // insert A[i] into the sorted subarray
///     A[1:i-1]
///     j = i - 1
///     while j > 0 and A[j] > key
///         A[j+1] = A[j]
///         j = j - 1
///     A[j+1] = key
pub fn insertion_sort<T>(array: &mut [T])
where
    T: Ord + Copy,
{
    let len = array.len();

    for i in 1..len {
        let key = array[i];
        let mut j = i;

        while j > 0 && array[j - 1] > key {
            array[j] = array[j - 1];
            j -= 1;
        }

        array[j] = key;
    }
}
