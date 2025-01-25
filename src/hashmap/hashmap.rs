use std::collections::HashSet;

/// Pseudocode
/// 2-SUM (Hash Table solution)
///
///     Input: array A of n integers and target integers t  
///     Output: "yes" if there are two integers x, y in A with x + y = t, "no" otherwise
///
///--------------------------------------------------------------------------------    
///     H := empty heap
///     for i := 1 to n do
///         Insert A[i] into H
///     for i := 1 to n do
///         y := t - A[i]
///        if y is in H then // using lookup in hash table
///           return "yes"
///    return "no"
pub fn two_sum(arr: Vec<i32>, target: i32) -> String {
    let mut hash_set = HashSet::new();

    for e in arr {
        let y = target - e;
        if hash_set.contains(&y) {
            return "yes".to_string();
        }
        hash_set.insert(e);
    }

    "no".to_string()
}

/// Pseudocode
/// 2-SUM (how many distinct pairs)
/// input: array A of n integers and an array of target integers t
/// output: the number of distinct pairs x, y in A with x + y = t
/// --------------------------------------------------------------------------------
/// H := empty hash table
/// for i := 1 to n do
///    Insert A[i] into H
/// count := 0
/// for i := 1 to n do
///   y := t - A[i]
///  if y is in H then
///    count := count + 1
///   remove y from H
/// return count
pub fn two_sum_distinct_pairs(arr: Vec<i32>, target: i32) -> i32 {
    let mut hash_set = HashSet::new();
    let mut count = 0;

    for e in arr {
        let y = target - e;
        if hash_set.contains(&y) {
            count += 1;
            hash_set.remove(&y);
        } else {
            hash_set.insert(e);
        }
    }

    count
}

pub fn count_distinct_sums_in_range(arr: Vec<i64>, t_min: i64, t_max: i64) -> usize {
    let mut valid_targets = HashSet::new();
    let numbers: HashSet<i64> = arr.iter().copied().collect();

    // Iterate over all target values in the range
    for t in t_min..=t_max {
        for &x in &arr {
            let y = t - x;

            // Check if y exists in the set and x != y
            if y != x && numbers.contains(&y) {
                valid_targets.insert(t);
                break; // No need to check further for this t
            }
        }
    }

    valid_targets.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_two_sum_yes() {
        // Arrange
        let arr = vec![1, 2, 3, 4, 5, 6];
        let target = 10;

        // Act
        let result = two_sum(arr, target);

        // Assert
        assert_eq!(result, "yes");
    }

    #[test]
    fn test_two_sum_no() {
        // Arrange
        let arr = vec![1, 2, 3, 4, 5, 6];
        let target = 20;

        // Act
        let result = two_sum(arr, target);

        // Assert
        assert_eq!(result, "no");
    }

    #[test]
    fn test_two_sum_distinct_pairs() {
        // Arrange
        let arr = vec![1, 2, 3, 4, 5, 6];
        let target = 10;

        // Act
        let result = two_sum_distinct_pairs(arr, target);

        // Assert
        assert_eq!(result, 1);
    }

    #[test]
    fn test_two_sum_distinct_pairs_no_pairs() {
        // Arrange
        let arr = vec![1, 2, 3, 4, 5, 6];
        let target = 20;

        // Act
        let result = two_sum_distinct_pairs(arr, target);

        // Assert
        assert_eq!(result, 0);
    }

    #[test]
    fn test_count_distinct_sums_in_range() {
        // Arrange
        let arr = vec![-3, -1, 1, 2, 9, 11, 7, 6, 2];
        let t_min = 3;
        let t_max = 10;

        // Act
        let result = count_distinct_sums_in_range(arr, t_min, t_max);

        // Assert
        assert_eq!(result, 8);
    }

    #[test]
    fn test_count_distinct_sums_in_range_2() {
        // Arrange
        let arr = vec![1, 2, 3, 4, 5, 6];

        let t_min = 3;
        let t_max = 10;

        // Act
        let result = count_distinct_sums_in_range(arr, t_min, t_max);

        // Assert
        assert_eq!(result, 8);
    }
}
