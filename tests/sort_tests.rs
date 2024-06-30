#[cfg(test)]
mod tests {
    // This will import the merge_sort function directly

    use clrs::sort::merge_sort;

    #[test]
    fn test_merge_sort() {
        let mut vec = vec![5, 3, 1, 4, 6, 2];
        merge_sort(&mut vec);
        assert_eq!(vec, vec![1, 2, 3, 4, 5, 6]);
    }
}
