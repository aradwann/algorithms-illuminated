#[cfg(test)]
mod tests {

    use algorithms_illuminated::sort::insertion_sort;
    use algorithms_illuminated::sort::merge_sort;

    #[test]
    fn test_merge_sort() {
        let mut vec = vec![5, 3, 1, 4, 6, 2];
        merge_sort(&mut vec);
        assert_eq!(vec, vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_insertion_sort() {
        let mut vec = vec![5, 3, 1, 4, 6, 2];
        insertion_sort(&mut vec);
        assert_eq!(vec, vec![1, 2, 3, 4, 5, 6]);
    }
}
