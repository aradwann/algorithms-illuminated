use std::{
    fs::File,
    io::{self, BufRead, BufReader},
};

pub fn build_vec_from_txt(path: &str) -> io::Result<Vec<i32>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    let numbers: Result<Vec<i32>, _> = reader
        .lines()
        .map(|line| {
            line.and_then(|line| {
                line.parse()
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            })
        })
        .collect();

    numbers
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_graph_from_txt() {
        // Arrange
        let expected_vec = vec![1, 2, 3, 4, 5, 6];

        // Act
        let extracted_vec = build_vec_from_txt("./src/sort/txt/vec_test_success.txt").unwrap();

        // Assert
        assert_eq!(expected_vec, extracted_vec)
    }

    #[test]
    #[should_panic(
        expected = "called `Result::unwrap()` on an `Err` value: Custom { kind: InvalidData, error: ParseIntError { kind: InvalidDigit } }"
    )]
    fn test_build_graph_from_txt_fail() {
        // Act & Assert
        build_vec_from_txt("./src/sort/txt/vec_test_fail.txt").unwrap();
    }
}
