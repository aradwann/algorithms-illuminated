use std::{
    fs::File,
    io::{self, BufRead, BufReader},
};

pub fn build_vec_from_txt(path: &str) -> io::Result<Vec<i32>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);

    reader
        .lines()
        .map(|line| {
            line.and_then(|line| {
                line.parse::<i32>()
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_test_file(path: &str, content: &str) {
        std::fs::write(path, content).expect("Unable to write test file");
    }

    #[test]
    fn test_build_vec_from_txt_success() {
        // Arrange
        let path = "./test_success.txt";
        let content = "1\n2\n3\n4\n5\n6\n";
        write_test_file(path, content);
        let expected_vec = vec![1, 2, 3, 4, 5, 6];

        // Act
        let extracted_vec = build_vec_from_txt(path).unwrap();

        // Assert
        assert_eq!(expected_vec, extracted_vec);

        // Cleanup
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn test_build_vec_from_txt_invalid_data() {
        // Arrange
        let path = "./test_invalid_data.txt";
        let content = "1\n2\nthree\n4\n";
        write_test_file(path, content);

        // Act
        let result = build_vec_from_txt(path);

        // Assert
        assert!(result.is_err());
        if let Err(e) = result {
            assert_eq!(e.kind(), io::ErrorKind::InvalidData);
        }

        // Cleanup
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn test_build_vec_from_txt_file_not_found() {
        // Arrange
        let path = "./non_existent_file.txt";

        // Act
        let result = build_vec_from_txt(path);

        // Assert
        assert!(result.is_err());
        if let Err(e) = result {
            assert_eq!(e.kind(), io::ErrorKind::NotFound);
        }
    }
}
