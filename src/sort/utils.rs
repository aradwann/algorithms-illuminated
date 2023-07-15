use std::{
    fs::File,
    io::{self, BufRead},
};

pub fn build_vec_from_txt(path: &str) -> io::Result<Vec<i32>> {
    let file = File::open(path)?;
    let reader = io::BufReader::new(file);

    let mut numbers: Vec<i32> = Vec::new();

    for line in reader.lines() {
        let line = line?;
        let number: i32 = line.parse().expect("Failed to parse line into integer");
        numbers.push(number);
    }
    Ok(numbers)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_build_graph_from_txt() {
        let expected_vec = vec![1, 2, 3, 4, 5, 6];

        let extracted_vec = build_vec_from_txt("./src/sort/txt/vec_test_success.txt").unwrap();

        assert_eq!(expected_vec, extracted_vec)
    }

    #[test]
    #[should_panic(
        expected = "Failed to parse line into integer: ParseIntError { kind: InvalidDigit }"
    )]
    fn test_build_graph_from_txt_fail() {
        build_vec_from_txt("./src/sort/txt/vec_test_fail.txt").unwrap();
    }
}
