use algorithms_illuminated::sort::compute_median_sum;

fn main() {
    let filename = "src/sort/txt/medians.txt";

    match compute_median_sum(filename) {
        Ok(result) => {
            println!(
                "The last 4 digits of the sum of the kth medians: {:04}",
                result
            );
        }
        Err(e) => {
            eprintln!("Error: {}", e);
        }
    }
}
