use std::fs::File;
use std::io::{BufReader, Read};
use starky_bls12_381::aggregate_proof::aggregate_proof;

fn main() {
    env_logger::init();
    let mut file = File::open("src/light_client_update_period_634.json").unwrap();
    let mut light_client_update_json_str = String::new();
    file.read_to_string(&mut light_client_update_json_str)
        .expect("Unable to read file");

    let prev_file = File::open("src/light_client_update_period_633.json").unwrap();
    let prev_reader = BufReader::new(prev_file);
    let prev_light_client_update_json: serde_json::Value = serde_json::from_reader(prev_reader).unwrap();

    let mut prev_file = File::open("src/light_client_update_period_633.json").unwrap();
    let mut prev_light_client_update_json_str = String::new();
    prev_file.read_to_string(&mut prev_light_client_update_json_str)
        .expect("Unable to read file");

    aggregate_proof(light_client_update_json_str, prev_light_client_update_json_str, prev_light_client_update_json);
    return;
}