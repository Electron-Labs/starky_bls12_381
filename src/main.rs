use eth_types::{eth2::{BeaconBlockHeader, SigningData, SyncAggregate, SyncCommittee, SyncCommitteeUpdate}, H256};
use starky_bls12_381::aggregate_proof::aggregate_proof;
use tree_hash::TreeHash;
use std::fs::File;
use std::io::BufReader;
use serde_json::{self, Value};

fn main() {
   env_logger::init();
   let file = File::open("src/light_client_update_period_1053.json").unwrap();
   let reader = BufReader::new(file);
   let light_client_update_json:Value = serde_json::from_reader(reader).expect("unable to read the file");

   let prev_file = File::open("src/light_client_update_period_1052.json").unwrap();
   let reader = BufReader::new(prev_file);
   let prev_light_client_update_json:Value = serde_json::from_reader(reader).expect("unable to read the file");


   let pub_keys =  prev_light_client_update_json["data"]["next_sync_committee"]["pubkeys"]
                                                                                                .as_array().unwrap()
                                                                                                .iter()
                                                                                                .map(|i| i.to_string())
                                                                                                .collect::<Vec<String>>();

    let sync_aggregate_str = serde_json::to_string(light_client_update_json["data"]["sync_aggregate"].as_object().unwrap()).unwrap();                                                                                      
    let sync_aggregate: SyncAggregate = serde_json::from_str(&sync_aggregate_str).unwrap();

    let domain:[u8;32] = hex::decode("0x070000006a95a1a967855d676d48be69883b712607f952d5198d0f5677564636".split_at(2).1).unwrap().try_into().unwrap();
    let domain_h256 = H256::from(domain);

    let attested_header_str = serde_json::to_string(&light_client_update_json["data"]["attested_header"]["beacon"].as_object().unwrap()).unwrap();
    let attested_header: BeaconBlockHeader = serde_json::from_str(&attested_header_str).unwrap();

    let signing_root = H256(
        SigningData{
            object_root: H256(attested_header.tree_hash_root()),
            domain: domain_h256
        }.tree_hash_root()
    );

    let prev_next_sync_committee_branch_json_str = serde_json::to_string(&prev_light_client_update_json["data"]["next_sync_committee_branch"].as_array().unwrap()).unwrap();
    let prev_next_sync_committee_branch: Vec<eth_types::H256> =
    serde_json::from_str(&prev_next_sync_committee_branch_json_str).unwrap();

    let prev_next_sync_committee_json_str = serde_json::to_string(&prev_light_client_update_json["data"]["next_sync_committee"]).unwrap();
    let prev_next_sync_committee: SyncCommittee =
        serde_json::from_str(&prev_next_sync_committee_json_str).unwrap();

    let prev_sync_committee_update = SyncCommitteeUpdate {
        next_sync_committee: prev_next_sync_committee,
        next_sync_committee_branch: prev_next_sync_committee_branch,
    };

    aggregate_proof(pub_keys, sync_aggregate,signing_root.0.0, prev_sync_committee_update);
    return;
}