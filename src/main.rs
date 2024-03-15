use eth_types::{eth2::{BeaconBlockHeader, SigningData, SyncAggregate, SyncCommittee, SyncCommitteeUpdate}, H256};
use starky_bls12_381::aggregate_proof::aggregate_proof;
use tree_hash::TreeHash;

#[tokio::main]
async fn main() {
    env_logger::init();

    let latest_finality_update: serde_json::Value = reqwest::get("http://unstable.mainnet.beacon-api.nimbus.team/eth/v1/beacon/light_client/finality_update")
                                                    .await
                                                    .unwrap()
                                                    .json()
                                                    .await
                                                    .unwrap();

    let latest_slot = latest_finality_update["data"]["attested_header"]["beacon"]["slot"].as_str().unwrap().parse::<u64>().unwrap();
    let period = latest_slot/(256 * 32);
    let prev_period = period - 1;


    let url = format!("http://unstable.mainnet.beacon-api.nimbus.team/eth/v1/beacon/light_client/updates?start_period={}&count={}", prev_period, 2);
    let combined_period_lc_updates: serde_json::Value = reqwest::get(url)
                                                        .await
                                                        .unwrap()
                                                        .json()
                                                        .await
                                                        .unwrap();
    let prev_light_client_update_json = combined_period_lc_updates[0].clone();
    let light_client_update_json = combined_period_lc_updates[1].clone();

    let pub_keys = prev_light_client_update_json["data"]["next_sync_committee"]["pubkeys"]
                                                                                                    .as_array().unwrap()
                                                                                                    .iter()
                                                                                                    .map(|i| i.to_string())
                                                                                                    .collect::<Vec<String>>();
    let sync_aggregate_json_str = serde_json::to_string(&light_client_update_json["data"]["sync_aggregate"].as_object().unwrap()).unwrap();
    let sync_aggregate: SyncAggregate = serde_json::from_str(&sync_aggregate_json_str).unwrap();

    let attested_header_json_str = serde_json::to_string(&light_client_update_json["data"]["attested_header"]["beacon"].as_object().unwrap()).unwrap();
    let attested_header: BeaconBlockHeader = serde_json::from_str(&attested_header_json_str).unwrap();
    let domain:[u8;32] = hex::decode("0x070000006a95a1a967855d676d48be69883b712607f952d5198d0f5677564636".split_at(2).1).unwrap().try_into().unwrap();
    let domain_h256 = H256::from(domain);
    let signing_root =  eth_types::H256(
        SigningData {
            object_root: H256(attested_header.tree_hash_root()),
            domain: domain_h256,
        }
        .tree_hash_root(),
    ).0.0;

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

    aggregate_proof(pub_keys, sync_aggregate,signing_root, prev_sync_committee_update);
    return;
}