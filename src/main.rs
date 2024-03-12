use num_bigint::BigUint;
use plonky2::{plonk::config::{GenericConfig, PoseidonGoldilocksConfig}, util::{log2_ceil, timing::TimingTree}};
use plonky2_crypto::{biguint::{BigUintTarget, CircuitBuilderBiguint}, u32::arithmetic_u32::U32Target};
use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
use crate::{calc_pairing_precomp::PairingPrecompStark, ecc_aggregate::ECCAggStark, final_exponentiate::FinalExponentiateStark, fp12_mul::FP12MulStark, fp_plonky2::N, g1_plonky2::{pk_point_check, PUB_KEY_LEN}, g2_plonky2::{signature_point_check, SIG_LEN}, hash_to_curve::hash_to_curve, miller_loop::MillerLoopStark, native::{Fp, Fp12, Fp2}};
use starky::util::trace_rows_to_poly_values;
use std::{io::Read, str::FromStr, time::Instant};
use plonky2_circuit_serializer::serializer::CustomGateSerializer;

use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::proof::ProofWithPublicInputs;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::AlgebraicHasher;
use plonky2::field::extension::Extendable;
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::prover::prove as plonky2_prove;
use log::Level;
use anyhow::Result;
use serde_json;
use std::io::BufReader;
use std::fs::File;
use snowbridge_milagro_bls::{AggregatePublicKey, BLSCurve::bls381::utils::hash_to_curve_g2, PublicKey, Signature};
use eth_lc_plonky2::utils::{compute_signing_root, get_attested_header_from_light_client_update_json_str, get_sync_aggregate_from_light_client_update_json_str, get_sync_committee_update_from_light_client_update_json_str, BeaconRPCRoutes, BeaconRPCVersion};
use tree_hash::TreeHash;
use eth_types::H256;

pub mod native;
pub mod big_arithmetic;
pub mod fp;
pub mod fp2;
pub mod fp6;
pub mod fp12;
pub mod g1;
pub mod utils;
pub mod calc_pairing_precomp;
pub mod miller_loop;
pub mod final_exponentiate;
pub mod fp12_mul;
pub mod ecc_aggregate;
pub mod hash_to_field;
pub mod fp_plonky2;
pub mod fp2_plonky2;
pub mod hash_to_curve;
pub mod g1_plonky2;
pub mod g2_plonky2;

fn calc_pairing_precomp<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F=F>,
    const D: usize
>(
    x: Fp2,
    y: Fp2,
    z: Fp2,
) -> (PairingPrecompStark<F, D>, starky::proof::StarkProofWithPublicInputs<F, C, D>, StarkConfig) {
    let mut config = StarkConfig::standard_fast_config();
    config.fri_config.rate_bits = 2;
    let stark = PairingPrecompStark::<F, D>::new(1024);
    let trace = stark.generate_trace(x.get_u32_slice(), y.get_u32_slice(), z.get_u32_slice());
    let ell_coeffs = native::calc_pairing_precomp(x, y, z);
    let mut public_inputs = Vec::new();
    for e in x.get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(e.clone()));
    }
    for e in y.get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(e.clone()));
    }
    for e in z.get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(e.clone()));
    }
    for cs in ell_coeffs.iter() {
        for fp2 in cs.iter() {
            for fp in fp2.0.iter() {
                for e in fp.0.iter() {
                    public_inputs.push(F::from_canonical_u32(*e));
                }
            }
        }
    }
    assert_eq!(public_inputs.len(), calc_pairing_precomp::PUBLIC_INPUTS);
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let t = Instant::now();
    let proof = prove::<F, C, PairingPrecompStark<F, D>, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    ).unwrap();
    println!("Time taken for calc_pairing_precomp stark proof {:?}", t.elapsed());
    verify_stark_proof(stark, proof.clone(), &config).unwrap();
    (stark, proof, config)
}

fn miller_loop_main<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F=F>,
    const D: usize
>(x: Fp, y: Fp, q_x: Fp2, q_y: Fp2, q_z: Fp2) -> (MillerLoopStark<F, D>, starky::proof::StarkProofWithPublicInputs<F, C, D>, StarkConfig) {
    let config = StarkConfig::standard_fast_config();
    let stark = MillerLoopStark::<F, D>::new(1024);
    let ell_coeffs = native::calc_pairing_precomp(q_x, q_y, q_z);
    let res = native::miller_loop(x, y, q_x, q_y, q_z);
    let mut public_inputs = Vec::<F>::new();
    for e in x.0.iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    for e in y.0.iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    for coeff in ell_coeffs.iter() {
        for f2 in coeff.iter() {
            for f in f2.0.iter() {
                for e in f.0.iter() {
                    public_inputs.push(F::from_canonical_u32(*e));
                }
            }
        }
    }
    for f in res.0.iter() {
        for e in f.0.iter() {
            public_inputs.push(F::from_canonical_u32(*e));
        }
    }
    assert_eq!(public_inputs.len(), miller_loop::PUBLIC_INPUTS);
    let s = Instant::now();
    let trace = stark.generate_trace(x, y, ell_coeffs);
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let proof = prove::<F, C, MillerLoopStark<F, D>, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    ).unwrap();
    println!("Time taken for miller_loop stark proof {:?}", s.elapsed());
    verify_stark_proof(stark, proof.clone(), &config).unwrap();
    (stark, proof, config)
}

fn fp12_mul_main<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F=F>,
    const D: usize
>(x: Fp12, y: Fp12) -> (FP12MulStark<F, D>, starky::proof::StarkProofWithPublicInputs<F, C, D>, StarkConfig) {
    let config = StarkConfig::standard_fast_config();
    let stark = FP12MulStark::<F, D>::new(16);
    let s = Instant::now();
    let mut public_inputs = Vec::<F>::new();
    for e in x.get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    for e in y.get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    for e in (x*y).get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    assert_eq!(public_inputs.len(), fp12_mul::PUBLIC_INPUTS);
    let trace = stark.generate_trace(x, y);
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let proof = prove::<F, C, FP12MulStark<F, D>, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    ).unwrap();
    println!("Time taken for fp12_mul stark proof {:?}", s.elapsed());
    verify_stark_proof(stark, proof.clone(), &config).unwrap();
    (stark, proof, config)
}

fn final_exponentiate_main<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F=F>,
    const D: usize
>(x: Fp12) -> (FinalExponentiateStark<F, D>, starky::proof::StarkProofWithPublicInputs<F, C, D>, StarkConfig) {
    let mut config = StarkConfig::standard_fast_config();
    config.fri_config.rate_bits = 2;
    let stark = FinalExponentiateStark::<F, D>::new(8192);
    let s = Instant::now();
    let mut public_inputs = Vec::<F>::new();
    for e in x.get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    for e in x.final_exponentiate().get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    assert_eq!(public_inputs.len(), final_exponentiate::PUBLIC_INPUTS);
    let trace = stark.generate_trace(x);
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let proof = prove::<F, C, FinalExponentiateStark<F, D>, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    ).unwrap();
    println!("Time taken for final_exponentiate stark proof {:?}", s.elapsed());
    verify_stark_proof(stark, proof.clone(), &config).unwrap();
    (stark, proof, config)
}

fn ec_aggregate_main<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F=F>,
    const D: usize
>(points: Vec<[Fp; 2]>, res: [Fp; 2], bits: Vec<bool>) -> (ECCAggStark<F, D>, starky::proof::StarkProofWithPublicInputs<F, C, D>, StarkConfig) {
    let mut config = StarkConfig::standard_fast_config();
    config.fri_config.rate_bits = 2;
    let num_rows = 1<<log2_ceil((points.len()-1)*12);
    let stark = ECCAggStark::<F, D>::new(num_rows);
    let s = Instant::now();
    let mut public_inputs = Vec::<F>::new();
    for pt in &points {
        for x in &pt[0].0 {
            public_inputs.push(F::from_canonical_u32(*x));
        }
        for y in &pt[1].0 {
            public_inputs.push(F::from_canonical_u32(*y));
        }
    }
    for b in bits.iter() {
        public_inputs.push(F::from_bool(*b));
    }
    for x in res[0].0 {
        public_inputs.push(F::from_canonical_u32(x));
    }
    for y in res[1].0 {
        public_inputs.push(F::from_canonical_u32(y));
    }
    assert_eq!(public_inputs.len(), ecc_aggregate::PUBLIC_INPUTS);
    let trace = stark.generate_trace(&points, &bits);
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let proof = prove::<F, C, ECCAggStark<F, D>, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    ).unwrap();
    println!("Time taken for acc_agg stark proof {:?}", s.elapsed());
    verify_stark_proof(stark, proof.clone(), &config).unwrap();
    (stark, proof, config)
}

fn aggregate_proof() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    
    type PpStark = PairingPrecompStark<F, D>;
    type MlStark = MillerLoopStark<F, D>;
    type Fp12MulStark = FP12MulStark<F, D>;
    type FeStark = FinalExponentiateStark<F, D>;
    type ECAggStark = ECCAggStark<F, D>;

    const DST: &str = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
    
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

    let pub_keys = prev_light_client_update_json["sync_committee_update"]["next_sync_committee"]["pubkeys"]
                                                                                                                .as_array().unwrap()
                                                                                                                .iter()
                                                                                                                .map(|i| i.to_string())
                                                                                                                .collect::<Vec<String>>();


    let points: Vec<[Fp;2]> = pub_keys
                                .iter()
                                .map(|i| {
                                    let res =  PublicKey::from_bytes(&hex::decode(i[3..99].to_string()).unwrap()).unwrap();
                                    [
                                        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(res.point.getx().to_string()).unwrap())), 
                                        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(res.point.gety().to_string()).unwrap()))
                                    ]
                                })
                                .collect::<Vec<[Fp;2]>>();

    let sync_aggregate = get_sync_aggregate_from_light_client_update_json_str(&light_client_update_json_str).unwrap();
    
    let mut bits= Vec::new();
    for num in sync_aggregate.sync_committee_bits.0 {
        for j in 0..8{
            bits.push((num>>j & 1) == 1);
        }
    }
    
    let mut public_keys: Vec<PublicKey>  = Vec::new();
    for i in 0..pub_keys.len(){
        if bits[i]  == true{
            public_keys.push(PublicKey::from_bytes(&hex::decode(pub_keys[i][3..99].to_string()).unwrap()).unwrap());
        }
    }

    let apk = AggregatePublicKey::aggregate(&(&public_keys.iter().collect::<Vec<&PublicKey>>())).unwrap();
    let res: [Fp; 2] = [
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(apk.point.getx().to_string()).unwrap())),
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(apk.point.gety().to_string()).unwrap())),
    ];
    println!("ec aggregate stark");
    let (
        stark_ec,
        proof_ec,
        config_ec
    ) = ec_aggregate_main::<F, C, D>(points, res, bits.clone());
    let recursive_ec = recursive_proof::<F, C, ECAggStark, C, D>(stark_ec, proof_ec, &config_ec, true);

    let px1 = res[0];
    let py1 = res[1];

    let routes = BeaconRPCRoutes{
        get_block: String::from(""),
        get_block_header: String::from(""),
        get_light_client_finality_update: String::from(""),
        get_light_client_update: String::from(""),
        get_light_client_update_by_epoch: String::from(""),
        get_bootstrap: String::from(""),
        get_state: String::from(""),
        version: BeaconRPCVersion::V1_5,
    };

    let domain:[u8;32] = hex::decode("0x07000000628941ef21d1fe8c7134720add10bb91e3b02c007e0046d2472c6695".split_at(2).1).unwrap().try_into().unwrap();
    let domain_h256 = H256::from(domain);

    let attested_header = get_attested_header_from_light_client_update_json_str(&routes, &light_client_update_json_str).unwrap();
    let signing_root = compute_signing_root(H256::from(attested_header.tree_hash_root()), domain_h256).0.0;

    let dst = DST.as_bytes();
    let result = hash_to_curve_g2(&signing_root, &dst);
    let q_x1 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(&result.getx().to_string().split(",").collect::<Vec<&str>>()[0][1..].to_string()).unwrap())),
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(&result.getx().to_string().split(",").collect::<Vec<&str>>()[1][..96].to_string()).unwrap())),
    ]);
    let q_y1 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(&result.gety().to_string().split(",").collect::<Vec<&str>>()[0][1..].to_string()).unwrap())),
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(&result.gety().to_string().split(",").collect::<Vec<&str>>()[1][..96].to_string()).unwrap())),
    ]);
    let q_z1 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
        Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
    ]);
    println!("calc_pairing_precomp stark 1");
    let (
        stark_pp1,
        proof_pp1,
        config_pp1
    ) = calc_pairing_precomp::<F, C, D>(q_x1, q_y1, q_z1);
    let recursive_pp1 = recursive_proof::<F, C, PpStark, C, D>(stark_pp1, proof_pp1.clone(), &config_pp1, true);

    println!("miller_loop stark 1");
    let (
        stark_ml1,
        proof_ml1,
        config_ml1,
    ) = miller_loop_main::<F, C, D>(px1, py1, q_x1, q_y1, q_z1);
    let recursive_ml1 = recursive_proof::<F, C, MlStark, C, D>(stark_ml1, proof_ml1.clone(), &config_ml1, true);

    let px2 = Fp::get_fp_from_biguint(BigUint::from_str("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507").unwrap());
    let py2 = Fp::get_fp_from_biguint(BigUint::from_str("2662903010277190920397318445793982934971948944000658264905514399707520226534504357969962973775649129045502516118218").unwrap());

    let sig: [u8;96] = sync_aggregate.sync_committee_signature.0.to_vec().try_into().expect("Incorrect signature length");
    let signature_points = Signature::from_bytes(&sig).unwrap();
    let q_x2 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(&signature_points.point.getx().to_string().split(",").collect::<Vec<&str>>()[0][1..].to_string()).unwrap())),
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(&signature_points.point.getx().to_string().split(",").collect::<Vec<&str>>()[1][..96].to_string()).unwrap())),
    ]);
    let q_y2 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(&signature_points.point.gety().to_string().split(",").collect::<Vec<&str>>()[0][1..].to_string()).unwrap())),
        Fp::get_fp_from_biguint(BigUint::from_bytes_be(&hex::decode(&signature_points.point.gety().to_string().split(",").collect::<Vec<&str>>()[1][..96].to_string()).unwrap())),
    ],);
    let q_z2 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
        Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
    ]);

    println!("calc_pairing_precomp stark 2");
    let (
        stark_pp2,
        proof_pp2,
        config_pp2
    ) = calc_pairing_precomp::<F, C, D>(q_x2, q_y2, q_z2);
    let recursive_pp2 = recursive_proof::<F, C, PpStark, C, D>(stark_pp2, proof_pp2.clone(), &config_pp2, true);

    println!("miller_loop stark 2");
    let (
        stark_ml2,
        proof_ml2,
        config_ml2,
    ) = miller_loop_main::<F, C, D>(px2, py2, q_x2, q_y2, q_z2);
    let recursive_ml2 = recursive_proof::<F, C, MlStark, C, D>(stark_ml2, proof_ml2.clone(), &config_ml2, true);
    
    let ml1_res = native::miller_loop(px1, py1, q_x1, q_y1, q_z1);
    let ml2_res = native::miller_loop(px2, py2, q_x2, q_y2, q_z2);
    println!("fp12_mul stark");
    let (
        stark_fp12_mul,
        proof_fp12_mul,
        config_fp12_mul,
    ) = fp12_mul_main::<F, C, D>(ml1_res, ml2_res);
    let recursive_fp12_mul = recursive_proof::<F, C, Fp12MulStark, C, D>(stark_fp12_mul, proof_fp12_mul.clone(), &config_fp12_mul, true);

    let final_exp_input = ml1_res * ml2_res;
    println!("final exponentiate stark");
    let (
        stark_final_exp,
        proof_final_exp,
        config_final_exp
    ) = final_exponentiate_main::<F, C, D>(final_exp_input);
    let recursive_final_exp = recursive_proof::<F, C, FeStark, C, D>(stark_final_exp, proof_final_exp, &config_final_exp, true);

    let msg = hex::decode("0x244aa8518b6781c70becf261b5ffd88c97bdd953ffe556b90e04f89ea7f6360f".split_at(2).1).unwrap();
    let prev_sync_committee_update = get_sync_committee_update_from_light_client_update_json_str(&routes,&prev_light_client_update_json_str).unwrap();
    let pks = prev_sync_committee_update.next_sync_committee.pubkeys.0
                                                                                    .iter()
                                                                                    .map(|i| {
                                                                                        // Assuming each inner vector has exactly 48 elements
                                                                                        let mut array = [0u8; 48];
                                                                                        array.copy_from_slice(&i.0[..48]);
                                                                                        array
                                                                                    })
                                                                                    .collect::<Vec<[u8; 48]>>();

    let (proof, verifier_only, common_data) = aggregate_recursive_proof::<F, C, C, D>(
        &msg,
        &sig,
        &pks,
        &bits,
        &recursive_pp1,
        &recursive_ml1,
        &recursive_pp2,
        &recursive_ml2,
        &recursive_fp12_mul,
        &recursive_final_exp,
        &recursive_ec,
    ).unwrap();
    let proof_bytes = proof.to_bytes();
    let verifier_bytes = verifier_only.to_bytes().unwrap();
    let common_bytes = common_data.to_bytes(&CustomGateSerializer).unwrap();
    std::fs::write("proof_with_pis.bin", &proof_bytes).unwrap();
    std::fs::write("verifier_only.bin", &verifier_bytes).unwrap();
    std::fs::write("common_data.bin", &common_bytes).unwrap();
}

fn recursive_proof<
    F: plonky2::hash::hash_types::RichField + plonky2::field::extension::Extendable<D>,
    C: GenericConfig<D, F = F>,
    S: starky::stark::Stark<F, D> + Copy,
    InnerC: GenericConfig<D, F = F>,
    const D: usize,
>(
    stark: S,
    inner_proof: starky::proof::StarkProofWithPublicInputs<F, InnerC, D>,
    inner_config: &StarkConfig,
    print_gate_counts: bool,
) -> ProofTuple<F, C, D>
where
    InnerC::Hasher: plonky2::plonk::config::AlgebraicHasher<F>,
{
    let circuit_config = plonky2::plonk::circuit_data::CircuitConfig::standard_recursion_config();
    let mut builder = plonky2::plonk::circuit_builder::CircuitBuilder::<F, D>::new(circuit_config);
    let mut pw = plonky2::iop::witness::PartialWitness::new();
    let degree_bits = inner_proof.proof.recover_degree_bits(inner_config);
    let pt = starky::recursive_verifier::add_virtual_stark_proof_with_pis(&mut builder, stark, inner_config, degree_bits);
    builder.register_public_inputs(&pt.public_inputs);
    starky::recursive_verifier::set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);
    starky::recursive_verifier::verify_stark_proof_circuit::<F, InnerC, S, D>(&mut builder, stark, pt, inner_config);

    if print_gate_counts {
        builder.print_gate_counts(0);
    }

    let data = builder.build::<C>();
    let s = Instant::now();
    let proof = data.prove(pw).unwrap();
    println!("time taken for plonky2 recursive proof {:?}", s.elapsed());
    data.verify(proof.clone()).unwrap();
    (proof, data.verifier_only, data.common)
}

type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

fn aggregate_recursive_proof<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F>,
    const D: usize,
>(
    msg: &[u8],
    sig: &[u8; SIG_LEN],
    pks: &[[u8; PUB_KEY_LEN]],
    bits: &[bool],
    inner_pp1: &ProofTuple<F, InnerC, D>,
    inner_ml1: &ProofTuple<F, InnerC, D>,
    inner_pp2: &ProofTuple<F, InnerC, D>,
    inner_ml2: &ProofTuple<F, InnerC, D>,
    inner_fp12m: &ProofTuple<F, InnerC, D>,
    inner_fe: &ProofTuple<F, InnerC, D>,
    inner_ec: &ProofTuple<F, InnerC, D>,
) -> Result<ProofTuple<F, C, D>>
where
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let config = CircuitConfig::standard_recursion_config();
    let (inner_proof_pp1, inner_vd_pp1, inner_cd_pp1) = inner_pp1;
    let (inner_proof_ml1, inner_vd_ml1, inner_cd_ml1) = inner_ml1;
    let (inner_proof_pp2, inner_vd_pp2, inner_cd_pp2) = inner_pp2;
    let (inner_proof_ml2, inner_vd_ml2, inner_cd_ml2) = inner_ml2;
    let (inner_proof_fp12m, inner_vd_fp12m, inner_cd_fp12m) = inner_fp12m;
    let (inner_proof_fe, inner_vd_fe, inner_cd_fe) = inner_fe;
    let (inner_proof_ec, inner_vd_ec, inner_cd_ec) = inner_ec;

    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let pt_pp1 = builder.add_virtual_proof_with_pis(inner_cd_pp1);
    let pt_ml1 = builder.add_virtual_proof_with_pis(inner_cd_ml1);
    let pt_pp2 = builder.add_virtual_proof_with_pis(inner_cd_pp2);
    let pt_ml2 = builder.add_virtual_proof_with_pis(inner_cd_ml2);
    let pt_fp12m = builder.add_virtual_proof_with_pis(inner_cd_fp12m);
    let pt_fe = builder.add_virtual_proof_with_pis(inner_cd_fe);
    let pt_ec = builder.add_virtual_proof_with_pis(inner_cd_ec);
  
    let msg_targets = builder.add_virtual_targets(msg.len());
    let sig_targets = builder.add_virtual_target_arr::<SIG_LEN>();
    let mut pk_targets = vec![];
    let mut bit_targets = vec![];
    for _ in 0..pks.len() {
        pk_targets.push(builder.add_virtual_target_arr::<PUB_KEY_LEN>());
        bit_targets.push(builder.add_virtual_bool_target_safe());
    }

    let hm = hash_to_curve(&mut builder, &msg_targets);
    let one = builder.one();
    let zero = builder.zero();
    for i in 0..N {
        builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::X0_PUBLIC_INPUTS_OFFSET + i], hm[0][0].limbs.get(i).unwrap_or(&U32Target(zero)).0);
        builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::X1_PUBLIC_INPUTS_OFFSET + i], hm[0][1].limbs.get(i).unwrap_or(&U32Target(zero)).0);
        builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::Y0_PUBLIC_INPUTS_OFFSET + i], hm[1][0].limbs.get(i).unwrap_or(&U32Target(zero)).0);
        builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::Y1_PUBLIC_INPUTS_OFFSET + i], hm[1][1].limbs.get(i).unwrap_or(&U32Target(zero)).0);
        builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::Z1_PUBLIC_INPUTS_OFFSET + i], zero);
        if i == 0 {
            builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::Z0_PUBLIC_INPUTS_OFFSET + i], one);
        } else {
            builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::Z0_PUBLIC_INPUTS_OFFSET + i], zero);
        }
    }

    for i in 0..68*3*24 {
        builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::ELL_COEFFS_PUBLIC_INPUTS_OFFSET + i], pt_ml1.public_inputs[miller_loop::PIS_ELL_COEFFS_OFFSET + i]);
    }

    for idx in 0..pk_targets.len() {
        let pk_point_x = BigUintTarget {
            limbs: (0..N).into_iter().map(|i| U32Target(pt_ec.public_inputs[ecc_aggregate::POINTS + idx*24 + i])).collect(),
        };
        let pk_point_y = BigUintTarget {
            limbs: (0..N).into_iter().map(|i| U32Target(pt_ec.public_inputs[ecc_aggregate::POINTS + idx*24 + 12 + i])).collect(),
        };
        builder.connect(pt_ec.public_inputs[ecc_aggregate::BITS + idx], bit_targets[idx].target);
        let pk_point = [pk_point_x, pk_point_y];
        pk_point_check(&mut builder, &pk_point, &pk_targets[idx]);
    }

    for i in 0..12 {
        builder.connect(pt_ec.public_inputs[ecc_aggregate::RES + i], pt_ml1.public_inputs[miller_loop::PIS_PX_OFFSET + i]);
    }
    for i in 0..12 {
        builder.connect(pt_ec.public_inputs[ecc_aggregate::RES + i + 12], pt_ml1.public_inputs[miller_loop::PIS_PY_OFFSET + i]);
    }

    for i in 0..24*3*2 {
        builder.connect(pt_ml1.public_inputs[miller_loop::PIS_RES_OFFSET + i], pt_fp12m.public_inputs[fp12_mul::PIS_INPUT_X_OFFSET + i]);
    }

    let sig_point_x0 = BigUintTarget {
        limbs: (0..N).into_iter().map(|i| U32Target(pt_pp2.public_inputs[calc_pairing_precomp::X0_PUBLIC_INPUTS_OFFSET + i])).collect(),
    };
    let sig_point_x1 = BigUintTarget {
        limbs: (0..N).into_iter().map(|i| U32Target(pt_pp2.public_inputs[calc_pairing_precomp::X1_PUBLIC_INPUTS_OFFSET + i])).collect(),
    };
    let sig_point_y0 = BigUintTarget {
        limbs: (0..N).into_iter().map(|i| U32Target(pt_pp2.public_inputs[calc_pairing_precomp::Y0_PUBLIC_INPUTS_OFFSET + i])).collect(),
    };
    let sig_point_y1 = BigUintTarget {
        limbs: (0..N).into_iter().map(|i| U32Target(pt_pp2.public_inputs[calc_pairing_precomp::Y1_PUBLIC_INPUTS_OFFSET + i])).collect(),
    };
    for i in 0..N {
        if i == 0 {
            builder.connect(pt_pp2.public_inputs[calc_pairing_precomp::Z0_PUBLIC_INPUTS_OFFSET + i], one);
        } else {
            builder.connect(pt_pp2.public_inputs[calc_pairing_precomp::Z0_PUBLIC_INPUTS_OFFSET + i], zero);
        }
        builder.connect(pt_pp2.public_inputs[calc_pairing_precomp::Z1_PUBLIC_INPUTS_OFFSET + i], zero);
    }
    let sig_point = [[sig_point_x0, sig_point_x1], [sig_point_y0, sig_point_y1]];
    signature_point_check(&mut builder, &sig_point, &sig_targets);

    for i in 0..68*3*24 {
        builder.connect(pt_pp2.public_inputs[calc_pairing_precomp::ELL_COEFFS_PUBLIC_INPUTS_OFFSET + i], pt_ml2.public_inputs[miller_loop::PIS_ELL_COEFFS_OFFSET + i]);
    }

    let neg_generator_x = builder.constant_biguint(&BigUint::from_str("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507").unwrap());
    let neg_generator_y = builder.constant_biguint(&BigUint::from_str("2662903010277190920397318445793982934971948944000658264905514399707520226534504357969962973775649129045502516118218").unwrap());
    for i in 0..N {
        builder.connect(pt_ml2.public_inputs[miller_loop::PIS_PX_OFFSET + i], neg_generator_x.limbs[i].0);
        builder.connect(pt_ml2.public_inputs[miller_loop::PIS_PY_OFFSET + i], neg_generator_y.limbs[i].0);
    }

    for i in 0..24*3*2 {
        builder.connect(pt_ml2.public_inputs[miller_loop::PIS_RES_OFFSET + i], pt_fp12m.public_inputs[fp12_mul::PIS_INPUT_Y_OFFSET + i]);
    }

    for i in 0..24*3*2 {
        builder.connect(pt_fp12m.public_inputs[fp12_mul::PIS_OUTPUT_OFFSET + i], pt_fe.public_inputs[final_exponentiate::PIS_INPUT_OFFSET + i]);
    }

    for i in 0..24*3*2 {
        let val = if i == 0 {
            builder.one()
        } else {
            builder.zero()
        };
        builder.connect(pt_fe.public_inputs[final_exponentiate::PIS_OUTPUT_OFFSET + i], val);
    }

    let inner_data_pp1 = builder.add_virtual_verifier_data(inner_cd_pp1.config.fri_config.cap_height);
    let inner_data_ml1 = builder.add_virtual_verifier_data(inner_cd_ml1.config.fri_config.cap_height);
    let inner_data_pp2 = builder.add_virtual_verifier_data(inner_cd_pp2.config.fri_config.cap_height);
    let inner_data_ml2 = builder.add_virtual_verifier_data(inner_cd_ml2.config.fri_config.cap_height);
    let inner_data_fp12m = builder.add_virtual_verifier_data(inner_cd_fp12m.config.fri_config.cap_height);
    let inner_data_fe = builder.add_virtual_verifier_data(inner_cd_fe.config.fri_config.cap_height);
    let inner_data_ec = builder.add_virtual_verifier_data(inner_cd_ec.config.fri_config.cap_height);

    builder.verify_proof::<InnerC>(&pt_pp1, &inner_data_pp1, inner_cd_pp1);
    builder.verify_proof::<InnerC>(&pt_ml1, &inner_data_ml1, inner_cd_ml1);
    builder.verify_proof::<InnerC>(&pt_pp2, &inner_data_pp2, inner_cd_pp2);
    builder.verify_proof::<InnerC>(&pt_ml2, &inner_data_ml2, inner_cd_ml2);
    builder.verify_proof::<InnerC>(&pt_fp12m, &inner_data_fp12m, inner_cd_fp12m);
    builder.verify_proof::<InnerC>(&pt_fe, &inner_data_fe, inner_cd_fe);
    builder.verify_proof::<InnerC>(&pt_ec, &inner_data_ec, inner_cd_ec);

    builder.register_public_inputs(&msg_targets);
    builder.register_public_inputs(&sig_targets);
    for i in 0..pk_targets.len() {
        builder.register_public_inputs(&pk_targets[i]);
        builder.register_public_input(bit_targets[i].target);
    }
    builder.print_gate_counts(0);

    let data = builder.build::<C>();

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&pt_pp1, inner_proof_pp1);
    pw.set_verifier_data_target(&inner_data_pp1, inner_vd_pp1);

    pw.set_proof_with_pis_target(&pt_ml1, inner_proof_ml1);
    pw.set_verifier_data_target(&inner_data_ml1, inner_vd_ml1);

    pw.set_proof_with_pis_target(&pt_pp2, inner_proof_pp2);
    pw.set_verifier_data_target(&inner_data_pp2, inner_vd_pp2);

    pw.set_proof_with_pis_target(&pt_ml2, inner_proof_ml2);
    pw.set_verifier_data_target(&inner_data_ml2, inner_vd_ml2);

    pw.set_proof_with_pis_target(&pt_fp12m, inner_proof_fp12m);
    pw.set_verifier_data_target(&inner_data_fp12m, inner_vd_fp12m);

    pw.set_proof_with_pis_target(&pt_fe, inner_proof_fe);
    pw.set_verifier_data_target(&inner_data_fe, inner_vd_fe);

    pw.set_proof_with_pis_target(&pt_ec, inner_proof_ec);
    pw.set_verifier_data_target(&inner_data_ec, inner_vd_ec);

    let msg_f = msg.iter().map(|i| F::from_canonical_u8(*i)).collect::<Vec<F>>();
    let sig_f = sig.iter().map(|i| F::from_canonical_u8(*i)).collect::<Vec<F>>();
    let mut pks_f = vec![];
    for i in 0..pks.len() {
        let pk_f = pks[i].iter().map(|i| F::from_canonical_u8(*i)).collect::<Vec<F>>();
        pks_f.push(pk_f);
    }
    pw.set_target_arr(&msg_targets, &msg_f);
    pw.set_target_arr(&sig_targets, &sig_f);
    for i in 0..pk_targets.len() {
        pw.set_target_arr(&pk_targets[i], &pks_f[i]);
        pw.set_bool_target(bit_targets[i], bits[i]);
    }
    let mut timing = TimingTree::new("prove", Level::Debug);
    let s = Instant::now();
    let proof = plonky2_prove::<F, C, D>(&data.prover_only, &data.common, pw, &mut timing)?;
    println!("Time taken for aggregate recusrive proof {:?}", s.elapsed());
    timing.print();

    data.verify(proof.clone())?;

    Ok((proof, data.verifier_only, data.common))
}

fn main() {
    env_logger::init();
    std::thread::Builder::new().spawn(|| {
        aggregate_proof();
    }).unwrap().join().unwrap();
    return;
}
