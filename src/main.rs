use num_bigint::BigUint;
use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, util::timing::{TimingTree, self}};
use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
use plonky2::field::types::Field;
use crate::{native::{get_u32_vec_from_literal_24, modulus, get_u32_vec_from_literal, Fp2, Fp, mul_Fp2}, fp_mult_starky::FpMultiplicationStark, fp2_mult_starky::Fp2MultiplicationStark, calc_pairing_precomp::PairingPrecompStark};
use starky::util::trace_rows_to_poly_values;
use std::time::Instant;


pub mod native;
pub mod big_arithmetic;
pub mod fp_mult_starky;
pub mod fp2_mult_starky;
pub mod calc_pairing_precomp;

pub const PUBLIC_INPUTS: usize = 72;

fn fp2_main() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = Fp2MultiplicationStark<F, D>;

    let config = StarkConfig::standard_fast_config();
    let mut stark = S::new(16);
    let s_ = stark.clone();
    let x: [u32; 12] = [
        1550366109, 1913070572, 760847606, 999580752, 3273422733, 182645169, 1634881460,
        1043400770, 1526865253, 1101868890, 3712845450, 132602617,
    ];
    let y: [u32; 12] = [
        3621225457, 1284733598, 2592173602, 2778433514, 3415298024, 3512038034, 2556930252,
        2289409521, 759431638, 3707643405, 216427024, 234777573,
    ];
    let x_fp2 = Fp2([Fp(x); 2]);
    let y_fp2 = Fp2([Fp(y); 2]);
    let x_y_product_fp2 = mul_Fp2(x_fp2, y_fp2);
    let x_y_product = [x_y_product_fp2.0[0].0, x_y_product_fp2.0[1].0];
    let s = Instant::now();
    stark.generate_trace([x, x], [y, y]);
    let mut public_inputs = Vec::new();
    for e in x.iter().chain(x.iter()).chain(y.iter()).chain(y.iter()) {
        public_inputs.push(F::from_canonical_u32(e.clone()));
    }
    for e in x_y_product.iter().flatten() {
        public_inputs.push(F::from_canonical_u32(e.clone()));
    }
    assert_eq!(public_inputs.len(), PUBLIC_INPUTS);
    let trace_poly_values = trace_rows_to_poly_values(stark.trace.clone());
    let proof = prove::<F, C, S, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    );
    println!("Time taken to gen proof {:?}", s.elapsed());
    verify_stark_proof(s_, proof.unwrap(), &config).unwrap();
}

fn fp1_main() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = FpMultiplicationStark<F, D>;

    let mut config = StarkConfig::standard_fast_config();
    let mut stark = S::new(16);
    let s_ = stark.clone();
    let x: [u32; 12] = [1550366109, 1913070572, 760847606, 999580752, 3273422733, 182645169, 1634881460, 1043400770, 1526865253, 1101868890, 3712845450, 132602617];
    let y: [u32; 12] = [3621225457, 1284733598, 2592173602, 2778433514, 3415298024, 3512038034, 2556930252, 2289409521, 759431638, 3707643405, 216427024, 234777573];
    let product_x_y: [u32; 12] =  get_u32_vec_from_literal((BigUint::new(x.to_vec())*BigUint::new(y.to_vec()))%modulus());
    let trace = stark.generate_trace(x, y);
    let mut pis = Vec::new();
    for e in x.iter().chain(y.iter()).chain(product_x_y.iter()) {
        pis.push(F::from_canonical_u32(e.clone()));
    }
    let trace_poly_values = trace_rows_to_poly_values(trace.clone());
    // stark.quotient_degree_factor()
    let t = Instant::now();
    let proof= prove::<F, C, S, D>(
        stark,
        &config,
        trace_poly_values,
        &pis,
        &mut TimingTree::default(),
    ); 
    println!("proof gen took {:?}", t.elapsed().as_millis());
    verify_stark_proof(s_, proof.unwrap(), &config).unwrap();
}

fn calc_pairing_precomp() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = PairingPrecompStark<F, D>;

    let config = StarkConfig::standard_fast_config();
    let mut stark = S::new(1024);
    let s_ = stark.clone();
    let x: [u32; 12] = [
        1550366109, 1913070572, 760847606, 999580752, 3273422733, 182645169, 1634881460,
        1043400770, 1526865253, 1101868890, 3712845450, 132602617,
    ];
    let y: [u32; 12] = [
        3621225457, 1284733598, 2592173602, 2778433514, 3415298024, 3512038034, 2556930252,
        2289409521, 759431638, 3707643405, 216427024, 234777573,
    ];
    let z: [u32; 12] = [
        3621225457, 1284733598, 2592173602, 2778433514, 3415298024, 3512038034, 2556930252,
        2289409521, 759431638, 3707643405, 216427024, 234777573,
    ];
    stark.generate_trace([x, x], [y, y], [z, z]);
    let mut public_inputs = Vec::new();
    for e in x.iter().chain(x.iter()) {
        public_inputs.push(F::from_canonical_u32(e.clone()));
    }
    for e in y.iter().chain(y.iter()) {
        public_inputs.push(F::from_canonical_u32(e.clone()));
    }
    for e in z.iter().chain(z.iter()) {
        public_inputs.push(F::from_canonical_u32(e.clone()));
    }
    assert_eq!(public_inputs.len(), PUBLIC_INPUTS);
    // println!("constraint_degree: {:?}", stark.constraint_degree());
    let trace_poly_values = trace_rows_to_poly_values(stark.trace.clone());
    let t = Instant::now();
    let proof = prove::<F, C, S, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    );
    println!("time taken {:?}", t.elapsed());
    verify_stark_proof(s_, proof.unwrap(), &config).unwrap();
}

fn main() {
    let test_fp_which: usize = 3;
    if test_fp_which == 1 {
        fp1_main();
    } else if test_fp_which == 2 {
        fp2_main();
    } else if test_fp_which == 3 {
        calc_pairing_precomp();
    }
}
