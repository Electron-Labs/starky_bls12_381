use num_bigint::BigUint;
use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, util::timing::{TimingTree, self}};
use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
use plonky2::field::types::Field;
use crate::{native::{get_u32_vec_from_literal_24, modulus, get_u32_vec_from_literal}, fp_mult_starky::FpMultiplicationStark};
use starky::util::trace_rows_to_poly_values;
use std::time::Instant;

pub mod native;
pub mod big_arithmetic;
pub mod fp_mult_starky;
fn main() {
    // println!("Hello, world!");
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
