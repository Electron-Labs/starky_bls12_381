use num_bigint::BigUint;
use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, util::timing::{TimingTree, self}};
use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
use plonky2::field::types::Field;
use crate::{native::{get_u32_vec_from_literal_24, modulus, get_u32_vec_from_literal, Fp2, Fp, mul_Fp2, Fp6, mul_Fp6, Fp12}, calc_pairing_precomp::{PairingPrecompStark, ELL_COEFFS_PUBLIC_INPUTS_OFFSET}, miller_loop::MillerLoopStark};
use starky::util::trace_rows_to_poly_values;
use std::time::Instant;


pub mod native;
pub mod big_arithmetic;
pub mod fp;
pub mod fp2;
pub mod fp6;
pub mod fp12;
pub mod utils;
pub mod calc_pairing_precomp;
pub mod miller_loop;

fn calc_pairing_precomp() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = PairingPrecompStark<F, D>;

    let mut config = StarkConfig::standard_fast_config();
    config.fri_config.rate_bits = 2;
    let stark = S::new(1024);
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
    let trace = stark.generate_trace([x, x], [y, y], [z, z]);
    let ell_coeffs = native::calc_pairing_precomp(Fp2([Fp(x), Fp(x)]), Fp2([Fp(y), Fp(y)]), Fp2([Fp(z), Fp(z)]));
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
    // println!("constraint_degree: {:?}", stark.constraint_degree());
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let t = Instant::now();
    let proof = prove::<F, C, S, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    );
    println!("time taken {:?}", t.elapsed());
    verify_stark_proof(stark, proof.unwrap(), &config).unwrap();
}

fn miller_loop_main() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = MillerLoopStark<F, D>;

    let config = StarkConfig::standard_fast_config();
    let stark = S::new(1024);
    let x = Fp([1550366109, 1913070572, 760847606, 999580752, 3273422733, 182645169, 1634881460, 1043400770, 1526865253, 1101868890, 3712845450, 132602617]);
    let y = Fp([673719994, 1835763041, 382898653, 2031122452, 723494459, 2514182158, 1528654322, 3691097491, 369601280, 1847427497, 748256393, 201500165]);
    let q_x = Fp2([Fp([1115400077, 734036635, 2658976793, 3446373348, 3797461211, 2799729988, 1086715089, 1766116042, 3720719530, 4214563288, 2211874409, 287824937]), Fp([4070035387, 3598430679, 2371795623, 2598602036, 314293284, 3104159902, 3828298491, 1770882328, 1026148559, 2003704675, 804131021, 382850433])]);
    let q_y = Fp2([Fp([3944640261, 440162500, 3767697757, 767512216, 3185360355, 1355179671, 2310853452, 2890628660, 2539693039, 3306767406, 473197245, 198293246]), Fp([920955909, 775806582, 2117093864, 286632291, 2248224021, 4208799968, 2272086148, 4009382258, 291945614, 2017047933, 1541154483, 220533456])]);
    let q_z = Fp2([Fp([2780158026, 2572579871, 3558563268, 1947800745, 1784566622, 912901049, 1766882808, 1286945791, 2204464567, 728083964, 3377958885, 227852528]), Fp([1492897660, 2845803056, 3990009560, 3332584519, 1144621723, 1049137482, 2386536189, 2220905202, 28647458, 3875714686, 701911767, 391244403])]);
    let s = Instant::now();
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
    let trace = stark.generate_trace(x, y, ell_coeffs);
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let proof = prove::<F, C, S, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    );
    println!("Time taken to gen proof {:?}", s.elapsed());
    verify_stark_proof(stark, proof.unwrap(), &config).unwrap();
}

fn test_stark_circuit_constraints() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = MillerLoopStark<F, D>;

    let stark = S::new(1024);
    starky::stark_testing::test_stark_circuit_constraints::<F, C, S, D>(stark).unwrap();
}

fn test_recursive_stark_verifier() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = MillerLoopStark<F, D>;

    let config = StarkConfig::standard_fast_config();
    let stark = S::new(1024);
    let x = Fp([1550366109, 1913070572, 760847606, 999580752, 3273422733, 182645169, 1634881460, 1043400770, 1526865253, 1101868890, 3712845450, 132602617]);
    let y = Fp([673719994, 1835763041, 382898653, 2031122452, 723494459, 2514182158, 1528654322, 3691097491, 369601280, 1847427497, 748256393, 201500165]);
    let q_x = Fp2([Fp([1115400077, 734036635, 2658976793, 3446373348, 3797461211, 2799729988, 1086715089, 1766116042, 3720719530, 4214563288, 2211874409, 287824937]), Fp([4070035387, 3598430679, 2371795623, 2598602036, 314293284, 3104159902, 3828298491, 1770882328, 1026148559, 2003704675, 804131021, 382850433])]);
    let q_y = Fp2([Fp([3944640261, 440162500, 3767697757, 767512216, 3185360355, 1355179671, 2310853452, 2890628660, 2539693039, 3306767406, 473197245, 198293246]), Fp([920955909, 775806582, 2117093864, 286632291, 2248224021, 4208799968, 2272086148, 4009382258, 291945614, 2017047933, 1541154483, 220533456])]);
    let q_z = Fp2([Fp([2780158026, 2572579871, 3558563268, 1947800745, 1784566622, 912901049, 1766882808, 1286945791, 2204464567, 728083964, 3377958885, 227852528]), Fp([1492897660, 2845803056, 3990009560, 3332584519, 1144621723, 1049137482, 2386536189, 2220905202, 28647458, 3875714686, 701911767, 391244403])]);
    let s = Instant::now();
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
    let trace = stark.generate_trace(x, y, ell_coeffs);
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let proof = prove::<F, C, S, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    ).unwrap();
    println!("Time taken to gen proof {:?}", s.elapsed());
    verify_stark_proof(stark, proof.clone(), &config).unwrap();

    recursive_proof::<F, C, S, C, D>(stark, proof, &config, true);
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
)
where
    InnerC::Hasher: plonky2::plonk::config::AlgebraicHasher<F>,
{
    let circuit_config = plonky2::plonk::circuit_data::CircuitConfig::standard_recursion_config();
    let mut builder = plonky2::plonk::circuit_builder::CircuitBuilder::<F, D>::new(circuit_config);
    let mut pw = plonky2::iop::witness::PartialWitness::new();
    let degree_bits = inner_proof.proof.recover_degree_bits(inner_config);
    let pt = starky::recursive_verifier::add_virtual_stark_proof_with_pis(&mut builder, stark, inner_config, degree_bits);
    starky::recursive_verifier::set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);
    starky::recursive_verifier::verify_stark_proof_circuit::<F, InnerC, S, D>(&mut builder, stark, pt, inner_config);

    if print_gate_counts {
        builder.print_gate_counts(0);
    }

    let data = builder.build::<C>();
    let s = Instant::now();
    let proof = data.prove(pw).unwrap();
    println!("plonky2 recursive proof in {:?}", s.elapsed());
    data.verify(proof).unwrap();
}

fn main() {
    // std::thread::Builder::new().spawn(|| {
    //    test_recursive_stark_verifier();
    //    test_stark_circuit_constraints();
    // }).unwrap().join().unwrap();
    // return;
    let test_fp_which: usize = 1;
    if test_fp_which == 0 {
        calc_pairing_precomp();
    } else if test_fp_which == 1 {
        miller_loop_main();
    }
}
