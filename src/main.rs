use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, util::timing::TimingTree};
use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
use crate::{native::{Fp2, Fp, Fp12}, calc_pairing_precomp::PairingPrecompStark, miller_loop::MillerLoopStark, final_exponentiate::FinalExponentiateStark, fp12_mul::FP12MulStark};
use starky::util::trace_rows_to_poly_values;
use std::time::Instant;

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

pub mod native;
pub mod big_arithmetic;
pub mod fp;
pub mod fp2;
pub mod fp6;
pub mod fp12;
pub mod utils;
pub mod calc_pairing_precomp;
pub mod miller_loop;
pub mod final_exponentiate;
pub mod fp12_mul;

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

fn aggregate_proof() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    
    type PpStark = PairingPrecompStark<F, D>;
    type MlStark = MillerLoopStark<F, D>;
    type Fp12MulStark = FP12MulStark<F, D>;
    type FeStark = FinalExponentiateStark<F, D>;

    let px1 = Fp([1550366109, 1913070572, 760847606, 999580752, 3273422733, 182645169, 1634881460, 1043400770, 1526865253, 1101868890, 3712845450, 132602617]);
    let py1 = Fp([673719994, 1835763041, 382898653, 2031122452, 723494459, 2514182158, 1528654322, 3691097491, 369601280, 1847427497, 748256393, 201500165]);
    let q_x1 = Fp2([Fp([1115400077, 734036635, 2658976793, 3446373348, 3797461211, 2799729988, 1086715089, 1766116042, 3720719530, 4214563288, 2211874409, 287824937]), Fp([4070035387, 3598430679, 2371795623, 2598602036, 314293284, 3104159902, 3828298491, 1770882328, 1026148559, 2003704675, 804131021, 382850433])]);
    let q_y1 = Fp2([Fp([3944640261, 440162500, 3767697757, 767512216, 3185360355, 1355179671, 2310853452, 2890628660, 2539693039, 3306767406, 473197245, 198293246]), Fp([920955909, 775806582, 2117093864, 286632291, 2248224021, 4208799968, 2272086148, 4009382258, 291945614, 2017047933, 1541154483, 220533456])]);
    let q_z1 = Fp2([Fp([2780158026, 2572579871, 3558563268, 1947800745, 1784566622, 912901049, 1766882808, 1286945791, 2204464567, 728083964, 3377958885, 227852528]), Fp([1492897660, 2845803056, 3990009560, 3332584519, 1144621723, 1049137482, 2386536189, 2220905202, 28647458, 3875714686, 701911767, 391244403])]);

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

    let px2 = Fp([3676489403, 4214943754, 4185529071, 1817569343, 387689560, 2706258495, 2541009157, 3278408783, 1336519695, 647324556, 832034708, 401724327]);
    let py2 = Fp([1187375073, 212476713, 2726857444, 3493644100, 738505709, 14358731, 3587181302, 4243972245, 1948093156, 2694721773, 3819610353, 146011265]);
    let q_x2 = Fp2([Fp([4072319491, 2776432055, 3207673906, 2931747336, 1670239197, 3780742951, 1625939546, 254790919, 1410949613, 3751257484, 1223867190, 286022738]), Fp([660700420, 4016548472, 256895237, 3552949192, 2391116264, 3365261990, 315457157, 2388449610, 215765303, 656720509, 3675306585, 304289727])]);
    let q_y2 = Fp2([Fp([3291452691, 1526698400, 123085972, 4217256013, 2390597986, 3622429380, 1791215328, 2878530825, 3131550138, 3116253669, 3504636512, 151829271]), Fp([4123265126, 2752013218, 1556720399, 386948539, 3643514185, 2039427681, 3467442232, 2876818448, 3322584909, 2011252300, 838048598, 284195453])]);
    let q_z2 = Fp2([Fp([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), Fp([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]);

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

    aggregate_recursive_proof::<F, C, C, D>(
        &recursive_pp1,
        &recursive_ml1,
        &recursive_pp2,
        &recursive_ml2,
        &recursive_fp12_mul,
        &recursive_final_exp,
    ).unwrap();
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
    inner_pp1: &ProofTuple<F, InnerC, D>,
    inner_ml1: &ProofTuple<F, InnerC, D>,
    inner_pp2: &ProofTuple<F, InnerC, D>,
    inner_ml2: &ProofTuple<F, InnerC, D>,
    inner_fp12m: &ProofTuple<F, InnerC, D>,
    inner_fe: &ProofTuple<F, InnerC, D>,
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

    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let pt_pp1 = builder.add_virtual_proof_with_pis(inner_cd_pp1);
    let pt_ml1 = builder.add_virtual_proof_with_pis(inner_cd_ml1);
    let pt_pp2 = builder.add_virtual_proof_with_pis(inner_cd_pp2);
    let pt_ml2 = builder.add_virtual_proof_with_pis(inner_cd_ml2);
    let pt_fp12m = builder.add_virtual_proof_with_pis(inner_cd_fp12m);
    let pt_fe = builder.add_virtual_proof_with_pis(inner_cd_fe);

    for i in 0..68*3*24 {
        builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::ELL_COEFFS_PUBLIC_INPUTS_OFFSET + i], pt_ml1.public_inputs[miller_loop::PIS_ELL_COEFFS_OFFSET + i]);
    }

    for i in 0..24*3*2 {
        builder.connect(pt_ml1.public_inputs[miller_loop::PIS_RES_OFFSET + i], pt_fp12m.public_inputs[fp12_mul::PIS_INPUT_X_OFFSET + i]);
    }

    for i in 0..68*3*24 {
        builder.connect(pt_pp2.public_inputs[calc_pairing_precomp::ELL_COEFFS_PUBLIC_INPUTS_OFFSET + i], pt_ml2.public_inputs[miller_loop::PIS_ELL_COEFFS_OFFSET + i]);
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

    builder.verify_proof::<InnerC>(&pt_pp1, &inner_data_pp1, inner_cd_pp1);
    builder.verify_proof::<InnerC>(&pt_ml1, &inner_data_ml1, inner_cd_ml1);
    builder.verify_proof::<InnerC>(&pt_pp2, &inner_data_pp2, inner_cd_pp2);
    builder.verify_proof::<InnerC>(&pt_ml2, &inner_data_ml2, inner_cd_ml2);
    builder.verify_proof::<InnerC>(&pt_fp12m, &inner_data_fp12m, inner_cd_fp12m);
    builder.verify_proof::<InnerC>(&pt_fe, &inner_data_fe, inner_cd_fe);
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

    let mut timing = TimingTree::new("prove", Level::Debug);
    let s = Instant::now();
    let proof = plonky2_prove::<F, C, D>(&data.prover_only, &data.common, pw, &mut timing)?;
    println!("Time taken for aggregaet recusrive proof {:?}", s.elapsed());
    timing.print();

    data.verify(proof.clone())?;

    Ok((proof, data.verifier_only, data.common))
}

fn main() {
    std::thread::Builder::new().spawn(|| {
        aggregate_proof();
    }).unwrap().join().unwrap();
    return;
}
