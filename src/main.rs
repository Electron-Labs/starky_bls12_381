use num_bigint::BigUint;
use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, util::timing::{TimingTree, self}};
use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
use plonky2::field::types::Field;
use crate::{native::{get_u32_vec_from_literal_24, modulus, get_u32_vec_from_literal, Fp2, Fp, mul_Fp2, Fp6, mul_Fp6, Fp12}, calc_pairing_precomp::{PairingPrecompStark, ELL_COEFFS_PUBLIC_INPUTS_OFFSET}, miller_loop::MillerLoopStark, final_exponentiate::FinalExponentiateStark};
use starky::util::trace_rows_to_poly_values;
use std::time::Instant;

use plonky2::plonk::circuit_data::{CircuitConfig, CommonCircuitData, VerifierOnlyCircuitData};
use plonky2::plonk::proof::{CompressedProofWithPublicInputs, ProofWithPublicInputs};
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
    // println!("constraint_degree: {:?}", stark.constraint_degree());
    let trace_poly_values = trace_rows_to_poly_values(trace);
    let t = Instant::now();
    let proof = prove::<F, C, PairingPrecompStark<F, D>, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    ).unwrap();
    println!("time taken {:?}", t.elapsed());
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
    println!("Time taken to gen proof {:?}", s.elapsed());
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
    println!("Time taken to gen proof {:?}", s.elapsed());
    verify_stark_proof(stark, proof.clone(), &config).unwrap();
    (stark, proof, config)
}

fn test_stark_circuit_constraints() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = FinalExponentiateStark<F, D>;

    let stark = S::new(8192);
    starky::stark_testing::test_stark_circuit_constraints::<F, C, S, D>(stark).unwrap();
}

fn test_recursive_stark_verifier() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = FinalExponentiateStark<F, D>;

    let mut config = StarkConfig::standard_fast_config();
    config.fri_config.rate_bits = 2;
    let stark = S::new(8192);
    let s = Instant::now();
    let x = Fp12([Fp([3688549023, 1461121002, 158795132, 3031927502, 213444395, 4286532434, 2430134266, 3543104615, 1291488635, 3435685873, 4037455674, 79410575]), Fp([1360882579, 3002343476, 3086261481, 844031790, 3247736081, 1476716566, 2285276612, 2128837429, 3999081699, 4034708995, 1714901244, 52662165]), Fp([4104185655, 3701245790, 808982471, 2474474870, 86883540, 2861754577, 892037001, 426313854, 351740683, 2973656712, 2938329451, 98989231]), Fp([1750337445, 1055423710, 3314636215, 3832606429, 682495303, 3837288901, 3323765171, 317766258, 263941221, 4122823463, 817092141, 399622891]), Fp([2471624410, 3446467705, 2404303712, 4024275285, 3482111337, 2794822952, 3019262746, 126898360, 1076123014, 2901504703, 3932319379, 98921494]), Fp([2110261208, 2032742098, 990038150, 1352002937, 3987858999, 2819343369, 3282554204, 766147331, 208424639, 1602982609, 4112224585, 236233458]), Fp([2046547795, 3173960576, 2639561839, 1364192507, 1671233573, 2391309894, 3000205425, 1179450741, 3256341155, 3289801138, 1673317021, 168965912]), Fp([993521759, 35789000, 2528933762, 1397651268, 1549073333, 728869112, 2818328447, 3376956733, 4125103710, 3410833193, 3702323277, 402097749]), Fp([1613123474, 1843683341, 870050044, 2560600706, 933520115, 916747666, 4021709957, 20791057, 516247948, 3820524631, 3267700533, 122227566]), Fp([3600146516, 2812057600, 4150243859, 210373455, 465523258, 2359663667, 2064799726, 1552807009, 494361983, 2866737666, 172560447, 37672107]), Fp([13226053, 1019983919, 546396615, 4251229931, 250632233, 654320493, 1352696718, 2083058924, 1058634822, 2809138592, 900633632, 353005311]), Fp([340295756, 388460180, 1763111897, 2809758930, 1065140740, 2216989682, 2359308769, 1641074723, 1795030663, 945477827, 911995824, 168338922])]);
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
    let proof = prove::<F, C, S, D>(
        stark,
        &config,
        trace_poly_values,
        &public_inputs,
        &mut TimingTree::default(),
    ).unwrap();
    println!("Time taken to gen proof {:?}", s.elapsed());
    verify_stark_proof(stark, proof.clone(), &config).unwrap();

    let proof_tuple = recursive_proof::<F, C, S, C, D>(stark, proof, &config, true);
}

fn combine_proofs_stark() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    
    type S_PP = PairingPrecompStark<F, D>;
    type S_ML = MillerLoopStark<F, D>;

    let px1 = Fp([1550366109, 1913070572, 760847606, 999580752, 3273422733, 182645169, 1634881460, 1043400770, 1526865253, 1101868890, 3712845450, 132602617]);
    let py1 = Fp([673719994, 1835763041, 382898653, 2031122452, 723494459, 2514182158, 1528654322, 3691097491, 369601280, 1847427497, 748256393, 201500165]);
    let q_x1 = Fp2([Fp([1115400077, 734036635, 2658976793, 3446373348, 3797461211, 2799729988, 1086715089, 1766116042, 3720719530, 4214563288, 2211874409, 287824937]), Fp([4070035387, 3598430679, 2371795623, 2598602036, 314293284, 3104159902, 3828298491, 1770882328, 1026148559, 2003704675, 804131021, 382850433])]);
    let q_y1 = Fp2([Fp([3944640261, 440162500, 3767697757, 767512216, 3185360355, 1355179671, 2310853452, 2890628660, 2539693039, 3306767406, 473197245, 198293246]), Fp([920955909, 775806582, 2117093864, 286632291, 2248224021, 4208799968, 2272086148, 4009382258, 291945614, 2017047933, 1541154483, 220533456])]);
    let q_z1 = Fp2([Fp([2780158026, 2572579871, 3558563268, 1947800745, 1784566622, 912901049, 1766882808, 1286945791, 2204464567, 728083964, 3377958885, 227852528]), Fp([1492897660, 2845803056, 3990009560, 3332584519, 1144621723, 1049137482, 2386536189, 2220905202, 28647458, 3875714686, 701911767, 391244403])]);

    println!("pp1");
    let (
        stark_pp1,
        proof_pp1,
        config_pp1
    ) = calc_pairing_precomp(q_x1, q_y1, q_z1);
    let recursive_pp1 = recursive_proof::<F, C, S_PP, C, D>(stark_pp1, proof_pp1.clone(), &config_pp1, true);

    // println!("ml1");
    // let (
    //     stark_ml1,
    //     proof_ml1,
    //     config_ml1,
    // ) = miller_loop_main(px1, py1, q_x1, q_y1, q_z1);
    // let recursive_ml1 = recursive_proof::<F, C, S_ML, C, D>(stark_ml1, proof_ml1.clone(), &config_ml1, true);

    let px2 = Fp([3676489403, 4214943754, 4185529071, 1817569343, 387689560, 2706258495, 2541009157, 3278408783, 1336519695, 647324556, 832034708, 401724327]);
    let py2 = Fp([1187375073, 212476713, 2726857444, 3493644100, 738505709, 14358731, 3587181302, 4243972245, 1948093156, 2694721773, 3819610353, 146011265]);
    let q_x2 = Fp2([Fp([4072319491, 2776432055, 3207673906, 2931747336, 1670239197, 3780742951, 1625939546, 254790919, 1410949613, 3751257484, 1223867190, 286022738]), Fp([660700420, 4016548472, 256895237, 3552949192, 2391116264, 3365261990, 315457157, 2388449610, 215765303, 656720509, 3675306585, 304289727])]);
    let q_y2 = Fp2([Fp([3291452691, 1526698400, 123085972, 4217256013, 2390597986, 3622429380, 1791215328, 2878530825, 3131550138, 3116253669, 3504636512, 151829271]), Fp([4123265126, 2752013218, 1556720399, 386948539, 3643514185, 2039427681, 3467442232, 2876818448, 3322584909, 2011252300, 838048598, 284195453])]);
    let q_z2 = Fp2([Fp([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), Fp([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])]);

    // println!("pp2");
    // let (
    //     stark_pp2,
    //     proof_pp2,
    //     config_pp2
    // ) = calc_pairing_precomp(q_x2, q_y2, q_z2);
    // let recursive_pp2 = recursive_proof::<F, C, S_PP, C, D>(stark_pp2, proof_pp2.clone(), &config_pp2, true);

    // println!("ml2");
    // let (
    //     stark_ml2,
    //     proof_ml2,
    //     config_ml2,
    // ) = miller_loop_main(px2, py2, q_x2, q_y2, q_z2);
    // let recursive_ml2 = recursive_proof::<F, C, S_ML, C, D>(stark_ml2, proof_ml2.clone(), &config_ml2, true);
    
    // combine_proofs_recursive::<F, C, S_PP, S_ML, C, D>(
    //     stark_pp1,
    //     proof_pp1,
    //     &config_pp1,
    //     stark_ml1,
    //     proof_ml1,
    //     &config_ml1,
    //     stark_pp2,
    //     proof_pp2,
    //     &config_pp2,
    //     stark_ml2,
    //     proof_ml2,
    //     &config_ml2,
    // );
    recursive_proof_step_two::<F, C, C, D>(&recursive_pp1).unwrap();//, &recursive_ml1, &recursive_pp2, &recursive_ml2).unwrap();
}

fn combine_proofs_recursive<
    F: plonky2::hash::hash_types::RichField + plonky2::field::extension::Extendable<D>,
    C: GenericConfig<D, F = F>,
    S_PP: starky::stark::Stark<F, D> + Copy,
    S_ML: starky::stark::Stark<F, D> + Copy,
    InnerC: GenericConfig<D, F = F>,
    const D: usize,
>(
    stark_pp1: S_PP,
    inner_proof_pp1: starky::proof::StarkProofWithPublicInputs<F, InnerC, D>,
    inner_config_pp1: &StarkConfig,
    stark_ml1: S_ML,
    inner_proof_ml1: starky::proof::StarkProofWithPublicInputs<F, InnerC, D>,
    inner_config_ml1: &StarkConfig,
    stark_pp2: S_PP,
    inner_proof_pp2: starky::proof::StarkProofWithPublicInputs<F, InnerC, D>,
    inner_config_pp2: &StarkConfig,
    stark_ml2: S_ML,
    inner_proof_ml2: starky::proof::StarkProofWithPublicInputs<F, InnerC, D>,
    inner_config_ml2: &StarkConfig,
) where
    InnerC::Hasher: plonky2::plonk::config::AlgebraicHasher<F>,
{
    let circuit_config = plonky2::plonk::circuit_data::CircuitConfig::standard_recursion_config();
    let mut builder = plonky2::plonk::circuit_builder::CircuitBuilder::<F, D>::new(circuit_config);
    let mut pw = plonky2::iop::witness::PartialWitness::new();

    let degree_bits_pp1 = inner_proof_pp1.proof.recover_degree_bits(inner_config_pp1);
    let pt_pp1 = starky::recursive_verifier::add_virtual_stark_proof_with_pis(&mut builder, stark_pp1, inner_config_pp1, degree_bits_pp1);

    let degree_bits_ml1 = inner_proof_ml1.proof.recover_degree_bits(inner_config_ml1);
    let pt_ml1 = starky::recursive_verifier::add_virtual_stark_proof_with_pis(&mut builder, stark_ml1, inner_config_ml1, degree_bits_ml1);

    let degree_bits_pp2 = inner_proof_pp2.proof.recover_degree_bits(inner_config_pp2);
    let pt_pp2 = starky::recursive_verifier::add_virtual_stark_proof_with_pis(&mut builder, stark_pp2, inner_config_pp2, degree_bits_pp2);

    let degree_bits_ml2 = inner_proof_ml2.proof.recover_degree_bits(inner_config_ml2);
    let pt_ml2 = starky::recursive_verifier::add_virtual_stark_proof_with_pis(&mut builder, stark_ml2, inner_config_ml2, degree_bits_ml2);

    for i in 0..68*3*24 {
        builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::ELL_COEFFS_PUBLIC_INPUTS_OFFSET + i], pt_ml1.public_inputs[miller_loop::PIS_ELL_COEFFS_OFFSET + i]);
    }

    starky::recursive_verifier::set_stark_proof_with_pis_target(&mut pw, &pt_pp1, &inner_proof_pp1);
    starky::recursive_verifier::set_stark_proof_with_pis_target(&mut pw, &pt_ml1, &inner_proof_ml1);
    starky::recursive_verifier::verify_stark_proof_circuit::<F, InnerC, S_PP, D>(&mut builder, stark_pp1, pt_pp1, inner_config_pp1);
    starky::recursive_verifier::verify_stark_proof_circuit::<F, InnerC, S_ML, D>(&mut builder, stark_ml1, pt_ml1, inner_config_ml1);

    for i in 0..68*3*24 {
        builder.connect(pt_pp2.public_inputs[calc_pairing_precomp::ELL_COEFFS_PUBLIC_INPUTS_OFFSET + i], pt_ml2.public_inputs[miller_loop::PIS_ELL_COEFFS_OFFSET + i]);
    }

    starky::recursive_verifier::set_stark_proof_with_pis_target(&mut pw, &pt_pp2, &inner_proof_pp2);
    starky::recursive_verifier::set_stark_proof_with_pis_target(&mut pw, &pt_ml2, &inner_proof_ml2);
    starky::recursive_verifier::verify_stark_proof_circuit::<F, InnerC, S_PP, D>(&mut builder, stark_pp2, pt_pp2, inner_config_pp2);
    starky::recursive_verifier::verify_stark_proof_circuit::<F, InnerC, S_ML, D>(&mut builder, stark_ml2, pt_ml2, inner_config_ml2);



    let data = builder.build::<C>();
    println!("one step degree::{:?}", data.common.fri_params.degree_bits);
    let s = Instant::now();
    let proof = data.prove(pw).unwrap();
    println!("plonky2 recursive proof step one in {:?}", s.elapsed());
    data.verify(proof.clone()).unwrap();
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

    println!("one step gates::{:?}", builder.num_gates());
    let data = builder.build::<C>();
    println!("one step degree::{:?}", data.common.fri_params.degree_bits);
    let s = Instant::now();
    let proof = data.prove(pw).unwrap();
    println!("plonky2 recursive proof step one in {:?}", s.elapsed());
    data.verify(proof.clone()).unwrap();
    (proof, data.verifier_only, data.common)
}

type ProofTuple<F, C, const D: usize> = (
    ProofWithPublicInputs<F, C, D>,
    VerifierOnlyCircuitData<C, D>,
    CommonCircuitData<F, D>,
);

fn recursive_proof_step_two<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    InnerC: GenericConfig<D, F = F>,
    const D: usize,
>(
    inner_pp1: &ProofTuple<F, InnerC, D>,
    // inner_ml1: &ProofTuple<F, InnerC, D>,
    // inner_pp2: &ProofTuple<F, InnerC, D>,
    // inner_ml2: &ProofTuple<F, InnerC, D>,
) -> Result<ProofTuple<F, C, D>>
where
    InnerC::Hasher: AlgebraicHasher<F>,
{
    let config = CircuitConfig::standard_recursion_config();
    let (inner_proof_pp1, inner_vd_pp1, inner_cd_pp1) = inner_pp1;
    // let (inner_proof_ml1, inner_vd_ml1, inner_cd_ml1) = inner_ml1;
    // let (inner_proof_pp2, inner_vd_pp2, inner_cd_pp2) = inner_pp2;
    // let (inner_proof_ml2, inner_vd_ml2, inner_cd_ml2) = inner_ml2;
    let mut builder = CircuitBuilder::<F, D>::new(config.clone());
    let pt_pp1 = builder.add_virtual_proof_with_pis(inner_cd_pp1);
    // let pt_ml1 = builder.add_virtual_proof_with_pis(inner_cd_ml1);
    // let pt_pp2 = builder.add_virtual_proof_with_pis(inner_cd_pp2);
    // let pt_ml2 = builder.add_virtual_proof_with_pis(inner_cd_ml2);

    // for i in 0..68*3*24 {
    //     builder.connect(pt_pp1.public_inputs[calc_pairing_precomp::ELL_COEFFS_PUBLIC_INPUTS_OFFSET + i], pt_ml1.public_inputs[miller_loop::PIS_ELL_COEFFS_OFFSET + i]);
    // }

    // for i in 0..68*3*24 {
    //     builder.connect(pt_pp2.public_inputs[calc_pairing_precomp::ELL_COEFFS_PUBLIC_INPUTS_OFFSET + i], pt_ml2.public_inputs[miller_loop::PIS_ELL_COEFFS_OFFSET + i]);
    // }

    let inner_data_pp1 = builder.add_virtual_verifier_data(inner_cd_pp1.config.fri_config.cap_height);
    // let inner_data_ml1 = builder.add_virtual_verifier_data(inner_cd_ml1.config.fri_config.cap_height);
    // let inner_data_pp2 = builder.add_virtual_verifier_data(inner_cd_pp2.config.fri_config.cap_height);
    // let inner_data_ml2 = builder.add_virtual_verifier_data(inner_cd_ml2.config.fri_config.cap_height);

    builder.verify_proof::<InnerC>(&pt_pp1, &inner_data_pp1, inner_cd_pp1);
    // builder.verify_proof::<InnerC>(&pt_ml1, &inner_data_ml1, inner_cd_ml1);
    // builder.verify_proof::<InnerC>(&pt_pp2, &inner_data_pp2, inner_cd_pp2);
    // builder.verify_proof::<InnerC>(&pt_ml2, &inner_data_ml2, inner_cd_ml2);
    builder.print_gate_counts(0);

    let data = builder.build::<C>();
    println!("step two degree {:?}", data.common.fri_params.degree_bits);

    let mut pw = PartialWitness::new();
    pw.set_proof_with_pis_target(&pt_pp1, inner_proof_pp1);
    pw.set_verifier_data_target(&inner_data_pp1, inner_vd_pp1);
    // pw.set_proof_with_pis_target(&pt_ml1, inner_proof_ml1);
    // pw.set_verifier_data_target(&inner_data_ml1, inner_vd_ml1);
    // pw.set_proof_with_pis_target(&pt_pp2, inner_proof_pp2);
    // pw.set_verifier_data_target(&inner_data_pp2, inner_vd_pp2);
    // pw.set_proof_with_pis_target(&pt_ml2, inner_proof_ml2);
    // pw.set_verifier_data_target(&inner_data_ml2, inner_vd_ml2);

    let mut timing = TimingTree::new("prove", Level::Debug);
    let s = Instant::now();
    let proof = plonky2_prove::<F, C, D>(&data.prover_only, &data.common, pw, &mut timing)?;
    println!("plonky2 recursive proof step two in {:?}", s.elapsed());
    timing.print();

    data.verify(proof.clone())?;

    Ok((proof, data.verifier_only, data.common))
}

fn main() {
    std::thread::Builder::new().spawn(|| {
        combine_proofs_stark();
    //     // test_recursive_stark_verifier();
    // //    test_stark_circuit_constraints();
    }).unwrap().join().unwrap();
    return;
}
