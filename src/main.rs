use num_bigint::BigUint;
use plonky2::{plonk::config::{GenericConfig, PoseidonGoldilocksConfig}, util::{log2_ceil, timing::TimingTree}};
use plonky2_crypto::{biguint::{BigUintTarget, CircuitBuilderBiguint}, u32::arithmetic_u32::U32Target};
use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
use crate::{calc_pairing_precomp::PairingPrecompStark, ecc_aggregate::ECCAggStark, final_exponentiate::FinalExponentiateStark, fp12_mul::FP12MulStark, fp_plonky2::N, g1_plonky2::{pk_point_check, PUB_KEY_LEN}, g2_plonky2::{signature_point_check, SIG_LEN}, hash_to_curve::hash_to_curve, miller_loop::MillerLoopStark, native::{Fp, Fp12, Fp2}};
use starky::util::trace_rows_to_poly_values;
use std::{str::FromStr, time::Instant};

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

    let points = vec![
        [
            Fp::get_fp_from_biguint(BigUint::from_str("3204138955814570578163609245534537991184203369979786968842881480076799789054981632540434360211986881033031472658003").unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str("3400436843331243255025775671359320832363887837093257363324494062808177888976930512820808727051373705973107275596119").unwrap()),
        ],
        [
            Fp::get_fp_from_biguint(BigUint::from_str("1101601737221706935109816861121870935969966708030370202803894334105334358317103767010405906904724717953819864305475").unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str("2064714532506765361908058428125785453945021969836533091101878795902523891899248198975064034221224974951243095831271").unwrap()),
        ],
        [
            Fp::get_fp_from_biguint(BigUint::from_str("1346643022941237800159313209100746455104371997080613959634163427450219360879349073912415640276897934908131829885184").unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str("1712788991679293507887700660369980906279919831589234955852173033905487490155444583094339422053170211142384092687628").unwrap()),
        ],
        [
            Fp::get_fp_from_biguint(BigUint::from_str("1031639803009669276882438963763981275074329140720160354665639552098213397982643116932932030191763933194586471909627").unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str("3726372909620496167814358707804602244514273294790070245553214196247327852781072012573878272832314221345853766477953").unwrap()),
        ],
        [
            Fp::get_fp_from_biguint(BigUint::from_str("2085001279304652784006067885796453258851694636386816006411973174502146339457892744460495709989765802644147560717816").unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str("1390666781016039523434196082048737611089630897903128060749583361970460589620202298030510104038715416317703964768542").unwrap()),
        ],
    ];
    let res: [Fp; 2] = [
        Fp::get_fp_from_biguint(BigUint::from_str("1087234969399043337532762145805345524271996637454313824378364062590589536160217698088146259941330713744485370761187").unwrap()),
        Fp::get_fp_from_biguint(BigUint::from_str("3136236634071708553925641468996902690489869721550807157708175819862626511757026243446358296870755620456180595452223").unwrap()),
    ];
    let bits = vec![true; points.len()];

    println!("ec aggregate stark");
    let (
        stark_ec,
        proof_ec,
        config_ec
    ) = ec_aggregate_main::<F, C, D>(points, res, bits);
    let recursive_ec = recursive_proof::<F, C, ECAggStark, C, D>(stark_ec, proof_ec, &config_ec, true);

    let px1 = res[0];
    let py1 = res[1];
    let q_x1 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_str("1505722259415310266779135205437121965740464413893960596196733603147581884791988893744101733970478256891055375945536").unwrap()),
        Fp::get_fp_from_biguint(BigUint::from_str("1340668519720881607961131679928620414840483177443456807087496430579808669980316362600672382339984992997204446029721").unwrap()),
    ]);
    let q_y1 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_str("1736295234468997273821029500893781562836275683336158580517989036137419470229009617876811879653872185340706405922178").unwrap()),
        Fp::get_fp_from_biguint(BigUint::from_str("2424193914082549242180464768220335415996860337456428622667083208994155010064986010416627744636795804106402407557929").unwrap()),
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
    let q_x2 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_str("304916624593589725758998192556906432588442835131785285875484156350300323256553323177480097246911735623586417719757").unwrap()),
        Fp::get_fp_from_biguint(BigUint::from_str("571683617417147406164343177484195831633317889851162360601199727543177539914402642614657067649863132648953763352885").unwrap()),
    ]);
    let q_y2 = Fp2([
        Fp::get_fp_from_biguint(BigUint::from_str("1417349350435972599763912691298115467938931059184091147527970191503761433500070433784861919103649993499233201391892").unwrap()),
        Fp::get_fp_from_biguint(BigUint::from_str("1682756831248378783150359974203437061444894692587983127813303708041999183911542679268931185532855646639209016254767").unwrap()),
    ]);
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

    let msg = vec![
        99, 172,  62, 204, 126, 207, 244,   3,
        60,  22, 106,  26, 222,  12,  60,  19,
        63, 222,  36, 235, 255, 224,  19, 208,
       121,  15, 171,  19, 200,   2, 192, 215
     ];
    let sig = [
        131, 182, 220, 150, 162,  98,  63,  32, 235, 202, 139, 103,
         15,  26,  31,  47, 173, 101, 131, 249,  51,  28,  81, 144,
         40, 231,  88,   1,  73, 149, 252,  71, 136,  38,  25, 142,
        218, 140, 140,  55, 194, 243, 171,  82,   1, 160,  81,  53,
          1, 251,  40,  70,  50, 110, 166,  57, 167,  36,  11, 111,
        233,  36,  77,  29,  59,  45,  45, 133,  60,  69,  83, 211,
        243, 141, 119,  26,  69, 131, 234,  97,   3, 124,  45, 238,
         97,  40,  60,  67,  47,  52,  85, 150, 248, 111, 185, 205
      ];
    let pks = vec![
        [
      180, 209,  85, 127, 227, 149, 141, 182, 246,
      216, 134,  63, 159,   4,  66, 177, 100, 149,
      111, 221,  78, 211, 187, 183, 133, 254,  76,
      212,  77, 220, 124,  41, 198, 251,  76, 235,
      173,  56, 105, 140, 151, 142,   4, 115, 185,
       88,  54,  83
    ],
    [
        167,  40,  65, 152, 126,  79,  33, 157,  84,
        242, 182, 169, 234, 197, 254, 110, 120, 112,
         70,  68, 117,  60,  53, 121, 231, 118, 163,
        105,  27, 193,  35, 116,  63, 140,  99, 119,
         14, 208, 247,  42, 113, 233, 233, 100, 219,
        245, 143,  67
      ],
      [
        136, 191, 211,  48, 232, 185, 131, 122, 211,  69,
        233,  39,  25,  49,  74,  29, 147, 117, 247, 212,
        236, 219,  38, 210,   5, 183, 244,  23,  21,  77,
         73,   0, 159,  18,  40,   3,  45, 129, 166, 184,
        107, 137,  18,  76,  57,  60,  41,   0
      ],
      [
        166, 179, 228,  21, 198,  74,  35,  27,  71,
        249,  74, 188, 161, 199, 218,  63, 109,  57,
        195, 124,  24,  44, 165, 146, 123, 229, 164,
        152, 120,  17,  59, 237, 222, 233,  90, 228,
         36,  85,  97, 170, 215,  12, 226, 187, 183,
        101, 200, 251
      ],
      [
        141, 139, 233,  43, 222, 138, 241, 185, 223,
         19, 213, 168, 237, 138,  58,   1, 234, 182,
        238,  76, 248, 131, 215, 152, 124,  29, 120,
        192, 215, 217, 181,  58, 134,  48,  84,  31,
        221, 245, 227,  36, 182, 207,  73,   0,  67,
         91,  29, 248
      ],
    ];

    aggregate_recursive_proof::<F, C, C, D>(
        &msg,
        &sig,
        &pks,
        &recursive_pp1,
        &recursive_ml1,
        &recursive_pp2,
        &recursive_ml2,
        &recursive_fp12_mul,
        &recursive_final_exp,
        &recursive_ec,
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
    msg: &[u8],
    sig: &[u8; SIG_LEN],
    pks: &[[u8; PUB_KEY_LEN]],
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
    for _ in 0..pks.len() {
        pk_targets.push(builder.add_virtual_target_arr::<PUB_KEY_LEN>());
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
    }
    let mut timing = TimingTree::new("prove", Level::Debug);
    let s = Instant::now();
    let proof = plonky2_prove::<F, C, D>(&data.prover_only, &data.common, pw, &mut timing)?;
    println!("Time taken for aggregaet recusrive proof {:?}", s.elapsed());
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
