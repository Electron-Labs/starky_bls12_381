use num_bigint::BigUint;
use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, util::timing::{TimingTree, self}};
use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
use plonky2::field::types::Field;
use crate::{native::{get_u32_vec_from_literal_24, modulus, get_u32_vec_from_literal, Fp2, Fp, mul_Fp2, Fp6, mul_Fp6, Fp12}, fp_mult_starky::FpMultiplicationStark, fp2_mult_starky::Fp2MultiplicationStark, calc_pairing_precomp::{PairingPrecompStark, ELL_COEFFS_PUBLIC_INPUTS_OFFSET}, fp6_mult_starky::Fp6MulStark, fp12_mult_starky::Fp12MulStark, multiply_by_014::MultiplyBy014Stark, miller_loop::MillerLoopStark, cyclotomic_exponent::CyclotomicExponentStark};
use starky::util::trace_rows_to_poly_values;
use std::time::Instant;


pub mod native;
pub mod big_arithmetic;
pub mod fp_mult_starky;
pub mod fp2_mult_starky;
pub mod calc_pairing_precomp;
pub mod fp6_mult_starky;
pub mod fp12_mult_starky;
pub mod multiply_by_014;
pub mod miller_loop;
pub mod cyclotomic_exponent;

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

    let mut config = StarkConfig::standard_fast_config();
    config.fri_config.rate_bits = 2;
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

fn fp6_main() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = Fp6MulStark<F, D>;

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
    let x_fp6 = Fp6([Fp(x); 6]);
    let y_fp6 = Fp6([Fp(y); 6]);
    let x_y_product_fp6 = mul_Fp6(x_fp6, y_fp6);
    let s = Instant::now();
    stark.generate_trace(x_fp6, y_fp6);
    let mut public_inputs = Vec::new();
    for fp in x_fp6.0.iter().chain(y_fp6.0.iter().chain(x_y_product_fp6.0.iter())) {
        for e in fp.0.iter() {
            public_inputs.push(F::from_canonical_u32(*e));
        }
    }
    assert_eq!(public_inputs.len(), fp6_mult_starky::PUBLIC_INPUTS);
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

fn fp12_main() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = Fp12MulStark<F, D>;

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
    let x_fp12 = Fp12([Fp(x); 12]);
    let y_fp12 = Fp12([Fp(y); 12]);
    let x_y_product_fp12 = x_fp12*y_fp12;
    let s = Instant::now();
    stark.generate_trace(x_fp12, y_fp12);
    let mut public_inputs = Vec::new();
    for fp in x_fp12.0.iter().chain(y_fp12.0.iter().chain(x_y_product_fp12.0.iter())) {
        for e in fp.0.iter() {
            public_inputs.push(F::from_canonical_u32(*e));
        }
    }
    assert_eq!(public_inputs.len(), fp12_mult_starky::PUBLIC_INPUTS);
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

fn multiply_by_014_main() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = MultiplyBy014Stark<F, D>;

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
    let x_fp12 = Fp12([Fp(x); 12]);
    let y_fp2 = Fp2([Fp(y); 2]);
    let res = x_fp12.multiplyBy014(y_fp2, y_fp2, y_fp2);
    let s = Instant::now();
    stark.generate_trace(x_fp12, y_fp2, y_fp2, y_fp2);
    let mut public_inputs = Vec::new();
    for fp in x_fp12.0.iter() {
        for e in fp.0.iter() {
            public_inputs.push(F::from_canonical_u32(*e));
        }
    }
    for fp in y_fp2.0.iter() {
        for e in fp.0.iter() {
            public_inputs.push(F::from_canonical_u32(*e));
        }
    }
    for fp in y_fp2.0.iter() {
        for e in fp.0.iter() {
            public_inputs.push(F::from_canonical_u32(*e));
        }
    }
    for fp in y_fp2.0.iter() {
        for e in fp.0.iter() {
            public_inputs.push(F::from_canonical_u32(*e));
        }
    }
    for fp in res.0.iter() {
        for e in fp.0.iter() {
            public_inputs.push(F::from_canonical_u32(*e));
        }
    }
    assert_eq!(public_inputs.len(), multiply_by_014::PUBLIC_INPUTS);
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

fn miller_loop_main() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = MillerLoopStark<F, D>;

    let config = StarkConfig::standard_fast_config();
    let mut stark = S::new(1024);
    let s_ = stark.clone();
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
    stark.generate_trace(x, y, ell_coeffs);
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

fn cyclomic_exponent_main() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = CyclotomicExponentStark<F, D>;

    let mut config = StarkConfig::standard_fast_config();
    config.fri_config.rate_bits = 2;
    let mut stark = S::new(1024);
    let s_ = stark.clone();
    let s = Instant::now();
    let x = Fp12([Fp([3688549023, 1461121002, 158795132, 3031927502, 213444395, 4286532434, 2430134266, 3543104615, 1291488635, 3435685873, 4037455674, 79410575]), Fp([1360882579, 3002343476, 3086261481, 844031790, 3247736081, 1476716566, 2285276612, 2128837429, 3999081699, 4034708995, 1714901244, 52662165]), Fp([4104185655, 3701245790, 808982471, 2474474870, 86883540, 2861754577, 892037001, 426313854, 351740683, 2973656712, 2938329451, 98989231]), Fp([1750337445, 1055423710, 3314636215, 3832606429, 682495303, 3837288901, 3323765171, 317766258, 263941221, 4122823463, 817092141, 399622891]), Fp([2471624410, 3446467705, 2404303712, 4024275285, 3482111337, 2794822952, 3019262746, 126898360, 1076123014, 2901504703, 3932319379, 98921494]), Fp([2110261208, 2032742098, 990038150, 1352002937, 3987858999, 2819343369, 3282554204, 766147331, 208424639, 1602982609, 4112224585, 236233458]), Fp([2046547795, 3173960576, 2639561839, 1364192507, 1671233573, 2391309894, 3000205425, 1179450741, 3256341155, 3289801138, 1673317021, 168965912]), Fp([993521759, 35789000, 2528933762, 1397651268, 1549073333, 728869112, 2818328447, 3376956733, 4125103710, 3410833193, 3702323277, 402097749]), Fp([1613123474, 1843683341, 870050044, 2560600706, 933520115, 916747666, 4021709957, 20791057, 516247948, 3820524631, 3267700533, 122227566]), Fp([3600146516, 2812057600, 4150243859, 210373455, 465523258, 2359663667, 2064799726, 1552807009, 494361983, 2866737666, 172560447, 37672107]), Fp([13226053, 1019983919, 546396615, 4251229931, 250632233, 654320493, 1352696718, 2083058924, 1058634822, 2809138592, 900633632, 353005311]), Fp([340295756, 388460180, 1763111897, 2809758930, 1065140740, 2216989682, 2359308769, 1641074723, 1795030663, 945477827, 911995824, 168338922])]);
    let res = x.cyclotocmicExponent();
    let mut public_inputs = Vec::<F>::new();
    for e in x.get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    for e in res.get_u32_slice().concat().iter() {
        public_inputs.push(F::from_canonical_u32(*e));
    }
    assert_eq!(public_inputs.len(), cyclotomic_exponent::PUBLIC_INPUTS);
    stark.generate_trace(x);
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

fn main() {
    let test_fp_which: usize = 8;
    if test_fp_which == 1 {
        fp1_main();
    } else if test_fp_which == 2 {
        fp2_main();
    } else if test_fp_which == 3 {
        calc_pairing_precomp();
    } else if test_fp_which == 4 {
        fp6_main();
    } else if test_fp_which == 5 {
        fp12_main();
    } else if test_fp_which == 6 {
        multiply_by_014_main();
    } else if test_fp_which == 7 {
        miller_loop_main();
    } else if test_fp_which == 8 {
        cyclomic_exponent_main();
    }
}
