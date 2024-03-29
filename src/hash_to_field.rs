use plonky2::{field::extension::Extendable, hash::hash_types::RichField, iop::target::{BoolTarget, Target}, plonk::circuit_builder::CircuitBuilder};
use plonky2_crypto::{biguint::{BigUintTarget, CircuitBuilderBiguint}, hash::{sha256::CircuitBuilderHashSha2, CircuitBuilderHash, HashOutputTarget}, u32::{arithmetic_u32::{CircuitBuilderU32, U32Target}, interleaved_u32::CircuitBuilderB32}};

use crate::{fp2_plonky2::Fp2Target, fp_plonky2::FpTarget, native::modulus};

const DST: &str = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";
const DST_LEN: usize = DST.len();
const M: usize = 2;
const L: usize = (381 + 128 + 7)/8; // bls12-381 prime bits - 381, target secutity bits - 128

pub fn preprocess1_sha256_input<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    input_bytes: &[U32Target],
    hash_len: usize,
) -> BigUintTarget {
    let zero = builder.zero();
    let one = builder.one();


    let input_bits_len = input_bytes.len() * 8;
    let next_32_multiple = (input_bits_len + 7 + 31) / 32;

    let mut input_bits = input_bytes.iter().flat_map(|byte| builder.split_le(byte.0, 8)).collect::<Vec<BoolTarget>>();
    input_bits.resize(next_32_multiple*32, BoolTarget::new_unsafe(zero));
    input_bits[input_bits_len+7] = BoolTarget::new_unsafe(one);

    let mut input_u32s = input_bits.chunks(32).map(|bits| {
        let swap_bits = bits.chunks(8).rev().flatten();
        U32Target(builder.le_sum(swap_bits))
    }).collect::<Vec<U32Target>>();

    input_u32s.resize(hash_len, U32Target(zero));

    let padding_end1 = builder.constant_u32((input_bits_len >> 32) as u32);
    let padding_end0 = builder.constant_u32(input_bits_len as u32);
    input_u32s[hash_len - 2] = padding_end1;
    input_u32s[hash_len - 1] = padding_end0;

    BigUintTarget { limbs: input_u32s }
}

pub fn preprocess2_sha256_input<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    prev_hash: &BigUintTarget,
    input_bytes: &[U32Target],
    hash_len: usize,
) -> BigUintTarget{
    let zero = builder.zero();
    let one = builder.one();

    let input_bits_len = input_bytes.len() * 8;
    let next_32_multiple = (input_bits_len + 7 + 31) / 32;

    let mut input_bits = input_bytes.iter().flat_map(|byte| builder.split_le(byte.0, 8)).collect::<Vec<BoolTarget>>();
    input_bits.resize(next_32_multiple*32, BoolTarget::new_unsafe(zero));
    input_bits[input_bits_len+7] = BoolTarget::new_unsafe(one);

    let mut tmp_u32s = input_bits.chunks(32).map(|bits| {
        let swap_bits = bits.chunks(8).rev().flatten();
        U32Target(builder.le_sum(swap_bits))
    }).collect::<Vec<U32Target>>();

    let mut input_u32s = Vec::with_capacity(hash_len);
    for i in 0..prev_hash.limbs.len() {
        input_u32s.push(prev_hash.limbs[i]);
    }
    input_u32s.append(&mut tmp_u32s);
    input_u32s.resize(hash_len, U32Target(zero));

    let padding_end1 = builder.constant_u32(((input_bits_len + 256) >> 32) as u32);
    let padding_end0 = builder.constant_u32((input_bits_len + 256) as u32);
    input_u32s[hash_len - 2] = padding_end1;
    input_u32s[hash_len - 1] = padding_end0;

    BigUintTarget { limbs: input_u32s }
}

pub fn expand_message_xmd<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    msg: &[Target],
    dst: &[U32Target],
    len_in_bytes: usize,
) -> Vec<HashOutputTarget> {
    let b_in_bytes = 32; // SHA256 output length
    let r_in_bytes = b_in_bytes * 2;
    let ell = (len_in_bytes + b_in_bytes - 1) / b_in_bytes;
    assert!(ell <= 255, "Invalid xmd length");

    let zero = builder.zero();
    let one = builder.one();

    let dst_prime = builder.add_virtual_u32_targets(DST_LEN + 1);
    for i in 0..DST_LEN {
        builder.connect_u32(dst[i], dst_prime[i]);
    }
    let io2sp_dst = builder.constant_u32(dst.len() as u32);
    builder.connect_u32(dst_prime[DST_LEN], io2sp_dst);
    let z_pad = builder.add_virtual_u32_targets(r_in_bytes);
    for target in z_pad.iter() {
        builder.connect(target.0, zero);
    }
    let l_i_b_str = builder.add_virtual_u32_targets(2);
    let l_i_b_target = builder.constant_u32(len_in_bytes as u32);
    let u8_max = builder.constant_u32(0xff);
    let low = builder.and_u32(l_i_b_target, u8_max);
    let high = builder.rsh_u32(l_i_b_target, 8);
    
    builder.connect_u32(l_i_b_str[0], high);
    builder.connect_u32(l_i_b_str[1], low);

    let input_len = z_pad.len() + msg.len() + l_i_b_str.len() + 1 + dst_prime.len();

    let mut input_bytes = vec![];
    for i in 0..z_pad.len() {
        input_bytes.push(z_pad[i]);
    }
    for i in 0..msg.len() {
        input_bytes.push(U32Target(msg[i]));
    }
    for i in 0..l_i_b_str.len() {
        input_bytes.push(l_i_b_str[i]);
    }
    input_bytes.push(U32Target(zero));
    for i in 0..dst_prime.len() {
        input_bytes.push(dst_prime[i]);
    }

    let b_0_input = builder.add_virtual_hash_input_target((input_len * 8 + 511) / 512, 512);
    let preprocessed_input = preprocess1_sha256_input(builder, &input_bytes, b_0_input.input.num_limbs());
    builder.connect_biguint(&preprocessed_input, &b_0_input.input);
    let b_0 = builder.hash_sha256(&b_0_input);

    let mut b = vec![];

    let b0_input = builder.add_virtual_hash_input_target(((32+1+43)*8 + 511) / 512, 512);
    let mut b0_input_bytes = vec![];
    b0_input_bytes.push(U32Target(one));
    for i in 0..dst_prime.len() {
        b0_input_bytes.push(dst_prime[i]);
    }
    let preprocessed_input = preprocess2_sha256_input(builder, &b_0, &b0_input_bytes, b0_input.input.num_limbs());
    builder.connect_biguint(&preprocessed_input, &b0_input.input);
    let b0 = builder.hash_sha256(&b0_input);
    b.push(b0);

    for i in 1..ell {
        let bi_input = builder.add_virtual_hash_input_target(((32+1+43)*8 + 511) / 512, 512);
        let mut bi_input_bytes = vec![];
        let i2osp_i = builder.constant_u32((i+1) as u32);
        bi_input_bytes.push(i2osp_i);
        for i in 0..dst_prime.len() {
            bi_input_bytes.push(dst_prime[i]);
        }
        let prev_xor = BigUintTarget {
            limbs: b_0.limbs.iter().zip(b[i-1].limbs.iter()).map(|(b0, bi)| builder.xor_u32(*b0, *bi)).collect::<Vec<U32Target>>()
        };
        let preprocessed_input = preprocess2_sha256_input(builder, &prev_xor, &bi_input_bytes, bi_input.input.num_limbs());
        builder.connect_biguint(&preprocessed_input, &bi_input.input);
        let bi = builder.hash_sha256(&bi_input);
        b.push(bi);
    }
    b
}

pub fn hash_to_field<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    msg: &[Target],
    count: usize,
) -> Vec<Fp2Target> {
    let dst_bytes = DST.as_bytes();
    let len_in_bytes = count * M * L;

    let modulus = builder.constant_biguint(&modulus());

    let dst = dst_bytes.iter().map(|b| builder.constant_u32(*b as u32)).collect::<Vec<U32Target>>();
    let mut pseudo_random_bytes = expand_message_xmd(builder, &msg, &dst, len_in_bytes);
    pseudo_random_bytes.iter_mut().for_each(|big| big.limbs.reverse());
    let mut u: Vec<Fp2Target> = Vec::with_capacity(count);
    for i in 0..count {
        let mut e: Vec<FpTarget> = Vec::with_capacity(M);
        for j in 0..M {
            let elm_offset = (L * (j + i*M))/32;
            let mut non_reduced_limbs = vec![];
            for k in (0..L/32).rev() {
                non_reduced_limbs.append(&mut pseudo_random_bytes[elm_offset + k].limbs);
            }
            let non_reduced_point = BigUintTarget { limbs: non_reduced_limbs };
            let point = builder.rem_biguint(&non_reduced_point, &modulus);
            e.push(point);
        }
        u.push(e.try_into().unwrap());
    }

    u
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use num_bigint::BigUint;
    use plonky2::{field::types::Field, iop::witness::{PartialWitness, WitnessWrite}, plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig, config::{GenericConfig, PoseidonGoldilocksConfig}}};
    use plonky2_crypto::biguint::WitnessBigUint;

    use crate::hash_to_field::{hash_to_field, M};

    #[test]
    fn test_hash_to_field_circuit() {
        env_logger::init();
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let msg = vec![0; 0];
        let points = vec![
            [
                BigUint::from_str(
                    "29049427705470064014372021539200946731799999421508007424058975406727614446045474101630850618806446883308850416212"
                ).unwrap(),
                BigUint::from_str(
                    "1902536696277558307181953186589646430378426314321017542292852776971493752529393071590138748612350933458183942594017"
                ).unwrap(),
            ],
            [
                BigUint::from_str(
                    "1469261503385240180838932949518429345203566614064503355039321556894749047984560599095216903263030533722651807245292"
                ).unwrap(),
                BigUint::from_str(
                    "572729459443939985969475830277770585760085104819073756927946494897811696192971610777692627017094870085003613417370"
                ).unwrap(),
            ]
        ];
        let msg_target = builder.add_virtual_targets(msg.len());
        let point_targets = hash_to_field(&mut builder, &msg_target, 2);

        builder.print_gate_counts(0);
        let data = builder.build::<C>();

        let mut pw = PartialWitness::<F>::new();
        let msg_f = msg.iter().map(|m| F::from_canonical_u32(*m)).collect::<Vec<F>>();
        pw.set_target_arr(&msg_target, &msg_f);
        for i in 0..point_targets.len() {
            for j in 0..M {
                pw.set_biguint_target(&point_targets[i][j], &points[i][j]);
            }
        }

        let proof = data.prove(pw).expect("failed to prove");
        data.verify(proof).expect("failed to verify");
    }
}
