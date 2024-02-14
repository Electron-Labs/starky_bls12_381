use num_bigint::BigUint;
use plonky2::{field::extension::Extendable, hash::hash_types::RichField, iop::target::Target, plonk::circuit_builder::CircuitBuilder};
use plonky2_crypto::{biguint::{BigUintTarget, CircuitBuilderBiguint}, u32::arithmetic_u32::{CircuitBuilderU32, U32Target}};

use crate::{fp_plonky2::{div_fp, FpTarget, N}, native::modulus};

pub type PointG1Target = [FpTarget; 2];

pub const PUB_KEY_LEN: usize = 48;

pub fn g1_to_affine<F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    x: &FpTarget,
    y: &FpTarget,
    z: &FpTarget,
) -> PointG1Target {
    [
        div_fp(builder, x, z),
        div_fp(builder, y, z),
    ]
}

pub fn pk_point_check<F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    point_x: &FpTarget,
    point_y: &FpTarget,
    point_z: &FpTarget,
    pk: &[Target; PUB_KEY_LEN],
){
    let msbs = builder.split_le(pk[0], 8);
    let bflag = msbs[6];
    builder.assert_zero(bflag.target);

    let aflag = msbs[5];

    let point_affine = g1_to_affine(builder, point_x, point_y, point_z);
    let (x, y) = (&point_affine[0], &point_affine[1]);
    let two = builder.constant_biguint(&2u32.into());
    let y_2 = builder.mul_biguint(y, &two);
    let p = builder.constant_biguint(&modulus());
    let y_2_p = builder.div_biguint(&y_2, &p);
    let zero = builder.zero_u32();
    for i in 0..y_2_p.limbs.len() {
        if i == 0 {
            builder.connect(aflag.target, y_2_p.limbs[i].0);
        }
        else {
            builder.connect_u32(y_2_p.limbs[i], zero);
        }
    }

    let z_limbs: Vec<U32Target> = pk.chunks(4).into_iter().map(|chunk| {
        let zero = builder.zero();
        let factor = builder.constant(F::from_canonical_u32(256));
        U32Target(chunk.iter().fold(zero, |acc, c| builder.mul_add(acc, factor, *c)))
    }).rev().collect();
    let z = BigUintTarget { limbs: z_limbs };

    let pow_2_383 = builder.constant_biguint(&(BigUint::from(1u32)<<383u32));
    let pow_2_381 = builder.constant_biguint(&(BigUint::from(1u32)<<381u32));
    let pow_2_381_or_zero = BigUintTarget {
        limbs: (0..N).into_iter().map(|i| U32Target(builder.select(aflag, pow_2_381.limbs[i].0, zero.0))).collect(),
    };
    let flags = builder.add_biguint(&pow_2_383, &pow_2_381_or_zero);
    let z_reconstructed = builder.add_biguint(x, &flags);

    builder.connect_biguint(&z, &z_reconstructed);

}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use num_bigint::BigUint;
    use plonky2::{field::types::Field, iop::witness::{PartialWitness, WitnessWrite}, plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig, config::{GenericConfig, PoseidonGoldilocksConfig}}};
    use plonky2_crypto::biguint::{CircuitBuilderBiguint, WitnessBigUint};

    use crate::{fp_plonky2::N, native::Fp};

    use super::{pk_point_check, PUB_KEY_LEN};

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;


    #[test]
    fn test_pk_point_check() {
        env_logger::init();
        let x_fp = Fp::get_fp_from_biguint(BigUint::from_str(
                "1411593089133753962474730354030258013436363179669233753420355895053483563962487440344772403327192608890810553901021"
            ).unwrap());
        let y_fp = Fp::get_fp_from_biguint(BigUint::from_str(
                "1129849551898749416521145382954514863932842971284587833618170655784677795582674723477811354555329195575398134182304"
            ).unwrap());
        let z_fp = Fp::get_fp_from_biguint(BigUint::from_str(
                "1"
            ).unwrap());
        let pk = vec![
            137,  43, 218, 171,  28,   7, 187, 176, 109,
            242, 254, 250, 130, 131,  36,  52,   5, 250,
             52, 180, 134,  10, 178, 231, 178,  58,  55,
            126, 255, 212, 103,  96, 128,  72, 218, 203,
            176, 158, 145,   7, 181, 216, 163, 154,  82,
            112, 159, 221
        ];
        let pk_f: Vec<F> = pk.iter().map(|i| F::from_canonical_u8(*i)).collect();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x = builder.add_virtual_biguint_target(N);
        let y = builder.add_virtual_biguint_target(N);
        let z = builder.add_virtual_biguint_target(N);

        let pk = builder.add_virtual_target_arr::<PUB_KEY_LEN>();

        pk_point_check(&mut builder, &x, &y, &z, &pk);

        let mut pw = PartialWitness::<F>::new();
        pw.set_biguint_target(&x, &x_fp.to_biguint());

        pw.set_biguint_target(&y, &y_fp.to_biguint());

        pw.set_biguint_target(&z, &z_fp.to_biguint());

        pw.set_target_arr(&pk, &pk_f);

        builder.print_gate_counts(0);
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();
    }
}
