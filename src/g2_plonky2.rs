use num_bigint::{BigUint, ToBigUint};
use plonky2::{field::extension::Extendable, hash::hash_types::RichField, iop::{generator::SimpleGenerator, target::{BoolTarget, Target}}, plonk::circuit_builder::CircuitBuilder};
use plonky2_crypto::{biguint::{BigUintTarget, CircuitBuilderBiguint, GeneratedValuesBigUint, WitnessBigUint}, u32::arithmetic_u32::{CircuitBuilderU32, U32Target}};

use crate::{fp2_plonky2::{add_fp2, is_equal, mul_fp2, negate_fp2, range_check_fp2, sub_fp2, Fp2Target}, fp_plonky2::N, native::{get_bls_12_381_parameter, modulus, Fp, Fp2}};

pub type PointG2Target = [Fp2Target; 2];

pub const SIG_LEN: usize = 96;

pub fn g2_add_unequal<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    a: &PointG2Target,
    b: &PointG2Target,
) -> PointG2Target {
    let dy = sub_fp2(builder, &b[1], &a[1]);
    let dx = sub_fp2(builder, &b[0], &a[0]);
    let outx_c0 = builder.add_virtual_biguint_target(N);
    let outx_c1 = builder.add_virtual_biguint_target(N);
    let outy_c0 = builder.add_virtual_biguint_target(N);
    let outy_c1 = builder.add_virtual_biguint_target(N);
    let out = [[outx_c0, outx_c1], [outy_c0, outy_c1]];
    builder.add_simple_generator(G2AdditionGenerator {
        a: a.clone(),
        b: b.clone(),
        dx: dx.clone(),
        dy: dy.clone(),
        out: out.clone(),
    });
    range_check_fp2(builder, &out[0]);
    range_check_fp2(builder, &out[1]);
    let dx_sq = mul_fp2(builder, &dx, &dx);
    let dy_sq = mul_fp2(builder,&dy, &dy);

    let x1x2= add_fp2(builder, &a[0], &b[0]);
    let x1x2x3 = add_fp2(builder, &x1x2, &out[0]);
    let cubic = mul_fp2(builder, &x1x2x3, &dx_sq);

    let cubic_dysq = sub_fp2(builder, &cubic, &dy_sq);
    let cubic_dysq_check = crate::fp2_plonky2::is_zero(builder, &cubic_dysq);
    builder.assert_one(cubic_dysq_check.target);
    
    let y1y3 = add_fp2(builder, &a[1], &out[1]);
    let y1y3dx = mul_fp2(builder, &y1y3, &dx);

    let x1x3 = sub_fp2(builder, &a[0], &out[0]);
    let x1x3dy = mul_fp2(builder, &x1x3, &dy);

    let check = is_equal(builder, &y1y3dx, &x1x3dy);
    builder.assert_one(check.target);

    out
}

pub fn g2_double<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    a: &PointG2Target,
    iso_3_a: &Fp2Target,
    iso_3_b: &Fp2Target,
) -> PointG2Target {

    let outx_c0 = builder.add_virtual_biguint_target(N);
    let outx_c1 = builder.add_virtual_biguint_target(N);
    let outy_c0 = builder.add_virtual_biguint_target(N);
    let outy_c1 = builder.add_virtual_biguint_target(N);
    let out = [[outx_c0, outx_c1], [outy_c0, outy_c1]];
    builder.add_simple_generator(G2DoublingGenerator {
        a: a.clone(),
        iso_3_a: iso_3_a.clone(),
        out: out.clone(),
    });
    range_check_fp2(builder, &out[0]);
    range_check_fp2(builder, &out[1]);
    
    // point on tangent
    let x_sq = mul_fp2(builder, &a[0], &a[0]);
    let x_sq2 = add_fp2(builder, &x_sq, &x_sq);
    let x_sq3 = add_fp2(builder, &x_sq2, &x_sq);
    let x_sq3_a = add_fp2(builder, &x_sq3, iso_3_a);
    let x1_x3 = sub_fp2(builder, &a[0], &out[0]);
    let right = mul_fp2(builder, &x_sq3_a, &x1_x3);

    let y1_2 = add_fp2(builder, &a[1], &a[1]);
    let y1_y3 = add_fp2(builder, &a[1], &out[1]);
    let left = mul_fp2(builder, &y1_2, &y1_y3);

    let check = is_equal(builder, &right, &left);
    builder.assert_one(check.target);

    // point on curve
    let outx_sq = mul_fp2(builder, &out[0], &out[0]);
    let outx_cu = mul_fp2(builder, &outx_sq, &out[0]);
    let a_outx = mul_fp2(builder, &out[0], iso_3_a);
    let outx_cu_a_outx = add_fp2(builder, &outx_cu, &a_outx);
    let right = add_fp2(builder, &outx_cu_a_outx, iso_3_b);

    let left = mul_fp2(builder, &out[1], &out[1]);

    let check = is_equal(builder, &right, &left);
    builder.assert_one(check.target);

    let check = is_equal(builder, &a[0], &out[0]);
    builder.assert_zero(check.target);

    out
}

pub fn g2_add<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    a: &PointG2Target,
    is_infinity_a: BoolTarget,
    b: &PointG2Target,
    is_infinity_b: BoolTarget,
    iso_3_a: &Fp2Target,
    iso_3_b: &Fp2Target,
) -> PointG2Target {
    let x_equal = crate::fp2_plonky2::is_equal(builder, &a[0], &b[0]);
    let y_equal = crate::fp2_plonky2::is_equal(builder, &a[1], &b[1]);
    let do_double = builder.and(x_equal, y_equal);
    let add_input_b = [
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
    ];
    for i in 0..12 {
        if i == 0 {
            let zero = builder.zero();
            let is_zero = builder.is_equal(b[0][0].limbs[i].0, zero);
            let select = builder.select(do_double, is_zero.target, b[0][0].limbs[i].0);
            builder.connect(add_input_b[0][0].limbs[i].0, select);
        } else {
            builder.connect_u32(add_input_b[0][0].limbs[i], b[0][0].limbs[i]);
        }
    }
    builder.connect_biguint(&add_input_b[0][1], &b[0][1]);
    builder.connect_biguint(&add_input_b[1][0], &b[1][0]);
    builder.connect_biguint(&add_input_b[1][1], &b[1][1]);
    let addition = g2_add_unequal(builder, a, &add_input_b);
    let doubling = g2_double(builder, a, iso_3_a, iso_3_b);
    let both_inf = builder.and(is_infinity_a, is_infinity_b);
    let a_not_inf = builder.not(is_infinity_a);
    let b_not_inf = builder.not(is_infinity_b);
    let both_not_inf = builder.and(a_not_inf, b_not_inf);
    let not_y_equal = builder.not(y_equal);
    let a_neg_b = builder.and(x_equal, not_y_equal);
    let inverse = builder.and(both_not_inf, a_neg_b);
    let out_inf = builder.or(both_inf, inverse);
    builder.assert_zero(out_inf.target);
    let add_or_double_select = [
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
    ];
    for i in 0..2 {
        for j in 0..2 {
            for k in 0..N {
                let s = builder.select(do_double, doubling[i][j].limbs[k].0, addition[i][j].limbs[k].0);
                builder.connect(add_or_double_select[i][j].limbs[k].0, s);
            }
        }
    }
    let a_inf_select = [
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
    ];
    for i in 0..2 {
        for j in 0..2 {
            for k in 0..N {
                let s = builder.select(is_infinity_a, b[i][j].limbs[k].0, add_or_double_select[i][j].limbs[k].0);
                builder.connect(a_inf_select[i][j].limbs[k].0, s);
            }
        }
    }
    let b_inf_select = [
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
    ];
    for i in 0..2 {
        for j in 0..2 {
            for k in 0..N {
                let s = builder.select(is_infinity_b, a[i][j].limbs[k].0, a_inf_select[i][j].limbs[k].0);
                builder.connect(b_inf_select[i][j].limbs[k].0, s);
            }
        }
    }
    
    b_inf_select
}

pub fn g2_negate<F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    p: &PointG2Target,
) -> PointG2Target {
    [
        p[0].clone(),
        negate_fp2(builder, &p[1])
    ]
}

pub fn g2_scalar_mul<F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    p: &PointG2Target,
    iso_3_b: &Fp2Target,
) -> PointG2Target {
    let iso_3_a = [
        builder.constant_biguint(&0.to_biguint().unwrap()),
        builder.constant_biguint(&0.to_biguint().unwrap()),
    ];
    let mut r = [
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
        [builder.add_virtual_biguint_target(N), builder.add_virtual_biguint_target(N)],
    ];
    let fals = builder._false();
    for i in (0..get_bls_12_381_parameter().bits()).rev() {
        if i==get_bls_12_381_parameter().bits()-1 {
            for idx in 0..2 {
                for jdx in 0..2 {
                    builder.connect_biguint(&r[idx][jdx], &p[idx][jdx]);
                }
            }
        } else {
            let pdouble = g2_double(builder, &r, &iso_3_a, iso_3_b);
            if !get_bls_12_381_parameter().bit(i) {
                r = pdouble;
            } else {
                r = g2_add(builder, &pdouble, fals, p, fals, &iso_3_a, iso_3_b);
            }
        }
    }
    r
}

pub fn signature_point_check<F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    point: &PointG2Target,
    sig: &[Target; SIG_LEN],
){
    let msbs = builder.split_le(sig[0], 8);
    let bflag = msbs[6];
    builder.assert_zero(bflag.target);

    let aflag = msbs[5];

    let (x0, x1, y0, y1) = (&point[0][0], &point[0][1], &point[1][0], &point[1][1]);
    let y1_zero = crate::fp_plonky2::is_zero(builder, &y1);
    let zero = builder.zero_u32();
    let y_select_limbs: Vec<U32Target> = (0..N).into_iter().map(|i| U32Target(builder.select(
        y1_zero,
        y0.limbs.get(i).unwrap_or(&zero).0,
        y1.limbs.get(i).unwrap_or(&zero).0,
    ))).collect();
    let y_select = BigUintTarget { limbs: y_select_limbs };
    let two = builder.constant_biguint(&2u32.into());
    let y_select_2 = builder.mul_biguint(&y_select, &two);
    let p = builder.constant_biguint(&modulus());
    let y_select_2_p = builder.div_biguint(&y_select_2, &p);
    for i in 0..y_select_2_p.limbs.len() {
        if i == 0 {
            builder.connect(aflag.target, y_select_2_p.limbs[i].0);
        }
        else {
            builder.connect_u32(y_select_2_p.limbs[i], zero);
        }
    }

    let z1_limbs: Vec<U32Target> = sig[0..SIG_LEN/2].chunks(4).into_iter().map(|chunk| {
        let zero = builder.zero();
        let factor = builder.constant(F::from_canonical_u32(256));
        U32Target(chunk.iter().fold(zero, |acc, c| builder.mul_add(acc, factor, *c)))
    }).rev().collect();
    let z1 = BigUintTarget { limbs: z1_limbs };

    let z2_limbs: Vec<U32Target> = sig[SIG_LEN/2..SIG_LEN].chunks(4).into_iter().map(|chunk| {
        let zero = builder.zero();
        let factor = builder.constant(F::from_canonical_u32(256));
        U32Target(chunk.iter().fold(zero, |acc, c| builder.mul_add(acc, factor, *c)))
    }).rev().collect();
    let z2 = BigUintTarget { limbs: z2_limbs };

    builder.connect_biguint(&x0, &z2);

    let pow_2_383 = builder.constant_biguint(&(BigUint::from(1u32)<<383u32));
    let pow_2_381 = builder.constant_biguint(&(BigUint::from(1u32)<<381u32));
    let pow_2_381_or_zero = BigUintTarget {
        limbs: (0..N).into_iter().map(|i| U32Target(builder.select(aflag, pow_2_381.limbs[i].0, zero.0))).collect(),
    };
    let flags = builder.add_biguint(&pow_2_383, &pow_2_381_or_zero);
    let z1_reconstructed = builder.add_biguint(x1, &flags);

    builder.connect_biguint(&z1, &z1_reconstructed);

}

#[derive(Debug, Default)]
pub struct G2AdditionGenerator {
    a: PointG2Target,
    b: PointG2Target,
    dx: Fp2Target,
    dy: Fp2Target,
    out: PointG2Target,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for G2AdditionGenerator {
    fn id(&self) -> String {
        "G2AdditionGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<plonky2::iop::target::Target> {
        let a_targets = self.a.iter().flat_map(|f2| f2.iter().flat_map(|f| f.limbs.iter().map(|l| l.0).collect::<Vec<Target>>()).collect::<Vec<Target>>()).collect::<Vec<Target>>();
        let b_targets = self.b.iter().flat_map(|f2| f2.iter().flat_map(|f| f.limbs.iter().map(|l| l.0).collect::<Vec<Target>>()).collect::<Vec<Target>>()).collect::<Vec<Target>>();
        let dx_targets = self.dx.iter().flat_map(|f| f.limbs.iter().map(|l| l.0).collect::<Vec<Target>>()).collect::<Vec<Target>>();
        let dy_targets = self.dy.iter().flat_map(|f| f.limbs.iter().map(|l| l.0).collect::<Vec<Target>>()).collect::<Vec<Target>>();
        [a_targets, b_targets, dx_targets, dy_targets].concat()
    }

    fn run_once(&self, witness: &plonky2::iop::witness::PartitionWitness<F>, out_buffer: &mut plonky2::iop::generator::GeneratedValues<F>) {
        let ax = Fp2([
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.a[0][0].clone())),
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.a[0][1].clone())),
        ]);
        let ay = Fp2([
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.a[1][0].clone())),
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.a[1][1].clone())),
        ]);
        let bx = Fp2([
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.b[0][0].clone())),
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.b[0][1].clone())),
        ]);
        let dx = Fp2([
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.dx[0].clone())),
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.dx[1].clone())),
        ]);
        let dy = Fp2([
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.dy[0].clone())),
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.dy[1].clone())),
        ]);
        let dx_inv = dx.invert();
        let lambda = dy * dx_inv;
        let lambda_sq = lambda * lambda;
        let outx = lambda_sq - ax - bx;
        let outy = lambda * (ax - outx) - ay;
        out_buffer.set_biguint_target(&self.out[0][0], &outx.0[0].to_biguint());
        out_buffer.set_biguint_target(&self.out[0][1], &outx.0[1].to_biguint());
        out_buffer.set_biguint_target(&self.out[1][0], &outy.0[0].to_biguint());
        out_buffer.set_biguint_target(&self.out[1][1], &outy.0[1].to_biguint());
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &plonky2::plonk::circuit_data::CommonCircuitData<F, D>) -> plonky2::util::serialization::IoResult<()> {
        self.a[0][0].serialize(dst)?;
        self.a[0][1].serialize(dst)?;
        self.a[1][0].serialize(dst)?;
        self.a[1][1].serialize(dst)?;
        self.b[0][0].serialize(dst)?;
        self.b[0][1].serialize(dst)?;
        self.b[1][0].serialize(dst)?;
        self.b[1][1].serialize(dst)?;
        self.dx[0].serialize(dst)?;
        self.dx[1].serialize(dst)?;
        self.dy[0].serialize(dst)?;
        self.dy[1].serialize(dst)?;
        self.out[0][0].serialize(dst)?;
        self.out[0][1].serialize(dst)?;
        self.out[1][0].serialize(dst)?;
        self.out[1][1].serialize(dst)
    }

    fn deserialize(src: &mut plonky2::util::serialization::Buffer, _common_data: &plonky2::plonk::circuit_data::CommonCircuitData<F, D>) -> plonky2::util::serialization::IoResult<Self>
    where
        Self: Sized {
        let ax_c0 = BigUintTarget::deserialize(src)?;
        let ax_c1 = BigUintTarget::deserialize(src)?;
        let ay_c0 = BigUintTarget::deserialize(src)?;
        let ay_c1 = BigUintTarget::deserialize(src)?;
        let bx_c0 = BigUintTarget::deserialize(src)?;
        let bx_c1 = BigUintTarget::deserialize(src)?;
        let by_c0 = BigUintTarget::deserialize(src)?;
        let by_c1 = BigUintTarget::deserialize(src)?;
        let dx_c0 = BigUintTarget::deserialize(src)?;
        let dx_c1 = BigUintTarget::deserialize(src)?;
        let dy_c0 = BigUintTarget::deserialize(src)?;
        let dy_c1 = BigUintTarget::deserialize(src)?;
        let outx_c0 = BigUintTarget::deserialize(src)?;
        let outx_c1 = BigUintTarget::deserialize(src)?;
        let outy_c0 = BigUintTarget::deserialize(src)?;
        let outy_c1 = BigUintTarget::deserialize(src)?;
        Ok(Self {
            a: [[ax_c0, ax_c1], [ay_c0, ay_c1]],
            b: [[bx_c0, bx_c1], [by_c0, by_c1]],
            dx: [dx_c0, dx_c1],
            dy: [dy_c0, dy_c1],
            out: [[outx_c0, outx_c1], [outy_c0, outy_c1]],
        })
    }
}

#[derive(Debug, Default)]
pub struct G2DoublingGenerator {
    a: PointG2Target,
    iso_3_a: Fp2Target,
    out: PointG2Target,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for G2DoublingGenerator {
    fn id(&self) -> String {
        "G2DoublingGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<plonky2::iop::target::Target> {
        let a_targets = self.a.iter().flat_map(|f2| f2.iter().flat_map(|f| f.limbs.iter().map(|l| l.0).collect::<Vec<Target>>()).collect::<Vec<Target>>()).collect::<Vec<Target>>();
        let iso_3_a_targets = self.iso_3_a.iter().flat_map(|f| f.limbs.iter().map(|l| l.0).collect::<Vec<Target>>()).collect::<Vec<Target>>();
        [a_targets, iso_3_a_targets].concat()
    }

    fn run_once(&self, witness: &plonky2::iop::witness::PartitionWitness<F>, out_buffer: &mut plonky2::iop::generator::GeneratedValues<F>) {
        let iso_3_a = Fp2([
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.iso_3_a[0].clone())),
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.iso_3_a[1].clone())),
        ]);
        let ax = Fp2([
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.a[0][0].clone())),
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.a[0][1].clone())),
        ]);
        let ay = Fp2([
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.a[1][0].clone())),
            Fp::get_fp_from_biguint(witness.get_biguint_target(self.a[1][1].clone())),
        ]);
        let lambda_num = iso_3_a + ax * ax * Fp::get_fp_from_biguint(3u32.into());
        let lambda_denom = ay + ay;
        let lambda = lambda_num / lambda_denom;
        let lambda_sq = lambda * lambda;
        let outx = lambda_sq - ax - ax;
        let outy = lambda * (ax - outx) - ay;
        out_buffer.set_biguint_target(&self.out[0][0], &outx.0[0].to_biguint());
        out_buffer.set_biguint_target(&self.out[0][1], &outx.0[1].to_biguint());
        out_buffer.set_biguint_target(&self.out[1][0], &outy.0[0].to_biguint());
        out_buffer.set_biguint_target(&self.out[1][1], &outy.0[1].to_biguint());
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &plonky2::plonk::circuit_data::CommonCircuitData<F, D>) -> plonky2::util::serialization::IoResult<()> {
        self.a[0][0].serialize(dst)?;
        self.a[0][1].serialize(dst)?;
        self.a[1][0].serialize(dst)?;
        self.a[1][1].serialize(dst)?;
        self.iso_3_a[0].serialize(dst)?;
        self.iso_3_a[1].serialize(dst)?;
        self.out[0][0].serialize(dst)?;
        self.out[0][1].serialize(dst)?;
        self.out[1][0].serialize(dst)?;
        self.out[1][1].serialize(dst)
    }

    fn deserialize(src: &mut plonky2::util::serialization::Buffer, _common_data: &plonky2::plonk::circuit_data::CommonCircuitData<F, D>) -> plonky2::util::serialization::IoResult<Self>
    where
        Self: Sized {
        let ax_c0 = BigUintTarget::deserialize(src)?;
        let ax_c1 = BigUintTarget::deserialize(src)?;
        let ay_c0 = BigUintTarget::deserialize(src)?;
        let ay_c1 = BigUintTarget::deserialize(src)?;
        let iso_3_a_c0 = BigUintTarget::deserialize(src)?;
        let iso_3_a_c1 = BigUintTarget::deserialize(src)?;
        let outx_c0 = BigUintTarget::deserialize(src)?;
        let outx_c1 = BigUintTarget::deserialize(src)?;
        let outy_c0 = BigUintTarget::deserialize(src)?;
        let outy_c1 = BigUintTarget::deserialize(src)?;
        Ok(Self {
            a: [[ax_c0, ax_c1], [ay_c0, ay_c1]],
            iso_3_a: [iso_3_a_c0, iso_3_a_c1],
            out: [[outx_c0, outx_c1], [outy_c0, outy_c1]],
        })
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use num_bigint::{BigUint, ToBigUint};
    use plonky2::{field::types::Field, iop::witness::{PartialWitness, WitnessWrite}, plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig, config::{GenericConfig, PoseidonGoldilocksConfig}}};
    use plonky2_crypto::biguint::{CircuitBuilderBiguint, WitnessBigUint};

    use crate::{fp_plonky2::N, native::{Fp, Fp2}};

    use super::{g2_add, g2_add_unequal, g2_double, g2_scalar_mul, signature_point_check, SIG_LEN};

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    #[test]
    fn test_g2_add_unequal() {
        // env_logger::init();
        let ax = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "337725438187709982817188701931175748950561864071211469604211805451542415352866003578718608366094520056481699232210"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "325784474482020989596135374893471919876505088991873421195308352667079503424389512976821068246925718319548045276021"
            ).unwrap()),
        ]);
        let ay = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2965841325781469856973174148258785715970498867849450741444982165189412687797594966692602501064144340797710797471604"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1396501224612541682947972324170488919567615665343008985787728980681572855276817422483173426760119128141672533354119"
            ).unwrap()),
        ]);
        let bx = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3310291183651938419676930134503606039576251708119934019650494815974674760881379622302324811830103490883079904029190"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "845507222118475144290150023685070019360459684233155402409229752404383900284940551672371362493058110240418657298132"
            ).unwrap()),
        ]);
        let by = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "569469686320544423596306308487126199229297307366529623191489815159190893993668979352767262071942316086625514601662"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2551756239942517806379811015764241238167383065214268002625836091916337464087928632477808357405422759164808763594986"
            ).unwrap()),
        ]);
        let outx = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3768960129599410557225162537737286003238400530051754572454824471200864202913026112975152396185116175737023068710834"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2843653242501816279232983717246998149289638605923450990196321568072224346134709601553669097144892265594669670100681"
            ).unwrap()),
        ]);
        let outy = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2136473314670056131183153764113091685196675640973971063848296586048702180604877062503412214120535118046733529576506"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3717743359948639609414970569174500186381762539811697438986507840606082550875593852503699874848297189142874182531754"
            ).unwrap()),
        ]);

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let ax_c0 = builder.add_virtual_biguint_target(N);
        let ax_c1 = builder.add_virtual_biguint_target(N);
        let ay_c0 = builder.add_virtual_biguint_target(N);
        let ay_c1 = builder.add_virtual_biguint_target(N);
        let a = [[ax_c0, ax_c1], [ay_c0, ay_c1]];

        let bx_c0 = builder.add_virtual_biguint_target(N);
        let bx_c1 = builder.add_virtual_biguint_target(N);
        let by_c0 = builder.add_virtual_biguint_target(N);
        let by_c1 = builder.add_virtual_biguint_target(N);
        let b = [[bx_c0, bx_c1], [by_c0, by_c1]];

        let out = g2_add_unequal(&mut builder, &a, &b);

        let mut pw = PartialWitness::<F>::new();
        pw.set_biguint_target(&a[0][0], &ax.0[0].to_biguint());
        pw.set_biguint_target(&a[0][1], &ax.0[1].to_biguint());
        pw.set_biguint_target(&a[1][0], &ay.0[0].to_biguint());
        pw.set_biguint_target(&a[1][1], &ay.0[1].to_biguint());

        pw.set_biguint_target(&b[0][0], &bx.0[0].to_biguint());
        pw.set_biguint_target(&b[0][1], &bx.0[1].to_biguint());
        pw.set_biguint_target(&b[1][0], &by.0[0].to_biguint());
        pw.set_biguint_target(&b[1][1], &by.0[1].to_biguint());

        pw.set_biguint_target(&out[0][0], &outx.0[0].to_biguint());
        pw.set_biguint_target(&out[0][1], &outx.0[1].to_biguint());
        pw.set_biguint_target(&out[1][0], &outy.0[0].to_biguint());
        pw.set_biguint_target(&out[1][1], &outy.0[1].to_biguint());

        builder.print_gate_counts(0);
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();
    }

    #[test]
    fn test_g2_double() {
        // env_logger::init();
        let ax = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "337725438187709982817188701931175748950561864071211469604211805451542415352866003578718608366094520056481699232210"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "325784474482020989596135374893471919876505088991873421195308352667079503424389512976821068246925718319548045276021"
            ).unwrap()),
        ]);
        let ay = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2965841325781469856973174148258785715970498867849450741444982165189412687797594966692602501064144340797710797471604"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1396501224612541682947972324170488919567615665343008985787728980681572855276817422483173426760119128141672533354119"
            ).unwrap()),
        ]);
        let outx = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1706600946883407123219281831938721281378271382276249190372502550662898700659312875480967274178992951148217552181426"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3667242666443602243234297601464303917352028754060836539777371958000208843208072408275476423902876206704592938302165"
            ).unwrap()),
        ]);
        let outy = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1455123735227984325271077817690334450857761312547658768990224051882209081684526238004573782051265522918945273385158"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3320466234608127782197732106422214686550406898681784249598895322673540642018347203281877363138090179901504571209003"
            ).unwrap()),
        ]);

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let iso_3_a = [
            builder.constant_biguint(&0.to_biguint().unwrap()),
            builder.constant_biguint(&240.to_biguint().unwrap()),
        ];
        let iso_3_b = [
            builder.constant_biguint(&1012.to_biguint().unwrap()),
            builder.constant_biguint(&1012.to_biguint().unwrap()),
        ];

        let ax_c0 = builder.add_virtual_biguint_target(N);
        let ax_c1 = builder.add_virtual_biguint_target(N);
        let ay_c0 = builder.add_virtual_biguint_target(N);
        let ay_c1 = builder.add_virtual_biguint_target(N);
        let a = [[ax_c0, ax_c1], [ay_c0, ay_c1]];

        let out = g2_double(&mut builder, &a, &iso_3_a, &iso_3_b);

        let mut pw = PartialWitness::<F>::new();
        pw.set_biguint_target(&a[0][0], &ax.0[0].to_biguint());
        pw.set_biguint_target(&a[0][1], &ax.0[1].to_biguint());
        pw.set_biguint_target(&a[1][0], &ay.0[0].to_biguint());
        pw.set_biguint_target(&a[1][1], &ay.0[1].to_biguint());

        pw.set_biguint_target(&out[0][0], &outx.0[0].to_biguint());
        pw.set_biguint_target(&out[0][1], &outx.0[1].to_biguint());
        pw.set_biguint_target(&out[1][0], &outy.0[0].to_biguint());
        pw.set_biguint_target(&out[1][1], &outy.0[1].to_biguint());

        builder.print_gate_counts(0);
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();
    }

    #[test]
    fn test_g2_add() {
        // env_logger::init();
        let ax = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "337725438187709982817188701931175748950561864071211469604211805451542415352866003578718608366094520056481699232210"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "325784474482020989596135374893471919876505088991873421195308352667079503424389512976821068246925718319548045276021"
            ).unwrap()),
        ]);
        let ay = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2965841325781469856973174148258785715970498867849450741444982165189412687797594966692602501064144340797710797471604"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1396501224612541682947972324170488919567615665343008985787728980681572855276817422483173426760119128141672533354119"
            ).unwrap()),
        ]);
        let bx = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3310291183651938419676930134503606039576251708119934019650494815974674760881379622302324811830103490883079904029190"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "845507222118475144290150023685070019360459684233155402409229752404383900284940551672371362493058110240418657298132"
            ).unwrap()),
        ]);
        let by = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "569469686320544423596306308487126199229297307366529623191489815159190893993668979352767262071942316086625514601662"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2551756239942517806379811015764241238167383065214268002625836091916337464087928632477808357405422759164808763594986"
            ).unwrap()),
        ]);
        let outx = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3768960129599410557225162537737286003238400530051754572454824471200864202913026112975152396185116175737023068710834"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2843653242501816279232983717246998149289638605923450990196321568072224346134709601553669097144892265594669670100681"
            ).unwrap()),
        ]);
        let outy = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2136473314670056131183153764113091685196675640973971063848296586048702180604877062503412214120535118046733529576506"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3717743359948639609414970569174500186381762539811697438986507840606082550875593852503699874848297189142874182531754"
            ).unwrap()),
        ]);

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let iso_3_a = [
            builder.constant_biguint(&0.to_biguint().unwrap()),
            builder.constant_biguint(&240.to_biguint().unwrap()),
        ];
        let iso_3_b = [
            builder.constant_biguint(&1012.to_biguint().unwrap()),
            builder.constant_biguint(&1012.to_biguint().unwrap()),
        ];

        let ax_c0 = builder.add_virtual_biguint_target(N);
        let ax_c1 = builder.add_virtual_biguint_target(N);
        let ay_c0 = builder.add_virtual_biguint_target(N);
        let ay_c1 = builder.add_virtual_biguint_target(N);
        let a = [[ax_c0, ax_c1], [ay_c0, ay_c1]];

        let bx_c0 = builder.add_virtual_biguint_target(N);
        let bx_c1 = builder.add_virtual_biguint_target(N);
        let by_c0 = builder.add_virtual_biguint_target(N);
        let by_c1 = builder.add_virtual_biguint_target(N);
        let b = [[bx_c0, bx_c1], [by_c0, by_c1]];

        let fals = builder._false();

        let out = g2_add(&mut builder, &a, fals, &b, fals, &iso_3_a, &iso_3_b);

        let mut pw = PartialWitness::<F>::new();
        pw.set_biguint_target(&a[0][0], &ax.0[0].to_biguint());
        pw.set_biguint_target(&a[0][1], &ax.0[1].to_biguint());
        pw.set_biguint_target(&a[1][0], &ay.0[0].to_biguint());
        pw.set_biguint_target(&a[1][1], &ay.0[1].to_biguint());

        pw.set_biguint_target(&b[0][0], &bx.0[0].to_biguint());
        pw.set_biguint_target(&b[0][1], &bx.0[1].to_biguint());
        pw.set_biguint_target(&b[1][0], &by.0[0].to_biguint());
        pw.set_biguint_target(&b[1][1], &by.0[1].to_biguint());

        pw.set_biguint_target(&out[0][0], &outx.0[0].to_biguint());
        pw.set_biguint_target(&out[0][1], &outx.0[1].to_biguint());
        pw.set_biguint_target(&out[1][0], &outy.0[0].to_biguint());
        pw.set_biguint_target(&out[1][1], &outy.0[1].to_biguint());

        builder.print_gate_counts(0);
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();
    }

    #[test]
    fn test_g2_scalar_mul() {
        env_logger::init();
        let ax = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3219922746671482828210036408711997441423671614254909325234707044434520756052360285257107968950769890523504628275940"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1689252599334450651431125834598273362703914442067213087777626885820814565104897473205802289043260096634945919754747"
            ).unwrap()),
        ]);
        let ay = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3277365552217223927730141275188890184833071787772555827000840921808443941258778716588573376888715070179970391655322"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "583921403203359937897773959554466412643567032578544897698779952656397892876222999644067619700087458377600564507453"
            ).unwrap()),
        ]);
        let outx = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2523579754967640238723918616351685721284996518144674649571478689837790667637298382703328020485789979179436650708908"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "926383654583210622704996942518380628779065643276946198453367351460754762515870939199945068184689019420502882527581"
            ).unwrap()),
        ]);
        let outy = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3787164088273368384415735450659985644624425652571718026503769291441565414050570276349393167238939810080925158072505"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3689766260810296892747853615583585529622598940500344733471060314731353498148974741263844587195375375425544954703339"
            ).unwrap()),
        ]);

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let iso_3_b = [
            builder.constant_biguint(&4.to_biguint().unwrap()),
            builder.constant_biguint(&4.to_biguint().unwrap()),
        ];

        let ax_c0 = builder.add_virtual_biguint_target(N);
        let ax_c1 = builder.add_virtual_biguint_target(N);
        let ay_c0 = builder.add_virtual_biguint_target(N);
        let ay_c1 = builder.add_virtual_biguint_target(N);
        let p = [[ax_c0, ax_c1], [ay_c0, ay_c1]];

        let out = g2_scalar_mul(&mut builder, &p, &iso_3_b);

        let mut pw = PartialWitness::<F>::new();
        pw.set_biguint_target(&p[0][0], &ax.0[0].to_biguint());
        pw.set_biguint_target(&p[0][1], &ax.0[1].to_biguint());
        pw.set_biguint_target(&p[1][0], &ay.0[0].to_biguint());
        pw.set_biguint_target(&p[1][1], &ay.0[1].to_biguint());

        pw.set_biguint_target(&out[0][0], &outx.0[0].to_biguint());
        pw.set_biguint_target(&out[0][1], &outx.0[1].to_biguint());
        pw.set_biguint_target(&out[1][0], &outy.0[0].to_biguint());
        pw.set_biguint_target(&out[1][1], &outy.0[1].to_biguint());

        builder.print_gate_counts(0);
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();
    }

    #[test]
    fn test_signature_point_check() {
        env_logger::init();
        let x = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2132190448044539512343458281906429348357553485972550361022637600291474790426714276782518732598485406127127542511958"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1768967113711705180967647921989767607043027235135825860038026636952386389242730816293578938377273126163720266364901"
            ).unwrap()),
        ]);
        let y = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1601269830186296343258204708609068858787525822280553591425324687245481424080606221266002538737401918289754033770338"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "508402758079580872259652181430201489694066144504950057753724961054091567713555160539784585997814439522141428760875"
            ).unwrap()),
        ]);
        let sig = vec![
            139, 126,  67,  23, 196, 226,  59, 211, 144, 232, 136, 101,
            183,  50, 126, 215, 210, 110,  97, 248, 215, 138, 135,  11,
            184, 144,   5, 162, 250, 243, 244,  51, 140,  27, 110,   7,
            158,  63,  35, 135,  61,  90, 233,   5, 135,  72, 183, 229,
             13, 218, 102,  33,  65,  70,  85,  67, 129, 210, 109,  61,
             39, 103, 248,   6, 238, 111, 155, 116, 213,  81, 130, 121,
             92, 156,  15, 149,  69,  65,  43,  98, 117, 125, 244,  59,
            143,  22,  72,  75,  38,  67, 175, 183, 249,   6,  57,  86
        ];
        let sig_f: Vec<F> = sig.iter().map(|i| F::from_canonical_u8(*i)).collect();

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let x_c0 = builder.add_virtual_biguint_target(N);
        let x_c1 = builder.add_virtual_biguint_target(N);
        let point_x = [x_c0, x_c1];
        let y_c0 = builder.add_virtual_biguint_target(N);
        let y_c1 = builder.add_virtual_biguint_target(N);
        let point_y = [y_c0, y_c1];
        let point = [point_x, point_y];

        let sig = builder.add_virtual_target_arr::<SIG_LEN>();

        signature_point_check(&mut builder, &point, &sig);

        let mut pw = PartialWitness::<F>::new();
        pw.set_biguint_target(&point[0][0], &x.0[0].to_biguint());
        pw.set_biguint_target(&point[0][1], &x.0[1].to_biguint());

        pw.set_biguint_target(&point[1][0], &y.0[0].to_biguint());
        pw.set_biguint_target(&point[1][1], &y.0[1].to_biguint());

        pw.set_target_arr(&sig, &sig_f);

        builder.print_gate_counts(0);
        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();
    }

}
