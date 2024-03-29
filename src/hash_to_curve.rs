use std::str::FromStr;

use num_bigint::{BigUint, ToBigUint};
use plonky2::{field::extension::Extendable, hash::hash_types::RichField, iop::{generator::{GeneratedValues, SimpleGenerator}, target::{BoolTarget, Target}, witness::{PartitionWitness, WitnessWrite}}, plonk::{circuit_builder::CircuitBuilder, circuit_data::CommonCircuitData}, util::serialization::{Buffer, IoResult, Read, Write}};
use plonky2_crypto::{biguint::{BigUintTarget, CircuitBuilderBiguint, GeneratedValuesBigUint, WitnessBigUint}, u32::arithmetic_u32::U32Target};

use crate::{fp2_plonky2::{add_fp2, div_fp2, frobenius_map, is_zero, mul_fp2, negate_fp2, range_check_fp2, sgn0_fp2, Fp2Target}, fp_plonky2::{mul_fp, N}, g2_plonky2::{g2_add, g2_double, g2_negate, g2_scalar_mul, PointG2Target}, hash_to_field::hash_to_field, native::{modulus, Fp, Fp2, Pow}};

pub const ISOGENY_COEFFICIENTS_G2: [[[&str; 2]; 4]; 4] = [
    [
        [
            "3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033",
            "0",
        ],
        [
            "2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526",
            "1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261",
        ],
        [
            "0",
            "2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522",
        ],
        [
            "889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542",
            "889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542",
        ],
    ],
    [
        [
            "0",
            "0",
        ],
        [
            "1",
            "0",
        ],
        [
            "12",
            "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775",
        ],
        [
            "0",
            "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715",
        ],
    ],
    [
        [
            "2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776",
            "0",
        ],
        [
            "2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524",
            "1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263",
        ],
        [
            "0",
            "889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518",
        ],
        [
            "3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558",
            "3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558",
        ],
    ],
    [
        [
            "1",
            "0",
        ],
        [
            "18",
            "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769",
        ],
        [
            "0",
            "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571",
        ],
        [
            "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355",
            "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355",
        ],
    ],
];

pub fn map_to_curve_simple_swu_9mod16<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    t: &Fp2Target,
) -> PointG2Target {
    let zero = builder.zero();

    let iso_3_a = [
        builder.constant_biguint(&0.to_biguint().unwrap()),
        builder.constant_biguint(&240.to_biguint().unwrap()),
    ];
    let iso_3_b = [
        builder.constant_biguint(&1012.to_biguint().unwrap()),
        builder.constant_biguint(&1012.to_biguint().unwrap()),
    ];
    let iso_3_z = [
        builder.constant_biguint(&(modulus() - 2u32)),
        builder.constant_biguint(&(modulus() - 1u32)),
    ];
    let one = [
        builder.constant_biguint(&1.to_biguint().unwrap()),
        builder.constant_biguint(&0.to_biguint().unwrap()),
    ];

    let t2 = mul_fp2(builder, &t, &t);
    let iso_3_z_t2 = mul_fp2(builder, &iso_3_z, &t2);
    let iso_3_z_t2_2 = mul_fp2(builder, &iso_3_z_t2, &iso_3_z_t2);
    let ztzt = add_fp2(builder, &iso_3_z_t2, &iso_3_z_t2_2);
    let iso_3_a_ztzt = mul_fp2(builder, &iso_3_a, &ztzt);
    let denominator_tmp = negate_fp2(builder, &iso_3_a_ztzt);
    let ztzt_1 = add_fp2(builder, &ztzt, &one);
    let numerator = mul_fp2(builder, &iso_3_b, &ztzt_1);

    let cmp = is_zero(builder, &denominator_tmp);
    let iso_3_z_iso_3_a = [
        builder.constant_biguint(&240.to_biguint().unwrap()),
        builder.constant_biguint(&(modulus() - 480u32)),
    ];
    let denominator = [
        BigUintTarget {
            limbs: (0..N)
                .into_iter()
                .map(|i| U32Target(
                    if i < iso_3_z_iso_3_a[0].num_limbs() { builder.select(cmp, iso_3_z_iso_3_a[0].limbs[i].0, denominator_tmp[0].limbs[i].0) }
                    else { builder.select(cmp, zero, denominator_tmp[0].limbs[i].0) }
                ))
                .collect::<Vec<U32Target>>()
        },
        BigUintTarget {
            limbs: (0..N)
                .into_iter()
                .map(|i| U32Target(
                    builder.select(cmp, iso_3_z_iso_3_a[1].limbs[i].0, denominator_tmp[1].limbs[i].0)
                ))
                .collect::<Vec<U32Target>>()
        },
    ];
    let x0 = div_fp2(builder, &numerator, &denominator);
    let x0_2 = mul_fp2(builder, &x0, &x0);
    let x0_3 = mul_fp2(builder,&x0_2, &x0);
    let a_x0 = mul_fp2(builder, &iso_3_a, &x0);
    let x0_3_a_x0 = add_fp2(builder, &x0_3, &a_x0);
    let gx0 = add_fp2(builder, &x0_3_a_x0, &iso_3_b);

    let x1 = mul_fp2(builder, &iso_3_z_t2, &x0);
    let xi3t6 = mul_fp2(builder, &iso_3_z_t2_2, &iso_3_z_t2);
    let gx1 = mul_fp2(builder, &xi3t6, &gx0);

    let is_square = builder.add_virtual_bool_target_unsafe();
    let sqrt = [
        builder.add_virtual_biguint_target(N),
        builder.add_virtual_biguint_target(N),
    ];
    builder.add_simple_generator(SqrtGenerator {
        t: t.clone(),
        x0: gx0.clone(),
        x1: gx1.clone(),
        is_square,
        sqrt: sqrt.clone(),
    });
    builder.assert_bool(is_square);
    range_check_fp2(builder, &sqrt);
    let sqrt2 = mul_fp2(builder, &sqrt, &sqrt);
    let gx0_gx1_select = [
        BigUintTarget {
            limbs: (0..N).into_iter().map(|i| U32Target(builder.select(is_square, gx0[0].limbs[i].0, gx1[0].limbs[i].0))).collect::<Vec<U32Target>>(),
        },
        BigUintTarget {
            limbs: (0..N).into_iter().map(|i| U32Target(builder.select(is_square, gx0[1].limbs[i].0, gx1[1].limbs[i].0))).collect::<Vec<U32Target>>(),
        },
    ];
    builder.connect_biguint(&gx0_gx1_select[0], &sqrt2[0]);
    builder.connect_biguint(&gx0_gx1_select[1], &sqrt2[1]);

    let sgn_t = sgn0_fp2(builder, t);
    let sgn_sqrt = sgn0_fp2(builder, &sqrt);
    let sgn_eq = builder.is_equal(sgn_t.target, sgn_sqrt.target);
    let sqrt_negate = negate_fp2(builder, &sqrt);
    let y = [
        BigUintTarget {
            limbs: (0..N).into_iter().map(|i| U32Target(builder.select(sgn_eq, sqrt[0].limbs[i].0, sqrt_negate[0].limbs[i].0))).collect::<Vec<U32Target>>(),
        },
        BigUintTarget {
            limbs: (0..N).into_iter().map(|i| U32Target(builder.select(sgn_eq, sqrt[1].limbs[i].0, sqrt_negate[1].limbs[i].0))).collect::<Vec<U32Target>>(),
        },
    ];
    let x0_x1_select = [
        BigUintTarget {
            limbs: (0..N).into_iter().map(|i| U32Target(builder.select(is_square, x0[0].limbs[i].0, x1[0].limbs[i].0))).collect::<Vec<U32Target>>(),
        },
        BigUintTarget {
            limbs: (0..N).into_iter().map(|i| U32Target(builder.select(is_square, x0[1].limbs[i].0, x1[1].limbs[i].0))).collect::<Vec<U32Target>>(),
        },
    ];

    [x0_x1_select, y]
}

pub fn isogeny_map<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    input: &PointG2Target
) -> PointG2Target {
    let x = &input[0];
    let x_sq = mul_fp2(builder, x, x);
    let x_cu = mul_fp2(builder, &x_sq, x);

    let coeffs = ISOGENY_COEFFICIENTS_G2.iter().map(|c_arr| c_arr.iter().map(|c| {
        let c0 = BigUint::from_str(c[0]).unwrap();
        let c1 = BigUint::from_str(c[1]).unwrap();
        [builder.constant_biguint(&c0), builder.constant_biguint(&c1)]
    }).collect::<Vec<Fp2Target>>()).collect::<Vec<Vec<Fp2Target>>>();

    let x_coeffs = mul_fp2(builder, x, &coeffs[0][2]);
    let x_sq_coeffs = mul_fp2(builder, &x_sq, &coeffs[0][1]);
    let x_cu_coeffs = mul_fp2(builder, &x_cu, &coeffs[0][0]);
    let x_num = add_fp2(builder, &coeffs[0][3], &x_coeffs);
    let x_num = add_fp2(builder, &x_num, &x_sq_coeffs);
    let x_num = add_fp2(builder, &x_num, &x_cu_coeffs);

    let x_coeffs = mul_fp2(builder, x, &coeffs[1][2]);
    let x_den = add_fp2(builder, &coeffs[1][3], &x_coeffs);
    let x_den = add_fp2(builder, &x_den, &x_sq);

    let x_coeffs = mul_fp2(builder, x, &coeffs[2][2]);
    let x_sq_coeffs = mul_fp2(builder, &x_sq, &coeffs[2][1]);
    let x_cu_coeffs = mul_fp2(builder, &x_cu, &coeffs[2][0]);
    let y_num = add_fp2(builder, &coeffs[2][3], &x_coeffs);
    let y_num = add_fp2(builder, &y_num, &x_sq_coeffs);
    let y_num = add_fp2(builder, &y_num, &x_cu_coeffs);

    let x_coeffs = mul_fp2(builder, x, &coeffs[3][2]);
    let x_sq_coeffs = mul_fp2(builder, &x_sq, &coeffs[3][1]);
    let y_den = add_fp2(builder, &coeffs[3][3], &x_coeffs);
    let y_den = add_fp2(builder, &y_den, &x_sq_coeffs);
    let y_den = add_fp2(builder, &y_den, &x_cu);

    let x_new = div_fp2(builder, &x_num, &x_den);
    let y_coeff = div_fp2(builder, &y_num, &y_den);
    let y_new = mul_fp2(builder, &input[1], &y_coeff);

    [x_new, y_new]
}

pub fn endomorphism_psi<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    inp: &PointG2Target,
) -> PointG2Target {
    let c0 = [
        builder.constant_biguint(&BigUint::from_str("0").unwrap()),
        builder.constant_biguint(&BigUint::from_str("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437").unwrap()),
    ];
    let c1 = [
        builder.constant_biguint(&BigUint::from_str("2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530").unwrap()),
        builder.constant_biguint(&BigUint::from_str("1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257").unwrap()),
    ];
    let frob = [
        frobenius_map(builder, &inp[0], 1),
        frobenius_map(builder, &inp[1], 1),
    ];
    [
        mul_fp2(builder, &c0, &frob[0]),
        mul_fp2(builder, &c1, &frob[1]),
    ]
}

pub fn endomorphism_psi2<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    inp: &PointG2Target,
) -> PointG2Target {
    let c = builder.constant_biguint(&BigUint::from_str("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap());
    [
        [
            mul_fp(builder, &inp[0][0], &c),
            mul_fp(builder, &inp[0][1], &c),
        ],
        negate_fp2(builder, &inp[1]),
    ]
}

pub fn clear_cofactor_g2<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    inp: &PointG2Target,
) -> PointG2Target {
    let a = [
        builder.constant_biguint(&BigUint::from_str("0").unwrap()),
        builder.constant_biguint(&BigUint::from_str("0").unwrap()),
    ];
    let b = [
        builder.constant_biguint(&BigUint::from_str("4").unwrap()),
        builder.constant_biguint(&BigUint::from_str("4").unwrap()),
    ];
    let fals = builder._false();
    let x_p = g2_scalar_mul(builder, inp, &b);
    let psi_p = endomorphism_psi(builder, inp);
    let neg_p = g2_negate(builder, &inp);
    let neg_psi_p = g2_negate(builder, &psi_p);
    let double_p = g2_double(builder, &inp, &a, &b);
    let psi2_2p = endomorphism_psi2(builder, &double_p);
    
    let add0 = g2_add(builder, &x_p, fals, &inp, fals, &a, &b);
    let add1 = g2_add(builder, &add0, fals, &neg_psi_p, fals, &a, &b);
    let x_add1 = g2_scalar_mul(builder, &add1, &b);
    let add2 = g2_add(builder, &x_add1, fals, &neg_p, fals, &a, &b);
    let add3 = g2_add(builder, &add2, fals, &neg_psi_p, fals, &a, &b);
    let add4 = g2_add(builder, &add3, fals, &psi2_2p, fals, &a, &b);
    add4
}

pub fn hash_to_curve<F: RichField + Extendable<D>,
    const D: usize
>(
    builder: &mut CircuitBuilder<F, D>,
    msg: &[Target],
) -> PointG2Target {
    let iso_3_a = [
        builder.constant_biguint(&0.to_biguint().unwrap()),
        builder.constant_biguint(&240.to_biguint().unwrap()),
    ];
    let iso_3_b = [
        builder.constant_biguint(&1012.to_biguint().unwrap()),
        builder.constant_biguint(&1012.to_biguint().unwrap()),
    ];

    let u = hash_to_field(builder, msg, 2);
    let pt1 = map_to_curve_simple_swu_9mod16(builder, &u[0]);
    let pt2 = map_to_curve_simple_swu_9mod16(builder, &u[1]);
    let no = builder._false();
    let pt1pt2 = g2_add(builder, &pt1, no, &pt2, no, &iso_3_a, &iso_3_b);
    let isogeny_mapping = isogeny_map(builder, &pt1pt2);
    let clear_cofactor = clear_cofactor_g2(builder, &isogeny_mapping);
    clear_cofactor
}

#[derive(Debug, Default)]
pub struct SqrtGenerator {
    t: Fp2Target,
    x0: Fp2Target,
    x1: Fp2Target,
    is_square: BoolTarget,
    sqrt: Fp2Target,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for SqrtGenerator {
    fn id(&self) -> String {
        "Fp2SqrtGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.t.iter().chain(self.x0.iter().chain(self.x1.iter())).flat_map(|f| f.limbs.iter().map(|l| l.0)).collect::<Vec<Target>>()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let x0_c0 = witness.get_biguint_target(self.x0[0].clone());
        let x0_c1 = witness.get_biguint_target(self.x0[1].clone());

        let x0_fp2 = Fp2([Fp::get_fp_from_biguint(x0_c0), Fp::get_fp_from_biguint(x0_c1)]);
        let p2_7_16 = (modulus().pow(2) + 7u32) / 16u32;
        let sqrt_candidate = x0_fp2.pow(Fp2::one(), p2_7_16);
        let roots = Fp2::roots_of_unity_8th();
        let mut is_square = false;
        let mut sqrt_witness = Fp2::zero();
        for root in roots {
            let sqrt_tmp = sqrt_candidate * root;
            if sqrt_tmp * sqrt_tmp == x0_fp2 {
                is_square = true;
                sqrt_witness = sqrt_tmp;
                break;
            }
        }
        out_buffer.set_bool_target(self.is_square, is_square);
        if is_square {
            out_buffer.set_biguint_target(&self.sqrt[0], &sqrt_witness.0[0].to_biguint());
            out_buffer.set_biguint_target(&self.sqrt[1], &sqrt_witness.0[1].to_biguint());
            return;
        }

        let t_c0 = witness.get_biguint_target(self.t[0].clone());
        let t_c1 = witness.get_biguint_target(self.t[1].clone());
        let t_fp2 = Fp2([Fp::get_fp_from_biguint(t_c0), Fp::get_fp_from_biguint(t_c1)]);

        let x1_c0 = witness.get_biguint_target(self.x1[0].clone());
        let x1_c1 = witness.get_biguint_target(self.x1[1].clone());
        let x1_fp2 = Fp2([Fp::get_fp_from_biguint(x1_c0), Fp::get_fp_from_biguint(x1_c1)]);

        let t3 = t_fp2*t_fp2*t_fp2;
        let sqrt_candidate = sqrt_candidate * t3;
        let etas = Fp2::etas();
        let mut is_square1 = false;
        for eta in etas {
            let sqrt_tmp = sqrt_candidate * eta;
            if sqrt_tmp * sqrt_tmp == x1_fp2 {
                is_square1 = true;
                sqrt_witness = sqrt_tmp;
                break;
            }
        }
        assert!(is_square1, "Failed in square root generator");
        out_buffer.set_biguint_target(&self.sqrt[0], &sqrt_witness.0[0].to_biguint());
        out_buffer.set_biguint_target(&self.sqrt[1], &sqrt_witness.0[1].to_biguint());
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        self.t[0].serialize(dst)?;
        self.t[1].serialize(dst)?;
        self.x0[0].serialize(dst)?;
        self.x0[1].serialize(dst)?;
        self.x1[0].serialize(dst)?;
        self.x1[1].serialize(dst)?;
        dst.write_target_bool(self.is_square)?;
        self.sqrt[0].serialize(dst)?;
        self.sqrt[1].serialize(dst)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self>
    where
        Self: Sized {
        let t_c0 = BigUintTarget::deserialize(src)?;
        let t_c1 = BigUintTarget::deserialize(src)?;
        let x0_c0 = BigUintTarget::deserialize(src)?;
        let x0_c1 = BigUintTarget::deserialize(src)?;
        let x1_c0 = BigUintTarget::deserialize(src)?;
        let x1_c1 = BigUintTarget::deserialize(src)?;
        let is_square = src.read_target_bool()?;
        let sqrt_c0 = BigUintTarget::deserialize(src)?;
        let sqrt_c1 = BigUintTarget::deserialize(src)?;
        Ok(Self {
            t: [t_c0, t_c1],
            x0: [x0_c0, x0_c1],
            x1: [x1_c0, x1_c1],
            is_square,
            sqrt: [sqrt_c0, sqrt_c1],
        })
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use num_bigint::BigUint;
    use plonky2::{field::types::Field, iop::witness::{PartialWitness, WitnessWrite}, plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig, config::{GenericConfig, PoseidonGoldilocksConfig}}};
    use plonky2_crypto::biguint::{CircuitBuilderBiguint, WitnessBigUint};

    use crate::{fp_plonky2::N, native::{Fp, Fp2}};

    use super::{hash_to_curve, isogeny_map};

    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    #[test]
    fn test_hash_to_curve() {
        env_logger::init();
        let config = CircuitConfig::standard_recursion_config();
        
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let msg = vec![0; 0];

        let msg_targets = builder.add_virtual_targets(msg.len());
        let point_g2 = hash_to_curve(&mut builder, &msg_targets);
        builder.print_gate_counts(0);

        let data = builder.build::<C>();
        let mut pw = PartialWitness::<F>::new();
        let msg_f = msg.iter().map(|m| F::from_canonical_u32(*m)).collect::<Vec<F>>();
        pw.set_target_arr(&msg_targets, &msg_f);
        pw.set_biguint_target(&point_g2[0][0], &BigUint::from_str("2484880953070652509895159898261749949971419256101265549903463729658081179969788208734336814677878439015289354663558").unwrap());
        pw.set_biguint_target(&point_g2[0][1], &BigUint::from_str("571286950361770968319560191831515067050084989489837870994029396792668285219017899793859671802388182901315402858724").unwrap());
        pw.set_biguint_target(&point_g2[1][0], &BigUint::from_str("3945400848309661287520855376438021610375515007889273149322439985738679863089347725379973912108534346949384256127526").unwrap());
        pw.set_biguint_target(&point_g2[1][1], &BigUint::from_str("1067268791373784971379690868996146496995005458163356395218843329703930727067637736115073576974603814754170298346268").unwrap());

        let proof = data.prove(pw).unwrap();
        data.verify(proof).unwrap();

    }

    #[test]
    fn test_isogeny_map() {
        env_logger::init();
        let ax = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3768960129599410557225162537737286003238400530051754572454824471200864202913026112975152396185116175737023068710834"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2843653242501816279232983717246998149289638605923450990196321568072224346134709601553669097144892265594669670100681"
            ).unwrap()),
        ]);
        let ay = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "2136473314670056131183153764113091685196675640973971063848296586048702180604877062503412214120535118046733529576506"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3717743359948639609414970569174500186381762539811697438986507840606082550875593852503699874848297189142874182531754"
            ).unwrap()),
        ]);
        let outx = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3219922746671482828210036408711997441423671614254909325234707044434520756052360285257107968950769890523504628275940"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "1689252599334450651431125834598273362703914442067213087777626885820814565104897473205802289043260096634945919754747"
            ).unwrap()),
        ]);
        let outy = Fp2([
            Fp::get_fp_from_biguint(BigUint::from_str(
                "3277365552217223927730141275188890184833071787772555827000840921808443941258778716588573376888715070179970391655322"
            ).unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str(
                "583921403203359937897773959554466412643567032578544897698779952656397892876222999644067619700087458377600564507453"
            ).unwrap()),
        ]);

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let ax_c0 = builder.add_virtual_biguint_target(N);
        let ax_c1 = builder.add_virtual_biguint_target(N);
        let ay_c0 = builder.add_virtual_biguint_target(N);
        let ay_c1 = builder.add_virtual_biguint_target(N);
        let a = [[ax_c0, ax_c1], [ay_c0, ay_c1]];

        let out = isogeny_map(&mut builder, &a);

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
}
