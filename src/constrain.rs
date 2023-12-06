use std::marker::PhantomData;

use plonky2::{hash::hash_types::RichField, field::{extension::{Extendable, FieldExtension}, packed::PackedField}, iop::ext_target::ExtensionTarget};
use starky::{stark::Stark, constraint_consumer::ConstraintConsumer, evaluation_frame::{StarkFrame, StarkEvaluationFrame}};

use crate::{layout::{TOTAL_COLUMNS, G1_X_IDX, G1_Y_IDX, G2_X_1_IDX, G2_X_2_IDX, G2_Y_1_IDX, G2_Y_2_IDX, G2_Z_1_IDX, G2_Z_2_IDX, G1_Y_CARRY_IDX}, trace::PairingStark, native::modulus_digits};
// #[derive(Copy, Clone)]
// pub struct PairingStark<F: RichField + Extendable<D>, const D: usize> {
//     _phantom: PhantomData<F>,
// }

pub const COLUMNS: usize = TOTAL_COLUMNS;
pub const PUBLIC_INPUTS: usize = 240;

impl<F: RichField + Extendable<D>, const D: usize> Stark<F,D> for PairingStark<F, D> {

    type EvaluationFrame<FE, P, const D2: usize> = StarkFrame<P, P::Scalar, COLUMNS, PUBLIC_INPUTS>
    where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>;

        fn eval_packed_generic<FE, P, const D2: usize>(
            &self,
            vars: &Self::EvaluationFrame<FE, P, D2>,
            yield_constr: &mut ConstraintConsumer<P>,
        ) where 
            FE: FieldExtension<D2, BaseField = F>,
            P: PackedField<Scalar = FE>, {
                // println!("FE::{:?}", FE::from_canonical_u32(1550366109 as u32));

            let local_values = vars.get_local_values();
            let next_values = vars.get_next_values();
            let public_inputs = vars.get_public_inputs();

            for i in 0..12 {
                yield_constr.constraint_first_row(local_values[G1_X_IDX + i]-public_inputs[G1_X_IDX+i]);
                yield_constr.constraint_first_row(local_values[G1_Y_IDX + i]-public_inputs[G1_Y_IDX+i]);
                yield_constr.constraint_first_row(local_values[G2_X_1_IDX + i]-public_inputs[G2_X_1_IDX+i]);
                yield_constr.constraint_first_row(local_values[G2_X_2_IDX + i]-public_inputs[G2_X_2_IDX+i]);
                yield_constr.constraint_first_row(local_values[G2_Y_1_IDX + i]-public_inputs[G2_Y_1_IDX+i]);
                yield_constr.constraint_first_row(local_values[G2_Y_2_IDX + i]-public_inputs[G2_Y_2_IDX+i]);
                yield_constr.constraint_first_row(local_values[G2_Z_1_IDX + i]-public_inputs[G2_Z_1_IDX+i]);
                yield_constr.constraint_first_row(local_values[G2_Z_2_IDX + i]-public_inputs[G2_Z_2_IDX+i]);
            }

            let modulus_digits = modulus_digits();

            //  G1_Y_INDEX(row: 0) + G1_Y_INDEX(row: 1) == MODULUS
            for i in 0..12 {
                if i == 0 {
                    yield_constr.constraint_first_row(
                        local_values[G1_Y_IDX+i] + 
                        next_values[G1_Y_IDX+i] - 
                        (next_values[G1_Y_CARRY_IDX+i] * FE::from_canonical_u64(1u64<<32)) - 
                        FE::from_canonical_u32(modulus_digits[i]));
                } else {
                    yield_constr.constraint_first_row(
                        local_values[G1_Y_IDX+i] + 
                        next_values[G1_Y_CARRY_IDX + i - 1] +
                        next_values[G1_Y_IDX+i] - 
                        (next_values[G1_Y_CARRY_IDX+i] * FE::from_canonical_u64(1u64<<32)) - 
                        FE::from_canonical_u32(modulus_digits[i]));
                }
            }
        }

        type EvaluationFrameTarget = StarkFrame<ExtensionTarget<D>, ExtensionTarget<D>, COLUMNS, PUBLIC_INPUTS>;

        fn eval_ext_circuit(
        &self,
        builder: &mut plonky2::plonk::circuit_builder::CircuitBuilder<F, D>,
        vars: &Self::EvaluationFrameTarget,
        yield_constr: &mut starky::constraint_consumer::RecursiveConstraintConsumer<F, D>,
    ) {
        todo!()
    }

    fn constraint_degree(&self) -> usize {
        2
    }
}

#[cfg(test)]
mod tests {
    use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, util::{timing::TimingTree, log2_strict}};
    use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof, stark::Stark};
    use plonky2::field::types::Field;
    use crate::{constrain::PairingStark, layout::TOTAL_COLUMNS, native::modulus_digits};
    use starky::util::trace_rows_to_poly_values;

    #[test]
    fn test_constraints() {
        println!("{:?}", modulus_digits());
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = PairingStark<F, D>;

        let mut config = StarkConfig::standard_fast_config();
        config.fri_config.cap_height = 0;
        let num_rows = 2;
        
        let public_inputs: [[u32; 12]; 20] = [
            [1550366109, 1913070572, 760847606, 999580752, 3273422733, 182645169, 1634881460, 1043400770, 1526865253, 1101868890, 3712845450, 132602617],
            [3621225457, 1284733598, 2592173602, 2778433514, 3415298024, 3512038034, 2556930252, 2289409521, 759431638, 3707643405, 216427024, 234777573],
            [1115400077, 734036635, 2658976793, 3446373348, 3797461211, 2799729988, 1086715089, 1766116042, 3720719530, 4214563288, 2211874409, 287824937],
            [4070035387, 3598430679, 2371795623, 2598602036, 314293284, 3104159902, 3828298491, 1770882328, 1026148559, 2003704675, 804131021, 382850433],
            [3944640261, 440162500, 3767697757, 767512216, 3185360355, 1355179671, 2310853452, 2890628660, 2539693039, 3306767406, 473197245, 198293246],
            [920955909, 775806582, 2117093864, 286632291, 2248224021, 4208799968, 2272086148, 4009382258, 291945614, 2017047933, 1541154483, 220533456],
            [2780158026, 2572579871, 3558563268, 1947800745, 1784566622, 912901049, 1766882808, 1286945791, 2204464567, 728083964, 3377958885, 227852528],
            [1492897660, 2845803056, 3990009560, 3332584519, 1144621723, 1049137482, 2386536189, 2220905202, 28647458, 3875714686, 701911767, 391244403],
            [1046962272, 2463794046, 2040554344, 1512106597, 3133001559, 2627724492, 2495709060, 1987230313, 1633322861, 1987308329, 3160603554, 114863259],
            [2957048900, 2141359070, 2215786106, 3973259941, 1525833145, 2918817582, 802810149, 1665566873, 502762526, 865276771, 1579344890, 232443498],
            [201958429, 3121400314, 2940378037, 2374214645, 2952795062, 1597696087, 2764980398, 286604913, 2800842665, 1495589741, 3740397684, 15042526],
            [836482633, 759867038, 2352794448, 2535515106, 1747978451, 2368296533, 3317313076, 4294027901, 1936969068, 1663751038, 1349265417, 337297738],
            [4267307686, 3170365581, 2479882102, 3880812608, 1597186880, 872785182, 3049350467, 4101866147, 3780678015, 1324675101, 3811136340, 103422579],
            [3697532432, 634750133, 3569069008, 2356328970, 3543032012, 10409852, 3243624567, 493689576, 1045441715, 4190032365, 3503262611, 312525404],
            [3754663211, 2550742268, 4290899951, 2706714523, 2133903942, 2064146858, 3020213681, 2883634441, 3261009886, 1008632016, 846238921, 96286922],
            [180805577, 1055123757, 467807645, 4188838718, 3750086686, 1445627818, 2274089757, 1654529253, 2174983320, 2283008145, 3927796640, 350581781],
            [469918622, 3807777117, 452339809, 2465317856, 2627104613, 1410613535, 3830870319, 215413192, 1426843449, 3522706096, 3084418480, 178318367],
            [594226935, 1048595597, 671709702, 194481283, 1989392263, 3637504447, 969917702, 2264507263, 3011599963, 3674289074, 1656763325, 268010078],
            [2073338358, 3729215563, 3209054574, 1434035135, 3624899862, 2705112330, 2265620158, 2268616837, 1518369705, 1251775683, 3557040129, 93696833],
            [3249504444, 3340631451, 1952322004, 4019190723, 1486900056, 1458999215, 3550549922, 1865792784, 1130292958, 3352664745, 146755901, 87675763]
        ];
        let mut stark = S::new(2);
        let s_ = stark.clone();
        println!("total_cols {:?}", TOTAL_COLUMNS);
        let trace = stark.generate_trace(
            [
                public_inputs[0].clone(),
                public_inputs[1].clone()
                ],
            [
                public_inputs[2].clone(),
                public_inputs[3].clone(),
                public_inputs[4].clone(),
                public_inputs[5].clone(),
                public_inputs[6].clone(),
                public_inputs[7].clone()
                ]
            );
        // println!("{:?}", trace);
        let mut pis = Vec::new();
        for r in public_inputs.iter() {
            for e in r.iter() {
                pis.push(F::from_canonical_u32(e.clone()));
            }
        }
        let trace_poly_values = trace_rows_to_poly_values(trace.clone());
        // stark.quotient_degree_factor()
        let proof= prove::<F, C, S, D>(
            stark,
            &config,
            trace_poly_values,
            &pis,
            &mut TimingTree::default(),
        ); 
        verify_stark_proof(s_, proof.unwrap(), &config).unwrap();
    }
}