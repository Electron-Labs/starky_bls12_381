use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{hash::hash_types::RichField, field::{extension::{Extendable, FieldExtension}, types::Field, polynomial::PolynomialValues, packed::PackedField}, util::transpose, iop::ext_target::ExtensionTarget};
use starky::{stark::Stark, evaluation_frame::{StarkFrame, StarkEvaluationFrame}, constraint_consumer::ConstraintConsumer};

use crate::native::{get_u32_vec_from_literal_24, get_selector_bits_from_u32, multiply_by_slice, add_u32_slices, get_div_rem_modulus_from_biguint_12, get_u32_vec_from_literal, modulus};


// Fp Multiplication Layout
pub const X_INPUT_IDX: usize = 0;
pub const Y_INPUT_IDX: usize = X_INPUT_IDX + 12;
pub const XY_IDX: usize = Y_INPUT_IDX + 12;
pub const XY_CARRIES_IDX: usize = XY_IDX + 13;
pub const SHIFTED_XY: usize = XY_CARRIES_IDX + 12;
pub const SELECTOR: usize = SHIFTED_XY + 24;
pub const SUM: usize = SELECTOR + 12;
pub const SUM_CARRIES: usize = SUM + 25;
pub const CONSTRAIN_ROW_IDX: usize = SUM_CARRIES + 24;
// pub const EVALUATION_IDX: usize = CONSTRAIN_ROW_IDX + 1;
pub const LAST_ROW_IDX: usize = CONSTRAIN_ROW_IDX + 1;
pub const REDUCED_IDX: usize = LAST_ROW_IDX + 1;
pub const DIVISOR_IDX: usize = REDUCED_IDX + 12;
pub const RES_MOD_IDX: usize = DIVISOR_IDX + 12;
pub const RES_MOD_CARRY_IDX: usize = RES_MOD_IDX + 13;
pub const RES_MOD_SHIFTED_IDX: usize = RES_MOD_CARRY_IDX + 12;
pub const RES_MOD_SUM_IDX: usize = RES_MOD_SHIFTED_IDX + 24;
pub const RES_MOD_SUM_CARRY_IDX: usize = RES_MOD_SUM_IDX + 25;
pub const RES_REM_SUM_IDX: usize = RES_MOD_SUM_CARRY_IDX + 24;
pub const RES_REM_SUM_CARRY_IDX: usize = RES_REM_SUM_IDX + 25;



pub const TOTAL_COLUMNS: usize =  RES_REM_SUM_CARRY_IDX + 24;


pub const COLUMNS: usize = TOTAL_COLUMNS;
pub const PUBLIC_INPUTS: usize = 36;

// A (Fp) * B (Fp) => C (Fp)
#[derive(Clone)]
pub struct FpMultiplicationStark<F: RichField + Extendable<D>, const D: usize> {
    pub trace: Vec<[F; TOTAL_COLUMNS]>,
    num_rows: usize,
}

// Implement trace generator
impl<F: RichField + Extendable<D>, const D: usize> FpMultiplicationStark<F, D> {
    pub fn new(num_rows: usize) -> Self {
        Self {
             trace: vec![[F::ZERO; TOTAL_COLUMNS]; num_rows],
             num_rows,
        }
    }

    pub fn assign_u32_12(&mut self, row: usize, start_col: usize, val: [u32; 12]) {
        for i in 0..12 {
            self.trace[row][start_col + i] = F::from_canonical_u32(val[i]);
        }
    }

    pub fn assign_u32_in_series(&mut self, row: usize, start_col: usize, val: &[u32]) {
        for i in 0..val.len() {
            self.trace[row][start_col + i] = F::from_canonical_u32(val[i]);
        }
    }

    pub fn assign_cols_from_prev(&mut self, row: usize, start_col: usize, num_cols: usize) {
        assert!(row>=1);
        for i in start_col..start_col+num_cols {
            self.trace[row][start_col+i] = self.trace[row-1][start_col+i];
        }
    }

    pub fn generate_trace(&mut self, x: [u32; 12], y: [u32; 12]) -> Vec<[F; TOTAL_COLUMNS]>{
        let z = get_u32_vec_from_literal_24(BigUint::new(x.to_vec())*BigUint::new(y.to_vec()));
        let mut selector: u32 = 1;
        for row in 0..self.num_rows {
            for i in 0..12 {
                self.trace[row][X_INPUT_IDX+i] = F::from_canonical_u32(x[i]);
                self.trace[row][Y_INPUT_IDX+i] = F::from_canonical_u32(y[i]);
            }
            // for i in 0..24 {
            //     self.trace[row][EVALUATION_IDX+i] = F::from_canonical_u32(z[i]);
            // }
            let selector_u32 = get_selector_bits_from_u32(selector.clone());
            self.assign_u32_12(row, SELECTOR, selector_u32);
            selector *= 2;
        }
        // run a loop for all elements in y, each x*y[i] progress marks as one row
        let mut prev_xy_sum = [0u32; 25];
        for i in 0..12 {
            // println!("what went in  {:?}", self.trace[i][CONSTRAIN_ROW_IDX]);
            let (xy, xy_carry) = multiply_by_slice(&x, y[i]);
            self.assign_u32_in_series(i, XY_IDX, &xy);
            self.assign_u32_in_series(i, XY_CARRIES_IDX, &xy_carry);

            // fill shifted XY's
            // XY's will have 0-11 number of shifts in their respective rows
            let mut xy_shifted = [0u32; 24];
            for j in 0..13 {
                let shift = i;
                xy_shifted[j+shift] = xy[j];
            }
            self.assign_u32_in_series(i, SHIFTED_XY, &xy_shifted);

            // Fill XY_SUM, XY_SUM_CARRIES
            let (xy_sum, xy_sum_carry) = add_u32_slices(&xy_shifted, &prev_xy_sum);
            self.assign_u32_in_series(i, SUM, &xy_sum);
            self.assign_u32_in_series(i, SUM_CARRIES, &xy_sum_carry);
            // lets see sum progresses in a constrained way
            // println!("{:?}", xy_sum[0] as u64 +( xy_sum_carry[0] as u64 * (1u64<<32) as u64) - xy_shifted[0] as u64 - prev_xy_sum[0] as u64 );
            // for x in 1..24 {
            //     println!("{:?}",xy_sum[x] as u64 + (xy_sum_carry[x] as u64 * (1u64<<32) as u64) - xy_sum_carry[x-1] as u64 - xy_shifted[x] as u64 - prev_xy_sum[x] as u64 );
            // }
            // println!("{:?}", xy_sum[24] as u64 - xy_sum_carry[23] as u64);
            prev_xy_sum = xy_sum;
        }

        for i in 0..11 {
            self.trace[i][CONSTRAIN_ROW_IDX] = F::from_canonical_u32(1u32);
        }

        // Reduction to Fp using Multiplication % modulus()
        // a = div * modulus() + rem
        // a comes from above computation
        // 1. Fill div and rem in first row 
        // rem here is our final multiplication result
        // self.trace[0][CONSTRAIN_REM_IDX] = F::ONE;

        let (div, rem) = get_div_rem_modulus_from_biguint_12(BigUint::new(x.to_vec())*BigUint::new(y.to_vec()));
        
        self.assign_u32_in_series(0, REDUCED_IDX, &rem);

        // Fill trace for div * modulus()
        let modulus = get_u32_vec_from_literal(modulus());
        let mut prev_res_mod_sum = [0u32; 25];
        for i in 0..self.num_rows {
            self.assign_u32_in_series(i, DIVISOR_IDX, &div);
        }

        for i in 0..12 {
            let (res_mod, res_mod_carry) = multiply_by_slice(&div , modulus[i]);
            self.assign_u32_in_series(i, RES_MOD_IDX, &res_mod);
            self.assign_u32_in_series(i, RES_MOD_CARRY_IDX, &res_mod_carry);            

            let mut res_mod_shifted = [0u32; 24];
            for j in 0..13 {
                let shift = i;
                res_mod_shifted[j+shift] = res_mod[j];
            }
            self.assign_u32_in_series(i, RES_MOD_SHIFTED_IDX, &res_mod_shifted);

            let (res_mod_sum, res_mod_sum_carry) = add_u32_slices(&res_mod_shifted, &prev_res_mod_sum);

            self.assign_u32_in_series(i, RES_MOD_SUM_IDX, &res_mod_sum);

            
            self.assign_u32_in_series(i, RES_MOD_SUM_CARRY_IDX, &res_mod_sum_carry);

            prev_res_mod_sum = res_mod_sum;
        }

        self.trace[11][LAST_ROW_IDX] = F::ONE;

        let mut remainder = [0u32; 24];
        remainder[0..12].copy_from_slice(&rem);

        let (res_rem_sum, res_rem_sum_carry) = add_u32_slices(&remainder, &prev_res_mod_sum);
        for i in 0..self.num_rows {
            self.assign_u32_in_series(i, RES_REM_SUM_IDX, &res_rem_sum);
            self.assign_u32_in_series(i, RES_REM_SUM_CARRY_IDX, &res_rem_sum_carry);
        }
        let local_values = self.trace[11].clone();

        self.trace.clone()
    }
}

pub fn trace_rows_to_poly_values<F: Field>(
    trace_rows: Vec<[F; TOTAL_COLUMNS]>,
) -> Vec<PolynomialValues<F>> {
    let trace_row_vecs = trace_rows.into_iter().map(|row| row.to_vec()).collect_vec();
    let trace_col_vecs: Vec<Vec<F>> = transpose(&trace_row_vecs);
    trace_col_vecs
        .into_iter()
        .map(|column| PolynomialValues::new(column))
        .collect()
}

// Implement constraint generator
impl<F: RichField + Extendable<D>, const D: usize> Stark<F,D> for FpMultiplicationStark<F, D> {

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
            let local_values = vars.get_local_values();
            let next_values = vars.get_next_values();
            let public_inputs = vars.get_public_inputs();

            for i in 0..12 {
                yield_constr.constraint_first_row(local_values[X_INPUT_IDX+i] - public_inputs[i]);
                yield_constr.constraint_first_row(local_values[Y_INPUT_IDX+i] - public_inputs[i+12]);
                yield_constr.constraint_first_row(local_values[REDUCED_IDX+i] - public_inputs[i+24]);
            }
            for i in 0..12 {
                yield_constr.constraint_transition(local_values[X_INPUT_IDX+i] - next_values[X_INPUT_IDX+i]);
                yield_constr.constraint_transition(local_values[Y_INPUT_IDX+i] - next_values[Y_INPUT_IDX+i]);
                yield_constr.constraint_transition(local_values[DIVISOR_IDX+i] - next_values[DIVISOR_IDX+i]);
            }

            for i in 0..25 {
                yield_constr.constraint_transition(local_values[RES_REM_SUM_IDX + i] - next_values[RES_REM_SUM_IDX + i]);
            }
            for i in 0..24 {
                yield_constr.constraint_transition(local_values[RES_REM_SUM_CARRY_IDX + i] - next_values[RES_REM_SUM_CARRY_IDX + i]);
            }
            // for i in 0..24 {
            //     yield_constr.constraint_first_row(local_values[EVALUATION_IDX+i] - public_inputs[i+24]);
            //     yield_constr.constraint_transition(local_values[EVALUATION_IDX+i] - next_values[EVALUATION_IDX+i]);
            // }

            // Check if the multiplication happens correct at each level
            for i in 0..12 {
                for j in 0..12 {
                    if j == 0 {
                        yield_constr.constraint_transition(
                            local_values[SELECTOR + i] *
                            (
                                local_values[X_INPUT_IDX + j] * local_values[Y_INPUT_IDX+i]
                                - local_values[XY_IDX + j]
                                - (local_values[XY_CARRIES_IDX + j] * FE::from_canonical_u64(1<<32))
                            )
                        )
                    } else {
                        yield_constr.constraint_transition(
                            local_values[SELECTOR + i] *
                            (
                                local_values[X_INPUT_IDX+j] * local_values[Y_INPUT_IDX+i]
                                + local_values[XY_CARRIES_IDX + j - 1]
                                - local_values[XY_IDX + j]
                                - (local_values[XY_CARRIES_IDX + j] * FE::from_canonical_u64(1<<32))
                            )
                        )
                    }
                }
            }
            yield_constr.constraint_transition(local_values[XY_IDX + 12] - local_values[XY_CARRIES_IDX + 11]);

            // Constrain XY SHIFTING
            for i in 0..12 {
                // shift is decided by selector
                for j in 0..13 {
                   yield_constr.constraint_transition(
                    local_values[SELECTOR+i] * 
                        (
                            local_values[SHIFTED_XY + j + i] - local_values[XY_IDX + j]
                        )
                    )
                }   
            }

            // Constrain addition at each row
            // 1. Constrain XY_SUM at row 0 is same as XY_SHIFTED
            // 2. Constrain XY_SUM_CARRIES at row 0 are all 0
            for j in 0..24{
                yield_constr.constraint_first_row(local_values[SUM + j] - local_values[SHIFTED_XY + j]);
                yield_constr.constraint_first_row(local_values[SUM_CARRIES + j] )
            }
            yield_constr.constraint_first_row(local_values[SUM + 24]);

            // println!("what got out {:?}", local_values[CONSTRAIN_ROW_IDX]);

            // 3. Constrain addition
            yield_constr.constraint_transition(
                local_values[CONSTRAIN_ROW_IDX] * 
                    (next_values[SUM] + 
                    (next_values[SUM_CARRIES] * FE::from_canonical_u64(1<<32)) -
                    next_values[SHIFTED_XY] -
                    local_values[SUM])
            );
            for j in 1..24 {
                yield_constr.constraint_transition(
                    local_values[CONSTRAIN_ROW_IDX] * 
                    (next_values[SUM + j] + 
                    (next_values[SUM_CARRIES + j] * FE::from_canonical_u64(1<<32)) -
                    next_values[SHIFTED_XY + j] -
                    local_values[SUM + j] -
                    next_values[SUM_CARRIES + j - 1])
                )
            }
            yield_constr.constraint_transition(local_values[CONSTRAIN_ROW_IDX] * (next_values[SUM + 24] - next_values[SUM_CARRIES + 23]));

            // constrain outputs
            // for j in 0..24 {
            //     yield_constr.constraint_transition(local_values[LAST_ROW_IDX] * (
            //         local_values[SUM + j] - public_inputs[24 + j]
            //     ))
            // }


            // -------------------
            let modulus = get_u32_vec_from_literal(modulus());

            for i in 0..12 {
                for j in 0..12 {
                    if j == 0 {
                        yield_constr.constraint_transition(
                            local_values[SELECTOR + i] *
                            (
                                local_values[DIVISOR_IDX + j] * FE::from_canonical_u32(modulus[i])
                                - local_values[RES_MOD_IDX + j]
                                - (local_values[RES_MOD_CARRY_IDX + j] * FE::from_canonical_u64(1<<32))
                            )
                        )
                    } else {
                        yield_constr.constraint_transition(
                            local_values[SELECTOR + i] *
                            (
                                local_values[DIVISOR_IDX+j] * FE::from_canonical_u32(modulus[i])
                                + local_values[RES_MOD_CARRY_IDX + j - 1]
                                - local_values[RES_MOD_IDX + j]
                                - (local_values[RES_MOD_CARRY_IDX + j] * FE::from_canonical_u64(1<<32))
                            )
                        )
                    }
                }
            }
            yield_constr.constraint_transition(local_values[RES_MOD_IDX + 12] - local_values[RES_MOD_CARRY_IDX + 11]);

            // Constrain RES_MOD SHIFTING
            for i in 0..12 {
                // shift is decided by selector
                for j in 0..13 {
                   yield_constr.constraint_transition(
                    local_values[SELECTOR+i] * 
                        (
                            local_values[RES_MOD_SHIFTED_IDX + j + i] - local_values[RES_MOD_IDX + j]
                        )
                    )
                }   
            }

            for j in 0..24{
                yield_constr.constraint_first_row(local_values[RES_MOD_SUM_IDX + j] - local_values[RES_MOD_SHIFTED_IDX + j]);
                yield_constr.constraint_first_row(local_values[RES_MOD_SUM_CARRY_IDX + j] )
            }
            yield_constr.constraint_first_row(local_values[RES_MOD_SUM_IDX + 24]);

            yield_constr.constraint_transition(
                local_values[CONSTRAIN_ROW_IDX] * 
                    (next_values[RES_MOD_SUM_IDX] + 
                    (next_values[RES_MOD_SUM_CARRY_IDX] * FE::from_canonical_u64(1<<32)) -
                    next_values[RES_MOD_SHIFTED_IDX] -
                    local_values[RES_MOD_SUM_IDX])
            );
            for j in 1..24 {
                yield_constr.constraint_transition(
                    local_values[CONSTRAIN_ROW_IDX] * 
                    (next_values[RES_MOD_SUM_IDX + j] + 
                    (next_values[RES_MOD_SUM_CARRY_IDX + j] * FE::from_canonical_u64(1<<32)) -
                    next_values[RES_MOD_SHIFTED_IDX + j] -
                    local_values[RES_MOD_SUM_IDX + j] -
                    next_values[RES_MOD_SUM_CARRY_IDX + j - 1])
                )
            }
            yield_constr.constraint_transition(local_values[CONSTRAIN_ROW_IDX] * (next_values[RES_MOD_SUM_IDX + 24] - next_values[RES_MOD_SUM_CARRY_IDX + 23]));

            // Constraining ab "+" y
            for j in 0..25 {
                if j == 0 {
                    yield_constr.constraint_transition(
                        local_values[LAST_ROW_IDX] * (
                            local_values[RES_REM_SUM_IDX + j]
                            + (local_values[RES_REM_SUM_CARRY_IDX + j] * FE::from_canonical_u64(1<<32))
                            - local_values[RES_MOD_SUM_IDX + j]
                            - public_inputs[24+j]
                        )
                    )
                } 
                else if j < 12{
                    yield_constr.constraint_transition(
                        local_values[LAST_ROW_IDX] * (
                            local_values[RES_REM_SUM_IDX + j]
                            + (local_values[RES_REM_SUM_CARRY_IDX + j] * FE::from_canonical_u64(1<<32))
                            - local_values[RES_MOD_SUM_IDX + j]
                            - public_inputs[24+j]
                            - local_values[RES_REM_SUM_CARRY_IDX + j - 1]
                        )
                    )
                    
                } else if (j < 24) {
                    yield_constr.constraint_transition(
                        local_values[LAST_ROW_IDX] * (
                            local_values[RES_REM_SUM_IDX + j]
                            + (local_values[RES_REM_SUM_CARRY_IDX + j] * FE::from_canonical_u64(1<<32))
                            - local_values[RES_MOD_SUM_IDX + j]
                            - local_values[RES_REM_SUM_CARRY_IDX + j - 1]
                        )
                    )
                } else {
                    yield_constr.constraint_transition(
                        local_values[LAST_ROW_IDX] * (
                            local_values[RES_REM_SUM_IDX + j]
                        )
                    )
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
    use num_bigint::BigUint;
    use plonky2::{plonk::config::{PoseidonGoldilocksConfig, GenericConfig}, util::timing::TimingTree};
    use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};
    use plonky2::field::types::Field;
    use crate::{native::{get_u32_vec_from_literal_24, modulus, get_u32_vec_from_literal}, fp_mult_starky::FpMultiplicationStark};
    use starky::util::trace_rows_to_poly_values;

    #[test]
    fn test_big_mul() {
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