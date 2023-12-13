use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{hash::hash_types::RichField, field::{extension::{Extendable, FieldExtension}, types::Field, polynomial::PolynomialValues, packed::PackedField}, util::transpose, iop::ext_target::ExtensionTarget, gates::public_input};
use starky::{stark::Stark, evaluation_frame::{StarkFrame, StarkEvaluationFrame}, constraint_consumer::ConstraintConsumer};

use crate::native::{get_u32_vec_from_literal_24, get_selector_bits_from_u32, multiply_by_slice, add_u32_slices, get_div_rem_modulus_from_biguint_12, get_u32_vec_from_literal, modulus, add_u32_slices_1};

// [TODO]
// 1. Constrain mult result to be < modulus
// 2. Check global selector failing for mult


// Fp Multiplication layout offsets
pub const X_INPUT_OFFSET: usize = 0;
pub const Y_INPUT_OFFSET: usize = X_INPUT_OFFSET + 12;
pub const XY_OFFSET: usize = Y_INPUT_OFFSET + 12;
pub const XY_CARRIES_OFFSET: usize = XY_OFFSET + 13;
pub const SHIFTED_XY_OFFSET: usize = XY_CARRIES_OFFSET + 12;
pub const SELECTOR_OFFSET: usize = SHIFTED_XY_OFFSET + 24;
pub const SUM_OFFSET: usize = SELECTOR_OFFSET + 12;
pub const SUM_CARRIES_OFFSET: usize = SUM_OFFSET + 24;
pub const MULTIPLICATION_SELECTOR_OFFSET: usize = SUM_CARRIES_OFFSET + 24;

pub const MULTIPLICATION_TOTAL_COLUMNS: usize = MULTIPLICATION_SELECTOR_OFFSET + 1;


// Fp steps final addition layout offsets

// Circuit specific layout Fp multiplication
pub const  MULTIPLICATION_1_OFFSET: usize = MULTIPLICATION_TOTAL_COLUMNS;
pub const  MULTIPLICATION_2_OFFSET: usize = MULTIPLICATION_1_OFFSET + MULTIPLICATION_TOTAL_COLUMNS;
pub const REDUCED_OFFSET: usize = MULTIPLICATION_2_OFFSET + 1;
pub const ADDITION_CHECK_OFFSET: usize = REDUCED_OFFSET + 12;
// (div*mod)+res offset
pub const DIV_RES_SUM_OFFSET: usize = ADDITION_CHECK_OFFSET + 1;
pub const DIV_RES_CARRY_OFFSET: usize = DIV_RES_SUM_OFFSET + 24;
pub const TOTAL_COLUMNS: usize = DIV_RES_CARRY_OFFSET + 24;


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


    pub fn fill_addition_trace(&mut self, x: &[u32; 24], y: &[u32; 24], row: usize,
        start_col: usize) { 
        self.trace[row][start_col + ADDITION_CHECK_OFFSET] = F::ONE;
        let (x_y_sum, x_y_sum_carry) = add_u32_slices(&x, &y);
        self.assign_u32_in_series(row, start_col + DIV_RES_SUM_OFFSET, &x_y_sum);
        self.assign_u32_in_series(row, start_col + DIV_RES_CARRY_OFFSET, &x_y_sum_carry);
    }

    // Fills from start_row..end_row+1
    pub fn fill_multiplication_trace_no_mod_reduction(&mut self, x: &[u32; 12], y: &[u32; 12], start_row: usize, end_row: usize, 
        start_col: usize, end_col: usize ) {
        // [TODO]:
        // 1. Assert end_row - start_row + 1 == total rows required
        // 2. Assert end_col - start_col + 1 == total cols required
        // assert_eq!(end_row - start_row + 1, self.num_rows);
        let mut selector = 1;
        // Inputs are filled from start_row..end_row + 1
        for i in start_row..start_row+11 {
            self.trace[i][start_col + MULTIPLICATION_SELECTOR_OFFSET] = F::ONE;
        }
        for row in start_row..end_row + 1 {
                self.assign_u32_in_series(row,  start_col + X_INPUT_OFFSET, x);
                self.assign_u32_in_series(row,  start_col + Y_INPUT_OFFSET, y);
                let selector_u32 = get_selector_bits_from_u32(selector);
                self.assign_u32_in_series(row,  start_col + SELECTOR_OFFSET, &selector_u32);
                selector *= 2;                
        }

        // We have calcualted multiplying two max bls12_381 Fp numbers
        // dont exceed [u32; 24] so no need of [u32; 25]
        let mut prev_xy_sum = [0u32; 24];

        for i in 0..12 {
            let (xy, xy_carry) = multiply_by_slice(&x, y[i]);
            self.assign_u32_in_series( start_row + i,  start_col + XY_OFFSET, &xy);
            self.assign_u32_in_series( start_row + i,   start_col + XY_CARRIES_OFFSET, &xy_carry);

            // fill shifted XY's
            // XY's will have 0-11 number of shifts in their respective rows
            let mut xy_shifted = [0u32; 24];
            for j in 0..13 {
                let shift = i;
                xy_shifted[j+shift] = xy[j];
            }
            self.assign_u32_in_series( start_row + i,  start_col + SHIFTED_XY_OFFSET, &xy_shifted);

            // Fill XY_SUM, XY_SUM_CARRIES
            let (xy_sum, xy_sum_carry) = add_u32_slices(&xy_shifted, &prev_xy_sum);
            self.assign_u32_in_series( start_row + i,  start_col + SUM_OFFSET, &xy_sum);
            self.assign_u32_in_series( start_row + i,  start_col + SUM_CARRIES_OFFSET, &xy_sum_carry);

            prev_xy_sum = xy_sum;
        }        
    }

    pub fn generate_trace(&mut self, x: [u32; 12], y: [u32; 12]) -> Vec<[F; TOTAL_COLUMNS]>{ 

        // Fill trace for X * Y       
        self.fill_multiplication_trace_no_mod_reduction(&x, &y, 0, 15, 0, TOTAL_COLUMNS);


        // Fill trace for div * modulus()
        let (div, rem) = get_div_rem_modulus_from_biguint_12(BigUint::new(x.to_vec())*BigUint::new(y.to_vec()));
        let modulus = get_u32_vec_from_literal(modulus());
        self.fill_multiplication_trace_no_mod_reduction(&div, &modulus, 0, 15, MULTIPLICATION_1_OFFSET, TOTAL_COLUMNS);
        
        let div_x_mod = get_u32_vec_from_literal_24(BigUint::new(div.to_vec()) * BigUint::new(modulus.to_vec()));
        
        for i in 0..self.num_rows {
            self.assign_u32_in_series(i, REDUCED_OFFSET, &rem);
        }
        let mut rem_24 = [0u32; 24];
        rem_24[0..12].copy_from_slice(&rem);

        self.fill_addition_trace(&div_x_mod, &rem_24, 11, 0);

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

pub fn add_multiplication_constraints<F: RichField + Extendable<D>, const D: usize, FE, P, const D2: usize> (
    local_values: &[P],
    next_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize, // Starting column of your multiplication trace
)
    where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE> 
{ 
    // Constrains the X and Y is filled same across the rows
    for i in 0..12 {
        yield_constr.constraint_transition(//local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * 
            (local_values[start_col + X_INPUT_OFFSET + i] - next_values[start_col + X_INPUT_OFFSET + i]));
        yield_constr.constraint_transition(//local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * 
            (
            local_values[start_col + Y_INPUT_OFFSET + i] - next_values[start_col + Y_INPUT_OFFSET + i]));
    }

    // Constrain that multiplication happens correctly at each level
    for i in 0..12 {
        for j in 0..12 {
            if j == 0 {
                yield_constr.constraint_transition(
                    //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * 
                    local_values[start_col + SELECTOR_OFFSET + i] *
                    (
                        local_values[start_col + X_INPUT_OFFSET + j] * local_values[start_col + Y_INPUT_OFFSET + i]
                        - local_values[start_col + XY_OFFSET + j]
                        - (local_values[start_col + XY_CARRIES_OFFSET + j] * FE::from_canonical_u64(1<<32))
                    )
                )
            } else {
                yield_constr.constraint_transition(
                    //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
                     local_values[start_col + SELECTOR_OFFSET + i] *
                    (
                        local_values[start_col + X_INPUT_OFFSET + j] * local_values[start_col + Y_INPUT_OFFSET + i]
                        + local_values[start_col + XY_CARRIES_OFFSET + j - 1]
                        - local_values[start_col + XY_OFFSET + j]
                        - (local_values[start_col + XY_CARRIES_OFFSET + j] * FE::from_canonical_u64(1<<32))
                    )
                )
            }
        }
    }
    yield_constr.constraint_transition(local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * 
        (local_values[start_col + XY_OFFSET + 12] - local_values[start_col + XY_CARRIES_OFFSET + 11]));

    
    // Constrain XY SHIFTING
    for i in 0..12 {
        // shift is decided by selector
        for j in 0..13 {
           yield_constr.constraint_transition(
            //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * 
            local_values[start_col + SELECTOR_OFFSET + i] * 
                (
                    local_values[start_col + SHIFTED_XY_OFFSET + j + i]
                     - local_values[start_col + XY_OFFSET + j]
                )
            )
        }   
    }

    // Constrain addition at each row
    // 1. Constrain XY_SUM at row 0 is same as XY_SHIFTED
    // 2. Constrain XY_SUM_CARRIES at row 0 are all 0
    for j in 0..24{
        yield_constr.constraint_first_row(//local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
             ( local_values[start_col + SUM_OFFSET + j] - local_values[start_col + SHIFTED_XY_OFFSET + j]));
        yield_constr.constraint_first_row(//local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
             local_values[start_col + SUM_CARRIES_OFFSET + j] )
    }
    // yield_constr.constraint_first_row(//local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * 
    //     local_values[start_col + SUM_OFFSET + 24]);  

    
    // 3. Constrain addition
    yield_constr.constraint_transition(
        local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * 
            (next_values[start_col + SUM_OFFSET] + 
            (next_values[start_col + SUM_CARRIES_OFFSET] * FE::from_canonical_u64(1<<32)) -
            next_values[start_col + SHIFTED_XY_OFFSET] -
            local_values[start_col + SUM_OFFSET])
    );
    
    for j in 1..24 {
        yield_constr.constraint_transition(
            local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * 
            (next_values[start_col + SUM_OFFSET + j] + 
            (next_values[start_col + SUM_CARRIES_OFFSET + j] * FE::from_canonical_u64(1<<32)) -
            next_values[start_col + SHIFTED_XY_OFFSET + j] -
            local_values[start_col + SUM_OFFSET + j] -
            next_values[start_col + SUM_CARRIES_OFFSET + j - 1])
        )
    }
    // yield_constr.constraint_transition(local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * (next_values[start_col + SUM_OFFSET + 24] - next_values[start_col + SUM_CARRIES_OFFSET + 23]));
    
}


pub fn add_addition_constraints<F: RichField + Extendable<D>, const D: usize, FE, P, const D2: usize> (
    local_values: &[P],
    public_inputs: &[FE],// Sending only slice of what we want
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize, // Starting column of your multiplication trace
)
    where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE> 
{
    
    for j in 0..24 {
                if j == 0 {
                    yield_constr.constraint_transition(
                        local_values[start_col + ADDITION_CHECK_OFFSET] * (
                            local_values[start_col + DIV_RES_SUM_OFFSET + j]
                            + (local_values[start_col + DIV_RES_CARRY_OFFSET + j] * FE::from_canonical_u64(1<<32))
                            - local_values[start_col + MULTIPLICATION_1_OFFSET + SUM_OFFSET + j]
                            - public_inputs[j]
                        )
                    )
                } 
                else if j < 12{
                    yield_constr.constraint_transition(
                        local_values[start_col + ADDITION_CHECK_OFFSET] * (
                            local_values[start_col + DIV_RES_SUM_OFFSET + j]
                            + (local_values[start_col + DIV_RES_CARRY_OFFSET  + j] * FE::from_canonical_u64(1<<32))
                            - local_values[start_col + MULTIPLICATION_1_OFFSET + SUM_OFFSET + j]
                            - public_inputs[j]
                            - local_values[start_col + DIV_RES_CARRY_OFFSET  + j - 1]
                        )
                    )
                    
                } else {
                    yield_constr.constraint_transition(
                        local_values[start_col + ADDITION_CHECK_OFFSET] * (
                            local_values[start_col + DIV_RES_SUM_OFFSET + j]
                            + (local_values[start_col + DIV_RES_CARRY_OFFSET + j] * FE::from_canonical_u64(1<<32))
                            - local_values[start_col + MULTIPLICATION_1_OFFSET + SUM_OFFSET + j]
                            - local_values[start_col + DIV_RES_CARRY_OFFSET + j - 1]
                        )
                    )
                }
        }
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

            // ----

            for i in 0..12 {
                yield_constr.constraint_first_row(local_values[X_INPUT_OFFSET+i] - public_inputs[i]);
                yield_constr.constraint_first_row(local_values[Y_INPUT_OFFSET+i] - public_inputs[i+12]);
                yield_constr.constraint_first_row(local_values[REDUCED_OFFSET+i] - public_inputs[i+24]);
            }

            add_multiplication_constraints(local_values, next_values, yield_constr, 0);
            add_multiplication_constraints(local_values, next_values, yield_constr, MULTIPLICATION_1_OFFSET);
            
            for i in 0..12 {
                yield_constr.constraint_transition(local_values[REDUCED_OFFSET+i] - next_values[REDUCED_OFFSET+i]);
            }

            add_addition_constraints(local_values, &public_inputs[24..], yield_constr, 0);

            for j in 0..24 {
                yield_constr.constraint_transition(
                    local_values[ADDITION_CHECK_OFFSET] * 
                    (local_values[SUM_OFFSET + j] - local_values[DIV_RES_SUM_OFFSET + j])
                )
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
    use crate::{native::{ modulus, get_u32_vec_from_literal}, fp_mult_starky::FpMultiplicationStark};
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