use itertools::Itertools;
use num_bigint::BigUint;
use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
        polynomial::PolynomialValues,
        types::Field,
    },
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    util::transpose,
};
use starky::{
    constraint_consumer::ConstraintConsumer,
    evaluation_frame::{StarkEvaluationFrame, StarkFrame},
    stark::Stark,
};

use crate::native::{
    add_u32_slices, add_u32_slices_12, get_bits_as_array, get_div_rem_modulus_from_biguint_12,
    get_selector_bits_from_u32, get_u32_vec_from_literal, get_u32_vec_from_literal_24, modulus,
    multiply_by_slice, sub_u32_slices,
};


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

pub const FP_MULTIPLICATION_TOTAL_COLUMNS: usize = MULTIPLICATION_SELECTOR_OFFSET + 1;

// Non reduced addition layout offsets
pub const ADDITION_CHECK_OFFSET: usize = 0;
pub const ADDITION_X_OFFSET: usize = ADDITION_CHECK_OFFSET + 1;
pub const ADDITION_Y_OFFSET: usize = ADDITION_X_OFFSET + 24;
pub const ADDITION_SUM_OFFSET: usize = ADDITION_Y_OFFSET + 24;
pub const ADDITION_CARRY_OFFSET: usize = ADDITION_SUM_OFFSET + 24;
pub const ADDITION_TOTAL: usize = ADDITION_CARRY_OFFSET + 24;

// Non reduced subtraction layout offsets
pub const SUBTRACTION_CHECK_OFFSET: usize = 0;
pub const SUBTRACTION_X_OFFSET: usize = SUBTRACTION_CHECK_OFFSET + 1;
pub const SUBTRACTION_Y_OFFSET: usize = SUBTRACTION_X_OFFSET + 24;
pub const SUBTRACTION_DIFF_OFFSET: usize = SUBTRACTION_Y_OFFSET + 24;
pub const SUBTRACTION_BORROW_OFFSET: usize = SUBTRACTION_DIFF_OFFSET + 24;
pub const SUBTRACTION_TOTAL: usize = SUBTRACTION_BORROW_OFFSET + 24;

// Reduce and rangecheck layout offsets
pub const REDUCE_MULTIPLICATION_OFFSET: usize = 0;
pub const REDUCE_X_OFFSET: usize = REDUCE_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const REDUCED_OFFSET: usize = REDUCE_X_OFFSET + 24;
pub const REDUCTION_ADDITION_OFFSET: usize = REDUCED_OFFSET + 12;

pub const RANGE_CHECK_SUM_OFFSET: usize = REDUCTION_ADDITION_OFFSET + ADDITION_TOTAL;
pub const RANGE_CHECK_SUM_CARRY_OFFSET: usize = RANGE_CHECK_SUM_OFFSET + 12;
pub const RANGE_CHECK_BIT_DECOMP_OFFSET: usize = RANGE_CHECK_SUM_CARRY_OFFSET + 12;
pub const REDUCE_RANGE_CHECK_TOTAL: usize = RANGE_CHECK_BIT_DECOMP_OFFSET + 32;

// Fp2 Multiplication layout offsets
pub const X_0_Y_0_MULTIPLICATION_OFFSET: usize = 0;
pub const X_1_Y_1_MULTIPLICATION_OFFSET: usize =
    X_0_Y_0_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;

pub const Z1_ADD_MODULUS_OFFSET: usize =
    X_1_Y_1_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const Z1_SUBTRACTION_OFFSET: usize = Z1_ADD_MODULUS_OFFSET + ADDITION_TOTAL;
pub const Z1_REDUCE_OFFSET: usize = Z1_SUBTRACTION_OFFSET + SUBTRACTION_TOTAL;

pub const X_0_Y_1_MULTIPLICATION_OFFSET: usize = Z1_REDUCE_OFFSET + REDUCE_RANGE_CHECK_TOTAL;
pub const X_1_Y_0_MULTIPLICATION_OFFSET: usize =
    X_0_Y_1_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;

pub const Z2_ADDITION_OFFSET: usize =
    X_1_Y_0_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const Z2_REDUCE_OFFSET: usize = Z2_ADDITION_OFFSET + ADDITION_TOTAL;

pub const TOTAL_COLUMNS: usize = Z2_REDUCE_OFFSET + REDUCE_RANGE_CHECK_TOTAL;

pub const COLUMNS: usize = TOTAL_COLUMNS;
pub const PUBLIC_INPUTS: usize = 72;

macro_rules! bit_decomp_32 {
    ($row:expr, $col:expr, $f:ty, $p:ty) => {
        ((0..32).fold(<$p>::ZEROS, |acc, i| {
            acc + $row[$col + i] * <$f>::from_canonical_u64(1 << i)
        }))
    };
}

// A (Fp) * B (Fp) => C (Fp)
#[derive(Clone)]
pub struct Fp2MultiplicationStark<F: RichField + Extendable<D>, const D: usize> {
    pub trace: Vec<[F; TOTAL_COLUMNS]>,
    _num_rows: usize,
}

// Implement trace generator
impl<F: RichField + Extendable<D>, const D: usize> Fp2MultiplicationStark<F, D> {
    pub fn new(num_rows: usize) -> Self {
        Self {
            trace: vec![[F::ZERO; TOTAL_COLUMNS]; num_rows],
            _num_rows: num_rows,
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
        assert!(row >= 1);
        for i in start_col..start_col + num_cols {
            self.trace[row][start_col + i] = self.trace[row - 1][start_col + i];
        }
    }

    pub fn fill_addition_trace(
        &mut self,
        x: &[u32; 24],
        y: &[u32; 24],
        row: usize,
        start_col: usize,
    ) {
        self.trace[row][start_col + ADDITION_CHECK_OFFSET] = F::ONE;
        let (x_y_sum, x_y_sum_carry) = add_u32_slices(&x, &y);
        self.assign_u32_in_series(row, start_col + ADDITION_X_OFFSET, x);
        self.assign_u32_in_series(row, start_col + ADDITION_Y_OFFSET, y);
        self.assign_u32_in_series(row, start_col + ADDITION_SUM_OFFSET, &x_y_sum);
        self.assign_u32_in_series(row, start_col + ADDITION_CARRY_OFFSET, &x_y_sum_carry);
    }

    pub fn fill_subtraction_trace(
        &mut self,
        x: &[u32; 24],
        y: &[u32; 24],
        row: usize,
        start_col: usize,
    ) {
        self.trace[row][start_col + SUBTRACTION_CHECK_OFFSET] = F::ONE;
        let (x_y_diff, x_y_diff_borrow) = sub_u32_slices(&x, &y);
        self.assign_u32_in_series(row, start_col + SUBTRACTION_X_OFFSET, x);
        self.assign_u32_in_series(row, start_col + SUBTRACTION_Y_OFFSET, y);
        self.assign_u32_in_series(row, start_col + SUBTRACTION_DIFF_OFFSET, &x_y_diff);
        self.assign_u32_in_series(row, start_col + SUBTRACTION_BORROW_OFFSET, &x_y_diff_borrow);
    }

    pub fn fill_range_check_trace(&mut self, x: &[u32; 12], row: usize, start_col: usize) {
        let y = (BigUint::from(1u32) << 382) - modulus();
        let y_u32 = get_u32_vec_from_literal(y);
        let (x_y_sum, x_y_carry) = add_u32_slices_12(&x, &y_u32);
        self.assign_u32_in_series(row, start_col + RANGE_CHECK_SUM_OFFSET, &x_y_sum);
        self.assign_u32_in_series(row, start_col + RANGE_CHECK_SUM_CARRY_OFFSET, &x_y_carry);
        self.assign_u32_in_series(
            row,
            start_col + RANGE_CHECK_BIT_DECOMP_OFFSET,
            &get_bits_as_array(x_y_sum[11]),
        );
    }

    // Fills from start_row..end_row+1
    pub fn fill_multiplication_trace_no_mod_reduction(
        &mut self,
        x: &[u32; 12],
        y: &[u32; 12],
        start_row: usize,
        end_row: usize,
        start_col: usize,
    ) {
        // [TODO]:
        // 1. Assert end_row - start_row + 1 == total rows required
        // 2. Assert end_col - start_col + 1 == total cols required
        // assert_eq!(end_row - start_row + 1, self.num_rows);
        let mut selector = 1;
        // Inputs are filled from start_row..end_row + 1
        for i in start_row..start_row + 11 {
            self.trace[i][start_col + MULTIPLICATION_SELECTOR_OFFSET] = F::ONE;
        }
        for row in start_row..end_row + 1 {
            self.assign_u32_in_series(row, start_col + X_INPUT_OFFSET, x);
            self.assign_u32_in_series(row, start_col + Y_INPUT_OFFSET, y);
            let selector_u32 = get_selector_bits_from_u32(selector);
            self.assign_u32_in_series(row, start_col + SELECTOR_OFFSET, &selector_u32);
            selector *= 2;
        }

        // We have calcualted multiplying two max bls12_381 Fp numbers
        // dont exceed [u32; 24] so no need of [u32; 25]
        let mut prev_xy_sum = [0u32; 24];

        for i in 0..12 {
            let (xy, xy_carry) = multiply_by_slice(&x, y[i]);
            self.assign_u32_in_series(start_row + i, start_col + XY_OFFSET, &xy);
            self.assign_u32_in_series(start_row + i, start_col + XY_CARRIES_OFFSET, &xy_carry);

            // fill shifted XY's
            // XY's will have 0-11 number of shifts in their respective rows
            let mut xy_shifted = [0u32; 24];
            for j in 0..13 {
                let shift = i;
                xy_shifted[j + shift] = xy[j];
            }
            self.assign_u32_in_series(start_row + i, start_col + SHIFTED_XY_OFFSET, &xy_shifted);

            // Fill XY_SUM, XY_SUM_CARRIES
            let (xy_sum, xy_sum_carry) = add_u32_slices(&xy_shifted, &prev_xy_sum);
            self.assign_u32_in_series(start_row + i, start_col + SUM_OFFSET, &xy_sum);
            self.assign_u32_in_series(start_row + i, start_col + SUM_CARRIES_OFFSET, &xy_sum_carry);

            prev_xy_sum = xy_sum;
        }
    }

    fn fill_reduction_and_range_check_trace(
        &mut self,
        x: &[u32; 24],
        start_row: usize,
        end_row: usize,
        start_col: usize,
    ) {
        let (div, rem) = get_div_rem_modulus_from_biguint_12(BigUint::new(x.to_vec()));
        let modulus = get_u32_vec_from_literal(modulus());
        self.fill_multiplication_trace_no_mod_reduction(
            &div,
            &modulus,
            start_row,
            end_row,
            start_col + REDUCE_MULTIPLICATION_OFFSET,
        );

        for row in start_row..end_row + 1 {
            self.assign_u32_in_series(row, start_col + REDUCE_X_OFFSET, x);
        }

        let div_x_mod = get_u32_vec_from_literal_24(
            BigUint::new(div.to_vec()) * BigUint::new(modulus.to_vec()),
        );

        for i in start_row..end_row + 1 {
            self.assign_u32_in_series(i, start_col + REDUCED_OFFSET, &rem);
        }
        let mut rem_24 = [0u32; 24];
        rem_24[0..12].copy_from_slice(&rem);

        self.fill_addition_trace(
            &div_x_mod,
            &rem_24,
            start_row + 11,
            start_col + REDUCTION_ADDITION_OFFSET,
        );

        self.fill_range_check_trace(&rem, start_row, start_col);
    }


    pub fn generate_trace(&mut self, x: [[u32; 12]; 2], y: [[u32; 12]; 2]) {
        let modulus = modulus();

        // filling trace for X0*Y0 - X1*Y1
        self.fill_multiplication_trace_no_mod_reduction(
            &x[0],
            &y[0],
            0,
            15,
            X_0_Y_0_MULTIPLICATION_OFFSET,
        );
        self.fill_multiplication_trace_no_mod_reduction(
            &x[1],
            &y[1],
            0,
            15,
            X_1_Y_1_MULTIPLICATION_OFFSET,
        );

        let x0y0 =
            get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y[0].to_vec()));
        let modulus_sq = get_u32_vec_from_literal_24(modulus.clone() * modulus.clone());
        self.fill_addition_trace(&x0y0, &modulus_sq, 11, Z1_ADD_MODULUS_OFFSET);

        let x0y0_add_modsq =
            get_u32_vec_from_literal_24(BigUint::new(x0y0.to_vec()) + modulus.clone() * modulus);
        let x1y1 =
            get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y[1].to_vec()));
        self.fill_subtraction_trace(&x0y0_add_modsq, &x1y1, 11, Z1_SUBTRACTION_OFFSET);

        let x0y0_x1y1 = get_u32_vec_from_literal_24(
            BigUint::new(x0y0_add_modsq.to_vec()) - BigUint::new(x1y1.to_vec()),
        );
        self.fill_reduction_and_range_check_trace(&x0y0_x1y1, 0, 15, Z1_REDUCE_OFFSET);

        // filling trace for X0*Y1 + X1*Y0
        self.fill_multiplication_trace_no_mod_reduction(
            &x[0],
            &y[1],
            0,
            15,
            X_0_Y_1_MULTIPLICATION_OFFSET,
        );
        self.fill_multiplication_trace_no_mod_reduction(
            &x[1],
            &y[0],
            0,
            15,
            X_1_Y_0_MULTIPLICATION_OFFSET,
        );

        let x0y1 =
            get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y[1].to_vec()));
        let x1y0 =
            get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y[0].to_vec()));
        self.fill_addition_trace(&x0y1, &x1y0, 11, Z2_ADDITION_OFFSET);

        let x0y1_x1y0 =
            get_u32_vec_from_literal_24(BigUint::new(x0y1.to_vec()) + BigUint::new(x1y0.to_vec()));
        self.fill_reduction_and_range_check_trace(&x0y1_x1y0, 0, 15, Z2_REDUCE_OFFSET);
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

pub fn add_multiplication_constraints<
    F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
>(
    local_values: &[P],
    next_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize, // Starting column of your multiplication trace
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    // Constrains the X and Y is filled same across the rows
    for i in 0..12 {
        yield_constr.constraint_transition(
            //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
            local_values[start_col + X_INPUT_OFFSET + i]
                - next_values[start_col + X_INPUT_OFFSET + i],
        );
        yield_constr.constraint_transition(
            //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
            local_values[start_col + Y_INPUT_OFFSET + i]
                - next_values[start_col + Y_INPUT_OFFSET + i],
        );
    }

    // Constrain that multiplication happens correctly at each level
    for i in 0..12 {
        for j in 0..12 {
            if j == 0 {
                yield_constr.constraint_transition(
                    //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
                    local_values[start_col + SELECTOR_OFFSET + i]
                        * (local_values[start_col + X_INPUT_OFFSET + j]
                            * local_values[start_col + Y_INPUT_OFFSET + i]
                            - local_values[start_col + XY_OFFSET + j]
                            - (local_values[start_col + XY_CARRIES_OFFSET + j]
                                * FE::from_canonical_u64(1 << 32))),
                )
            } else {
                yield_constr.constraint_transition(
                    //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
                    local_values[start_col + SELECTOR_OFFSET + i]
                        * (local_values[start_col + X_INPUT_OFFSET + j]
                            * local_values[start_col + Y_INPUT_OFFSET + i]
                            + local_values[start_col + XY_CARRIES_OFFSET + j - 1]
                            - local_values[start_col + XY_OFFSET + j]
                            - (local_values[start_col + XY_CARRIES_OFFSET + j]
                                * FE::from_canonical_u64(1 << 32))),
                )
            }
        }
    }
    yield_constr.constraint_transition(
        local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET]
            * (local_values[start_col + XY_OFFSET + 12]
                - local_values[start_col + XY_CARRIES_OFFSET + 11]),
    );

    // Constrain XY SHIFTING
    for i in 0..12 {
        // shift is decided by selector
        for j in 0..13 {
            yield_constr.constraint_transition(
                //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
                local_values[start_col + SELECTOR_OFFSET + i]
                    * (local_values[start_col + SHIFTED_XY_OFFSET + j + i]
                        - local_values[start_col + XY_OFFSET + j]),
            )
        }
    }

    // Constrain addition at each row
    // 1. Constrain XY_SUM at row 0 is same as XY_SHIFTED
    // 2. Constrain XY_SUM_CARRIES at row 0 are all 0
    for j in 0..24 {
        yield_constr.constraint_first_row(
            //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
            local_values[start_col + SUM_OFFSET + j]
                - local_values[start_col + SHIFTED_XY_OFFSET + j],
        );
        yield_constr.constraint_first_row(
            //local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
            local_values[start_col + SUM_CARRIES_OFFSET + j],
        )
    }
    // yield_constr.constraint_first_row(//local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
    //     local_values[start_col + SUM_OFFSET + 24]);

    // 3. Constrain addition
    yield_constr.constraint_transition(
        local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET]
            * (next_values[start_col + SUM_OFFSET]
                + (next_values[start_col + SUM_CARRIES_OFFSET] * FE::from_canonical_u64(1 << 32))
                - next_values[start_col + SHIFTED_XY_OFFSET]
                - local_values[start_col + SUM_OFFSET]),
    );

    for j in 1..24 {
        yield_constr.constraint_transition(
            local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET]
                * (next_values[start_col + SUM_OFFSET + j]
                    + (next_values[start_col + SUM_CARRIES_OFFSET + j]
                        * FE::from_canonical_u64(1 << 32))
                    - next_values[start_col + SHIFTED_XY_OFFSET + j]
                    - local_values[start_col + SUM_OFFSET + j]
                    - next_values[start_col + SUM_CARRIES_OFFSET + j - 1]),
        )
    }
    // yield_constr.constraint_transition(local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] * (next_values[start_col + SUM_OFFSET + 24] - next_values[start_col + SUM_CARRIES_OFFSET + 23]));
}

pub fn add_addition_constraints<
    F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
>(
    local_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize, // Starting column of your multiplication trace
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    for j in 0..24 {
        if j == 0 {
            yield_constr.constraint_transition(
                local_values[start_col + ADDITION_CHECK_OFFSET]
                    * (local_values[start_col + ADDITION_SUM_OFFSET + j]
                        + (local_values[start_col + ADDITION_CARRY_OFFSET + j]
                            * FE::from_canonical_u64(1 << 32))
                        - local_values[start_col + ADDITION_X_OFFSET + j]
                        - local_values[start_col + ADDITION_Y_OFFSET + j]),
            )
        } else {
            yield_constr.constraint_transition(
                local_values[start_col + ADDITION_CHECK_OFFSET]
                    * (local_values[start_col + ADDITION_SUM_OFFSET + j]
                        + (local_values[start_col + ADDITION_CARRY_OFFSET + j]
                            * FE::from_canonical_u64(1 << 32))
                        - local_values[start_col + ADDITION_X_OFFSET + j]
                        - local_values[start_col + ADDITION_Y_OFFSET + j]
                        - local_values[start_col + ADDITION_CARRY_OFFSET + j - 1]),
            )
        }
    }
}

pub fn add_subtraction_constraints<
    F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
>(
    local_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize, // Starting column of your multiplication trace
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    for j in 0..24 {
        if j == 0 {
            yield_constr.constraint_transition(
                local_values[start_col + SUBTRACTION_CHECK_OFFSET]
                    * (local_values[start_col + SUBTRACTION_DIFF_OFFSET + j]
                        + local_values[start_col + SUBTRACTION_Y_OFFSET + j]
                        - (local_values[start_col + SUBTRACTION_BORROW_OFFSET + j]
                            * FE::from_canonical_u64(1 << 32))
                        - local_values[start_col + SUBTRACTION_X_OFFSET + j]),
            )
        } else {
            yield_constr.constraint_transition(
                local_values[start_col + SUBTRACTION_CHECK_OFFSET]
                    * (local_values[start_col + SUBTRACTION_DIFF_OFFSET + j]
                        + local_values[start_col + SUBTRACTION_Y_OFFSET + j]
                        + local_values[start_col + SUBTRACTION_BORROW_OFFSET + j - 1]
                        - (local_values[start_col + SUBTRACTION_BORROW_OFFSET + j]
                            * FE::from_canonical_u64(1 << 32))
                        - local_values[start_col + SUBTRACTION_X_OFFSET + j]),
            )
        }
    }
}

pub fn add_range_check_constraints<
    F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
>(
    local_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize, // Starting column of your multiplication trace
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let y = (BigUint::from(1u32) << 382) - modulus();
    let y_u32 = get_u32_vec_from_literal(y);

    for i in 0..12 {
        if i == 0 {
            yield_constr.constraint_first_row(
                local_values[start_col + RANGE_CHECK_SUM_OFFSET + i]
                    + (local_values[start_col + RANGE_CHECK_SUM_CARRY_OFFSET + i]
                        * FE::from_canonical_u64(1 << 32))
                    - FE::from_canonical_u32(y_u32[i])
                    - local_values[start_col + REDUCED_OFFSET + i],
            )
        } else if i < 12 {
            yield_constr.constraint_first_row(
                local_values[start_col + RANGE_CHECK_SUM_OFFSET + i]
                    + (local_values[start_col + RANGE_CHECK_SUM_CARRY_OFFSET + i]
                        * FE::from_canonical_u64(1 << 32))
                    - FE::from_canonical_u32(y_u32[i])
                    - local_values[start_col + REDUCED_OFFSET + i]
                    - local_values[start_col + RANGE_CHECK_SUM_CARRY_OFFSET + i - 1],
            )
        }
        let bit_col: usize = start_col + RANGE_CHECK_BIT_DECOMP_OFFSET;
        let val_reconstructed = bit_decomp_32!(local_values, bit_col, FE, P);
        yield_constr.constraint_first_row(
            val_reconstructed - local_values[start_col + RANGE_CHECK_SUM_OFFSET + 11],
        );
        yield_constr.constraint_first_row(local_values[bit_col + 30]);
    }
}

fn add_reduce_range_check_constraints<
    F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
>(
    local_values: &[P],
    next_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize, // Starting column of your multiplication trace
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let modulus = modulus();
    let modulus_u32 = get_u32_vec_from_literal(modulus);
    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[start_col + REDUCE_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
                - FE::from_canonical_u32(modulus_u32[i]),
        );
    }

    add_multiplication_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + REDUCE_MULTIPLICATION_OFFSET,
    );

    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + REDUCE_X_OFFSET + i]
                - next_values[start_col + REDUCE_X_OFFSET + i],
        );
    }

    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[start_col + REDUCED_OFFSET + i]
                - next_values[start_col + REDUCED_OFFSET + i],
        );
    }

    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + REDUCE_MULTIPLICATION_OFFSET + SUM_OFFSET + i]
                    - local_values[start_col + REDUCTION_ADDITION_OFFSET + ADDITION_X_OFFSET + i]),
        );
    }

    add_addition_constraints(
        local_values,
        yield_constr,
        start_col + REDUCTION_ADDITION_OFFSET,
    );

    for i in 0..24 {
        if i < 12 {
            yield_constr.constraint_transition(
                local_values[start_col + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                    * (local_values[start_col + REDUCED_OFFSET + i]
                        - local_values
                            [start_col + REDUCTION_ADDITION_OFFSET + ADDITION_Y_OFFSET + i]),
            );
        } else {
            yield_constr.constraint_transition(
                local_values[start_col + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                    * local_values[start_col + REDUCTION_ADDITION_OFFSET + ADDITION_Y_OFFSET + i],
            );
        }
    }

    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + REDUCE_X_OFFSET + i]
                    - local_values
                        [start_col + REDUCTION_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i]),
        )
    }

    add_range_check_constraints(local_values, yield_constr, start_col);
}

// Implement constraint generator
impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for Fp2MultiplicationStark<F, D> {
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
        P: PackedField<Scalar = FE>,
    {
        let local_values = vars.get_local_values();
        let next_values = vars.get_next_values();
        let public_inputs = vars.get_public_inputs();

        // ----

        // constrain X0*Y0 multiplication with public inputs
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[X_0_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] - public_inputs[i],
            );
            yield_constr.constraint_first_row(
                local_values[X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
                    - public_inputs[i + 24],
            );
        }

        // constrain X_0*Y_0
        add_multiplication_constraints(
            local_values,
            next_values,
            yield_constr,
            X_0_Y_0_MULTIPLICATION_OFFSET,
        );

        // constrain X1*Y1 multiplication with public inputs
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[X_1_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i]
                    - public_inputs[i + 12],
            );
            yield_constr.constraint_first_row(
                local_values[X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
                    - public_inputs[i + 36],
            );
        }

        // constrain X_1*Y_1
        add_multiplication_constraints(
            local_values,
            next_values,
            yield_constr,
            X_1_Y_1_MULTIPLICATION_OFFSET,
        );

        // constrain X0*Y0 with X0*Y0 + modulus^2
        for i in 0..24 {
            yield_constr.constraint_transition(
                local_values[Z1_ADD_MODULUS_OFFSET + ADDITION_CHECK_OFFSET]
                    * (local_values[Z1_ADD_MODULUS_OFFSET + ADDITION_X_OFFSET + i]
                        - local_values[X_0_Y_0_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
            );
        }

        // constrain modulus^2 with X0*Y0 + modulus^2
        let modulus = modulus();
        let modulus_sq_u32 = get_u32_vec_from_literal_24(modulus.clone() * modulus);
        for i in 0..24 {
            yield_constr.constraint_transition(
                local_values[Z1_ADD_MODULUS_OFFSET + ADDITION_CHECK_OFFSET]
                    * (local_values[Z1_ADD_MODULUS_OFFSET + ADDITION_Y_OFFSET + i]
                        - FE::from_canonical_u32(modulus_sq_u32[i])),
            );
        }

        // constrain X0*Y0 + modulus^2
        add_addition_constraints(local_values, yield_constr, Z1_ADD_MODULUS_OFFSET);

        // constrain X0*Y0 + modulus^2 with X0*Y0 + modulus^2 - X1Y1
        for i in 0..24 {
            yield_constr.constraint_transition(
                local_values[Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]
                    * (local_values[Z1_SUBTRACTION_OFFSET + SUBTRACTION_X_OFFSET + i]
                        - local_values[Z1_ADD_MODULUS_OFFSET + ADDITION_SUM_OFFSET + i]),
            );
        }

        // constrain X1*Y1 + modulus^2 with X0*Y0 + modulus^2 - X1Y1
        for i in 0..24 {
            yield_constr.constraint_transition(
                local_values[Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]
                    * (local_values[Z1_SUBTRACTION_OFFSET + SUBTRACTION_Y_OFFSET + i]
                        - local_values[X_1_Y_1_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
            );
        }

        // constrain X0*Y0 + modulus^2 - X1Y1
        add_subtraction_constraints(local_values, yield_constr, Z1_SUBTRACTION_OFFSET);

        // constrain X0*Y0 + modulus^2 - X1Y1 with reduction
        for i in 0..24 {
            yield_constr.constraint_transition(
                local_values[Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]
                    * (local_values[Z1_SUBTRACTION_OFFSET + SUBTRACTION_DIFF_OFFSET + i]
                        - local_values[Z1_REDUCE_OFFSET + REDUCE_X_OFFSET + i]),
            );
        }

        // constrain reduction with public inputs
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[Z1_REDUCE_OFFSET + REDUCED_OFFSET + i] - public_inputs[i + 48],
            );
        }

        // constrain reduction
        add_reduce_range_check_constraints(
            local_values,
            next_values,
            yield_constr,
            Z1_REDUCE_OFFSET,
        );

        // constrain X0*Y1 multiplication with public inputs
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[X_0_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] - public_inputs[i],
            );
            yield_constr.constraint_first_row(
                local_values[X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
                    - public_inputs[i + 36],
            );
        }

        // constrain X_1*Y_0
        add_multiplication_constraints(
            local_values,
            next_values,
            yield_constr,
            X_0_Y_1_MULTIPLICATION_OFFSET,
        );

        // constrain X1*Y0 multiplication with public inputs
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[X_1_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i]
                    - public_inputs[i + 12],
            );
            yield_constr.constraint_first_row(
                local_values[X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
                    - public_inputs[i + 24],
            );
        }

        // constrain X_1*Y_0
        add_multiplication_constraints(
            local_values,
            next_values,
            yield_constr,
            X_1_Y_0_MULTIPLICATION_OFFSET,
        );

        // constrain X0*Y1 with X0*Y1 + X1*Y0
        for i in 0..24 {
            yield_constr.constraint_transition(
                local_values[Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                    * (local_values[Z2_ADDITION_OFFSET + ADDITION_X_OFFSET + i]
                        - local_values[X_0_Y_1_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
            );
        }

        // constrain X1*Y0 with X0*Y1 + X1*Y0
        for i in 0..24 {
            yield_constr.constraint_transition(
                local_values[Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                    * (local_values[Z2_ADDITION_OFFSET + ADDITION_Y_OFFSET + i]
                        - local_values[X_1_Y_0_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
            );
        }

        // constrain X0*Y1 + X1*Y0
        add_addition_constraints(local_values, yield_constr, Z2_ADDITION_OFFSET);

        // constrain X0*Y1 + X1*Y0 with reduction
        for i in 0..24 {
            yield_constr.constraint_transition(
                local_values[Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                    * (local_values[Z2_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i]
                        - local_values[Z2_REDUCE_OFFSET + REDUCE_X_OFFSET + i]),
            );
        }

        // constrain reduction with public inputs
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[Z2_REDUCE_OFFSET + REDUCED_OFFSET + i] - public_inputs[i + 60],
            );
        }

        // constrain reduction
        add_reduce_range_check_constraints(
            local_values,
            next_values,
            yield_constr,
            Z2_REDUCE_OFFSET,
        );
    }

    type EvaluationFrameTarget =
        StarkFrame<ExtensionTarget<D>, ExtensionTarget<D>, COLUMNS, PUBLIC_INPUTS>;

    fn eval_ext_circuit(
        &self,
        _builder: &mut plonky2::plonk::circuit_builder::CircuitBuilder<F, D>,
        _vars: &Self::EvaluationFrameTarget,
        _yield_constr: &mut starky::constraint_consumer::RecursiveConstraintConsumer<F, D>,
    ) {
        todo!()
    }

    fn constraint_degree(&self) -> usize {
        2
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        fp2_mult_starky::{Fp2MultiplicationStark, PUBLIC_INPUTS},
        native::{mul_Fp2, Fp, Fp2},
    };
    use plonky2::field::types::Field;
    use plonky2::{
        plonk::config::{GenericConfig, PoseidonGoldilocksConfig},
        util::timing::TimingTree,
    };
    use starky::util::trace_rows_to_poly_values;
    use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};

    #[test]
    fn test_fp2_mul() {
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
        verify_stark_proof(s_, proof.unwrap(), &config).unwrap();
    }
}
