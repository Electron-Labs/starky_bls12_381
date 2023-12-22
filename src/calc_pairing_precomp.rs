use std::str::FromStr;

use itertools::Itertools;
use num_bigint::{BigUint, ToBigUint};
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
    multiply_by_slice, sub_u32_slices, Fp, Fp2, calc_qs, calc_precomp_stuff_loop0, sub_u32_slices_12, mul_u32_slice_u32, mod_inverse,
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
pub const MULTIPLICATION_FIRST_ROW_OFFSET: usize = MULTIPLICATION_SELECTOR_OFFSET + 1;

pub const FP_MULTIPLICATION_TOTAL_COLUMNS: usize = MULTIPLICATION_FIRST_ROW_OFFSET + 1;

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
pub const REDUCTION_ADDITION_OFFSET: usize = REDUCE_X_OFFSET + 24;
pub const REDUCED_OFFSET: usize = REDUCTION_ADDITION_OFFSET + ADDITION_TOTAL;
pub const REDUCTION_TOTAL: usize = REDUCED_OFFSET + 12;

// Rangecheck offsets
// whenever range check is used, start_col - 12 will contain the element being rangechecked
pub const RANGE_CHECK_SELECTOR_OFFSET: usize = 0;
pub const RANGE_CHECK_SUM_OFFSET: usize = RANGE_CHECK_SELECTOR_OFFSET + 1;
pub const RANGE_CHECK_SUM_CARRY_OFFSET: usize = RANGE_CHECK_SUM_OFFSET + 12;
pub const RANGE_CHECK_BIT_DECOMP_OFFSET: usize = RANGE_CHECK_SUM_CARRY_OFFSET + 12;
pub const RANGE_CHECK_TOTAL: usize = RANGE_CHECK_BIT_DECOMP_OFFSET + 32;

// Fp2 Multiplication layout offsets
pub const FP2_FP2_SELECTOR_OFFSET: usize = 0;
pub const FP2_FP2_X_INPUT_OFFSET: usize = FP2_FP2_SELECTOR_OFFSET + 1;
pub const FP2_FP2_Y_INPUT_OFFSET: usize = FP2_FP2_X_INPUT_OFFSET + 24;
pub const X_0_Y_0_MULTIPLICATION_OFFSET: usize = FP2_FP2_Y_INPUT_OFFSET + 24;
pub const X_1_Y_1_MULTIPLICATION_OFFSET: usize =
    X_0_Y_0_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;

pub const Z1_ADD_MODULUS_OFFSET: usize =
    X_1_Y_1_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const Z1_SUBTRACTION_OFFSET: usize = Z1_ADD_MODULUS_OFFSET + ADDITION_TOTAL;
pub const Z1_REDUCE_OFFSET: usize = Z1_SUBTRACTION_OFFSET + SUBTRACTION_TOTAL;
pub const Z1_RANGECHECK_OFFSET: usize = Z1_REDUCE_OFFSET + REDUCTION_TOTAL;

pub const X_0_Y_1_MULTIPLICATION_OFFSET: usize = Z1_RANGECHECK_OFFSET + RANGE_CHECK_TOTAL;
pub const X_1_Y_0_MULTIPLICATION_OFFSET: usize =
    X_0_Y_1_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;

pub const Z2_ADDITION_OFFSET: usize =
    X_1_Y_0_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const Z2_REDUCE_OFFSET: usize = Z2_ADDITION_OFFSET + ADDITION_TOTAL;
pub const Z2_RANGECHECK_OFFSET: usize = Z2_REDUCE_OFFSET + REDUCTION_TOTAL;

pub const TOTAL_COLUMNS_FP2_MULTIPLICATION: usize = Z2_RANGECHECK_OFFSET + RANGE_CHECK_TOTAL;

// Fp2 * Fp multiplication layout offsets
pub const FP2_FP_MUL_SELECTOR_OFFSET: usize = 0;
pub const FP2_FP_X_INPUT_OFFSET: usize = FP2_FP_MUL_SELECTOR_OFFSET + 1;
pub const FP2_FP_Y_INPUT_OFFSET: usize = FP2_FP_X_INPUT_OFFSET + 24;
pub const X0_Y_MULTIPLICATION_OFFSET:  usize = FP2_FP_Y_INPUT_OFFSET + 12;
pub const X0_Y_REDUCE_OFFSET: usize = X0_Y_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const X0_Y_RANGECHECK_OFFSET: usize = X0_Y_REDUCE_OFFSET + REDUCTION_TOTAL;
pub const X1_Y_MULTIPLICATION_OFFSET:  usize = X0_Y_RANGECHECK_OFFSET + RANGE_CHECK_TOTAL;
pub const X1_Y_REDUCE_OFFSET: usize = X1_Y_MULTIPLICATION_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const X1_Y_RANGECHECK_OFFSET: usize = X1_Y_REDUCE_OFFSET + REDUCTION_TOTAL;
pub const FP2_FP_TOTAL_COLUMNS: usize = X1_Y_RANGECHECK_OFFSET + RANGE_CHECK_TOTAL;

// Multiply by B layout offsets
pub const MULTIPLY_B_SELECTOR_OFFSET: usize = 0;
pub const MULTIPLY_B_X_OFFSET: usize = MULTIPLY_B_SELECTOR_OFFSET + 1;
pub const MULTIPLY_B_X0_B_MUL_OFFSET: usize = MULTIPLY_B_X_OFFSET + 24;
pub const MULTIPLY_B_X1_B_MUL_OFFSET: usize = MULTIPLY_B_X0_B_MUL_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const MULTIPLY_B_ADD_MODSQ_OFFSET: usize = MULTIPLY_B_X1_B_MUL_OFFSET + FP_MULTIPLICATION_TOTAL_COLUMNS;
pub const MULTIPLY_B_SUB_OFFSET: usize = MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_TOTAL;
pub const MULTIPLY_B_Z0_REDUCE_OFFSET: usize = MULTIPLY_B_SUB_OFFSET + SUBTRACTION_TOTAL;
pub const MULTIPLY_B_Z0_RANGECHECK_OFFSET: usize = MULTIPLY_B_Z0_REDUCE_OFFSET + REDUCTION_TOTAL;
pub const MULTIPLY_B_ADD_OFFSET: usize = MULTIPLY_B_Z0_RANGECHECK_OFFSET + RANGE_CHECK_TOTAL;
pub const MULTIPLY_B_Z1_REDUCE_OFFSET: usize = MULTIPLY_B_ADD_OFFSET + ADDITION_TOTAL;
pub const MULTIPLY_B_Z1_RANGECHECK_OFFSET: usize = MULTIPLY_B_Z1_REDUCE_OFFSET + REDUCTION_TOTAL;
pub const MULTIPLY_B_TOTAL_COLUMS: usize = MULTIPLY_B_Z1_RANGECHECK_OFFSET + RANGE_CHECK_TOTAL;

// Fp addition layout offsets
pub const FP_ADDITION_CHECK_OFFSET: usize = 0;
pub const FP_ADDITION_X_OFFSET: usize = FP_ADDITION_CHECK_OFFSET + 1;
pub const FP_ADDITION_Y_OFFSET: usize = FP_ADDITION_X_OFFSET + 12;
pub const FP_ADDITION_SUM_OFFSET: usize = FP_ADDITION_Y_OFFSET + 12;
pub const FP_ADDITION_CARRY_OFFSET: usize = FP_ADDITION_SUM_OFFSET + 12;
pub const FP_ADDITION_TOTAL: usize = FP_ADDITION_CARRY_OFFSET + 12;

// Fp subtraction layout offsets
pub const FP_SUBTRACTION_CHECK_OFFSET: usize = 0;
pub const FP_SUBTRACTION_X_OFFSET: usize = FP_SUBTRACTION_CHECK_OFFSET + 1;
pub const FP_SUBTRACTION_Y_OFFSET: usize = FP_SUBTRACTION_X_OFFSET + 12;
pub const FP_SUBTRACTION_DIFF_OFFSET: usize = FP_SUBTRACTION_Y_OFFSET + 12;
pub const FP_SUBTRACTION_BORROW_OFFSET: usize = FP_SUBTRACTION_DIFF_OFFSET + 12;
pub const FP_SUBTRACTION_TOTAL: usize = FP_SUBTRACTION_BORROW_OFFSET + 12;

// Fp2 addition layout offsets
pub const FP2_ADDITION_0_OFFSET: usize = 0;
pub const FP2_ADDITION_1_OFFSET: usize = FP2_ADDITION_0_OFFSET + FP_ADDITION_TOTAL;
pub const FP2_ADDITION_TOTAL: usize = FP2_ADDITION_1_OFFSET + FP_ADDITION_TOTAL;

// Fp2 subtraction layout offsets
pub const FP2_SUBTRACTION_0_OFFSET: usize = 0;
pub const FP2_SUBTRACTION_1_OFFSET: usize = FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_TOTAL;
pub const FP2_SUBTRACTION_TOTAL: usize = FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_TOTAL;

// Fp multiply single
pub const FP_MULTIPLY_SINGLE_CHECK_OFFSET: usize = 0;
pub const FP_MULTIPLY_SINGLE_X_OFFSET: usize = FP_MULTIPLY_SINGLE_CHECK_OFFSET + 1;
pub const FP_MULTIPLY_SINGLE_Y_OFFSET: usize = FP_MULTIPLY_SINGLE_X_OFFSET + 12;
pub const FP_MULTIPLY_SINGLE_SUM_OFFSET: usize = FP_MULTIPLY_SINGLE_Y_OFFSET + 1;
pub const FP_MULTIPLY_SINGLE_CARRY_OFFSET: usize = FP_MULTIPLY_SINGLE_SUM_OFFSET + 12;
pub const FP_MULTIPLY_SINGLE_TOTAL: usize = FP_MULTIPLY_SINGLE_CARRY_OFFSET + 12;

// Fp2 multiply single
pub const FP2_MULTIPLY_SINGLE_0_OFFSET: usize = 0;
pub const FP2_MULTIPLY_SINGLE_1_OFFSET: usize = FP2_MULTIPLY_SINGLE_0_OFFSET + FP_MULTIPLY_SINGLE_TOTAL;
pub const FP2_MULTIPLY_SINGLE_TOTAL: usize = FP2_MULTIPLY_SINGLE_1_OFFSET + FP_MULTIPLY_SINGLE_TOTAL;

// Fp reduce rangecheck single
pub const FP_SINGLE_REDUCE_MULTIPLICATION_OFFSET: usize = 0;
pub const FP_SINGLE_REDUCE_X_OFFSET: usize = FP_SINGLE_REDUCE_MULTIPLICATION_OFFSET + FP_MULTIPLY_SINGLE_TOTAL;
pub const FP_SINGLE_REDUCTION_ADDITION_OFFSET: usize = FP_SINGLE_REDUCE_X_OFFSET + 12;
pub const FP_SINGLE_REDUCED_OFFSET: usize = FP_SINGLE_REDUCTION_ADDITION_OFFSET + FP_ADDITION_TOTAL;
pub const FP_SINGLE_REDUCE_TOTAL: usize = FP_SINGLE_REDUCED_OFFSET + 12;

pub const Z_MULT_Z_INV_OFFSET: usize = 0;
pub const X_MULT_Z_INV_OFFSET: usize = Z_MULT_Z_INV_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const Y_MULT_Z_INV_OFFSET: usize = X_MULT_Z_INV_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;


pub const QX_OFFSET: usize = Y_MULT_Z_INV_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const QY_OFFSET: usize = QX_OFFSET + 24;
pub const QZ_OFFSET: usize = QY_OFFSET + 24;
pub const FIRST_LOOP_SELECTOR_OFFSET: usize = QZ_OFFSET + 24;
pub const FIRST_ROW_SELECTOR_OFFSET: usize = FIRST_LOOP_SELECTOR_OFFSET + 1;
pub const RX_OFFSET: usize = FIRST_ROW_SELECTOR_OFFSET + 1;
pub const RY_OFFSET: usize = RX_OFFSET + 24;
pub const RZ_OFFSET: usize = RY_OFFSET + 24;
pub const T0_CALC_OFFSET: usize = RZ_OFFSET + 24;
pub const T1_CALC_OFFSET: usize = T0_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const X0_CALC_OFFSET: usize = T1_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const T2_CALC_OFFSET: usize = X0_CALC_OFFSET + FP2_FP_TOTAL_COLUMNS;
pub const T3_CALC_OFFSET: usize = T2_CALC_OFFSET + MULTIPLY_B_TOTAL_COLUMS;
pub const X1_CALC_OFFSET: usize = T3_CALC_OFFSET + FP2_FP_TOTAL_COLUMNS;
pub const T4_CALC_OFFSET: usize = X1_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const X2_CALC_OFFSET: usize = T4_CALC_OFFSET + FP2_FP_TOTAL_COLUMNS;
pub const X3_CALC_OFFSET: usize = X2_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const X4_CALC_OFFSET: usize = X3_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const X5_CALC_OFFSET: usize = X4_CALC_OFFSET + FP2_FP_TOTAL_COLUMNS;
pub const X6_CALC_OFFSET: usize = X5_CALC_OFFSET + FP2_ADDITION_TOTAL;
pub const X7_CALC_OFFSET: usize = X6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const X8_CALC_OFFSET: usize = X7_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const X9_CALC_OFFSET: usize = X8_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const X10_CALC_OFFSET: usize = X9_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const X11_CALC_OFFSET: usize = X10_CALC_OFFSET + FP2_FP_TOTAL_COLUMNS;
pub const X12_CALC_OFFSET: usize = X11_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const X13_CALC_OFFSET: usize = X12_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const NEW_RX_OFFSET: usize = X13_CALC_OFFSET + FP2_FP_TOTAL_COLUMNS;
pub const NEW_RY_OFFSET: usize = NEW_RX_OFFSET + FP2_FP_TOTAL_COLUMNS;
pub const NEW_RZ_OFFSET: usize = NEW_RY_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const TOTAL_COLUMNS: usize = NEW_RZ_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;

pub const COLUMNS: usize = TOTAL_COLUMNS;
pub const PUBLIC_INPUTS: usize = 72;

pub const X0_PUBLIC_INPUTS_OFFSET: usize = 0;
pub const X1_PUBLIC_INPUTS_OFFSET: usize = 12;
pub const Y0_PUBLIC_INPUTS_OFFSET: usize = 24;
pub const Y1_PUBLIC_INPUTS_OFFSET: usize = 36;
pub const Z0_PUBLIC_INPUTS_OFFSET: usize = 48;
pub const Z1_PUBLIC_INPUTS_OFFSET: usize = 60;



macro_rules! bit_decomp_32 {
    ($row:expr, $col:expr, $f:ty, $p:ty) => {
        ((0..32).fold(<$p>::ZEROS, |acc, i| {
            acc + $row[$col + i] * <$f>::from_canonical_u64(1 << i)
        }))
    };
}

// A (Fp) * B (Fp) => C (Fp)
#[derive(Clone)]
pub struct PairingPrecompStark<F: RichField + Extendable<D>, const D: usize> {
    pub trace: Vec<[F; TOTAL_COLUMNS]>,
    _num_rows: usize,
}

// Implement trace generator
impl<F: RichField + Extendable<D>, const D: usize> PairingPrecompStark<F, D> {
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

    pub fn fill_trace_addition_fp(
        &mut self,
        x: &[u32; 12],
        y: &[u32; 12],
        row: usize,
        start_col: usize,
    ) {
        self.trace[row][start_col + FP_ADDITION_CHECK_OFFSET] = F::ONE;
        let (x_y_sum, x_y_sum_carry) = add_u32_slices_12(&x, &y);
        self.assign_u32_in_series(row, start_col + FP_ADDITION_X_OFFSET, x);
        self.assign_u32_in_series(row, start_col + FP_ADDITION_Y_OFFSET, y);
        self.assign_u32_in_series(row, start_col + FP_ADDITION_SUM_OFFSET, &x_y_sum);
        self.assign_u32_in_series(row, start_col + FP_ADDITION_CARRY_OFFSET, &x_y_sum_carry);
    }

    pub fn fill_trace_negate_fp(
        &mut self,
        x: &[u32; 12],
        row: usize,
        start_col: usize
    ) {
        let minus_x = (-Fp(x.to_owned())).0;
        self.fill_trace_addition_fp(x, &minus_x, row, start_col);
    }

    pub fn fill_trace_subtraction_fp(
        &mut self,
        x: &[u32; 12],
        y: &[u32; 12],
        row: usize,
        start_col: usize,
    ) {
        self.trace[row][start_col + FP_SUBTRACTION_CHECK_OFFSET] = F::ONE;
        let (x_y_diff, x_y_borrow) = sub_u32_slices_12(&x, &y);
        self.assign_u32_in_series(row, start_col + FP_SUBTRACTION_X_OFFSET, x);
        self.assign_u32_in_series(row, start_col + FP_SUBTRACTION_Y_OFFSET, y);
        self.assign_u32_in_series(row, start_col + FP_SUBTRACTION_DIFF_OFFSET, &x_y_diff);
        self.assign_u32_in_series(row, start_col + FP_SUBTRACTION_BORROW_OFFSET, &x_y_borrow);
    }

    pub fn fill_trace_multiply_single_fp(
        &mut self,
        x: &[u32; 12],
        y: u32,
        row: usize,
        start_col: usize,
    ) {
        self.trace[row][start_col + FP_MULTIPLY_SINGLE_CHECK_OFFSET] = F::ONE;
        let (x_y_sum, x_y_carry) = mul_u32_slice_u32(x, y);
        self.assign_u32_in_series(row, start_col + FP_MULTIPLY_SINGLE_X_OFFSET, x);
        self.trace[row][start_col + FP_MULTIPLY_SINGLE_Y_OFFSET] = F::from_canonical_u32(y);
        self.assign_u32_in_series(row, start_col + FP_MULTIPLY_SINGLE_SUM_OFFSET, &x_y_sum);
        self.assign_u32_in_series(row, start_col + FP_MULTIPLY_SINGLE_CARRY_OFFSET, &x_y_carry);
    }

    pub fn fill_trace_reduce_single(
        &mut self,
        x: &[u32; 12],
        row: usize,
        start_col: usize,
    ) -> [u32; 12] {
        let (div, rem) = get_div_rem_modulus_from_biguint_12(BigUint::new(x.to_vec()));
        let div = div[0];
        let modulus = get_u32_vec_from_literal(modulus());
        self.fill_trace_multiply_single_fp(&modulus, div, row, start_col + FP_SINGLE_REDUCE_MULTIPLICATION_OFFSET);
        self.assign_u32_in_series(row, start_col + FP_SINGLE_REDUCE_X_OFFSET, x);
        let div_x_mod = get_u32_vec_from_literal(div.to_biguint().unwrap() * BigUint::new(modulus.to_vec()));
        self.assign_u32_in_series(row, start_col + FP_SINGLE_REDUCED_OFFSET, &rem);
        self.fill_trace_addition_fp(&div_x_mod, &rem, row, start_col + FP_SINGLE_REDUCTION_ADDITION_OFFSET);
        rem
    }

    pub fn fill_trace_addition_fp2(
        &mut self,
        x: &[[u32; 12]; 2],
        y: &[[u32; 12]; 2],
        row: usize,
        start_col: usize,
    ) {
        self.fill_trace_addition_fp(&x[0], &y[0], row, start_col + FP2_ADDITION_0_OFFSET);
        self.fill_trace_addition_fp(&x[1], &y[1], row, start_col + FP2_ADDITION_1_OFFSET);
    }

    pub fn fill_trace_subtraction_fp2(
        &mut self,
        x: &[[u32; 12]; 2],
        y: &[[u32; 12]; 2],
        row: usize,
        start_col: usize,
    ) {
        self.fill_trace_subtraction_fp(&x[0], &y[0], row, start_col + FP2_SUBTRACTION_0_OFFSET);
        self.fill_trace_subtraction_fp(&x[1], &y[1], row, start_col + FP2_SUBTRACTION_1_OFFSET);
    }

    pub fn fill_trace_multiply_single_fp2(
        &mut self,
        x: &[[u32; 12]; 2],
        y: &[u32; 2],
        row: usize,
        start_col: usize,
    ) {
        self.fill_trace_multiply_single_fp(&x[0], y[0], row, start_col + FP2_SUBTRACTION_0_OFFSET);
        self.fill_trace_multiply_single_fp(&x[1], y[1], row, start_col + FP2_SUBTRACTION_1_OFFSET);
    }

    pub fn fill_trace_negate_fp2(
        &mut self,
        x: &[[u32; 12]; 2],
        row: usize,
        start_col: usize
    ) {
        let minus_x: [[u32; 12]; 2] = (-Fp2([Fp(x[0].to_owned()), Fp(x[1].to_owned())])).0.iter().map(|x| x.0).collect::<Vec<[u32; 12]>>().try_into().unwrap();
        self.fill_trace_addition_fp2(x, &minus_x, row, start_col);
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
        self.trace[row][start_col + RANGE_CHECK_SELECTOR_OFFSET] = F::ONE;
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
        self.trace[start_row][start_col + MULTIPLICATION_FIRST_ROW_OFFSET] = F::ONE;
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

    fn fill_reduction_trace(
        &mut self,
        x: &[u32; 24],
        start_row: usize,
        end_row: usize,
        start_col: usize,
    ) -> [u32; 12] {
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
        println!("rem {:?}", rem_24);
        rem

    }


    pub fn generate_trace_fp2_mul(&mut self, x: [[u32; 12]; 2], y: [[u32; 12]; 2], start_row: usize, end_row: usize,start_col: usize) {
        let modulus = modulus();

        for i in start_row..end_row+1 {
            self.trace[i][start_col + FP2_FP2_SELECTOR_OFFSET] = F::ONE;
            self.assign_u32_in_series(i, start_col + FP2_FP2_X_INPUT_OFFSET, &x[0]);
            self.assign_u32_in_series(i, start_col + FP2_FP2_X_INPUT_OFFSET+12, &x[1]);
            self.assign_u32_in_series(i, start_col + FP2_FP2_Y_INPUT_OFFSET, &y[0]);
            self.assign_u32_in_series(i, start_col + FP2_FP2_Y_INPUT_OFFSET+12, &y[1]);
        }
        self.trace[end_row][start_col + FP2_FP2_SELECTOR_OFFSET] = F::ZERO;
        // filling trace for X0*Y0 - X1*Y1
        self.fill_multiplication_trace_no_mod_reduction(
            &x[0],
            &y[0],
            start_row,
            end_row,
            start_col + X_0_Y_0_MULTIPLICATION_OFFSET,
        );
        self.fill_multiplication_trace_no_mod_reduction(
            &x[1],
            &y[1],
            start_row,
            end_row,
            start_col + X_1_Y_1_MULTIPLICATION_OFFSET,
        );

        let x0y0 =
            get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y[0].to_vec()));
        let modulus_sq = get_u32_vec_from_literal_24(modulus.clone() * modulus.clone());
        self.fill_addition_trace(&x0y0, &modulus_sq, start_row + 11, start_col + Z1_ADD_MODULUS_OFFSET);

        let x0y0_add_modsq =
            get_u32_vec_from_literal_24(BigUint::new(x0y0.to_vec()) + modulus.clone() * modulus);
        let x1y1 =
            get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y[1].to_vec()));
        self.fill_subtraction_trace(&x0y0_add_modsq, &x1y1, start_row + 11, start_col + Z1_SUBTRACTION_OFFSET);

        let x0y0_x1y1 = get_u32_vec_from_literal_24(
            BigUint::new(x0y0_add_modsq.to_vec()) - BigUint::new(x1y1.to_vec()),
        );
        let rem = self.fill_reduction_trace(&x0y0_x1y1, start_row, end_row, start_col + Z1_REDUCE_OFFSET);
        self.fill_range_check_trace(&rem, start_row, start_col + Z1_RANGECHECK_OFFSET);

        // filling trace for X0*Y1 + X1*Y0
        self.fill_multiplication_trace_no_mod_reduction(
            &x[0],
            &y[1],
            start_row,
            end_row,
            start_col + X_0_Y_1_MULTIPLICATION_OFFSET,
        );
        self.fill_multiplication_trace_no_mod_reduction(
            &x[1],
            &y[0],
            start_row,
            end_row,
            start_col + X_1_Y_0_MULTIPLICATION_OFFSET,
        );

        let x0y1 =
            get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y[1].to_vec()));
        let x1y0 =
            get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y[0].to_vec()));
        self.fill_addition_trace(&x0y1, &x1y0, start_row + 11, start_col + Z2_ADDITION_OFFSET);

        let x0y1_x1y0 =
            get_u32_vec_from_literal_24(BigUint::new(x0y1.to_vec()) + BigUint::new(x1y0.to_vec()));
        let rem = self.fill_reduction_trace(&x0y1_x1y0, start_row, end_row, start_col + Z2_REDUCE_OFFSET);
        self.fill_range_check_trace(&rem, start_row, start_col + Z2_RANGECHECK_OFFSET);
    }

    pub fn fill_trace_fp2_fp_mul(&mut self, x: &[[u32; 12]; 2], y: &[u32; 12], start_row: usize, end_row: usize, start_col: usize) {
        for i in start_row..end_row + 1 {
            self.trace[i][start_col + FP2_FP_MUL_SELECTOR_OFFSET] = F::ONE;
            self.assign_u32_in_series(i, start_col + FP2_FP_X_INPUT_OFFSET, &x[0]);
            self.assign_u32_in_series(i, start_col + FP2_FP_X_INPUT_OFFSET + 12, &x[1]);
            self.assign_u32_in_series(i, start_col + FP2_FP_Y_INPUT_OFFSET, y);
        }
        self.trace[end_row][start_col + FP2_FP_MUL_SELECTOR_OFFSET] = F::ZERO;
        self.fill_multiplication_trace_no_mod_reduction(&x[0], y, start_row, end_row, start_col + X0_Y_MULTIPLICATION_OFFSET);
        let x0y = get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y.to_vec()));
        let rem = self.fill_reduction_trace(&x0y, start_row, end_row, start_col + X0_Y_REDUCE_OFFSET);
        self.fill_range_check_trace(&rem, start_row, start_col + X0_Y_RANGECHECK_OFFSET);
        self.fill_multiplication_trace_no_mod_reduction(&x[1], y, start_row, end_row, start_col + X1_Y_MULTIPLICATION_OFFSET);
        let x1y = get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y.to_vec()));
        let rem = self.fill_reduction_trace(&x1y, start_row, end_row, start_col + X1_Y_REDUCE_OFFSET);
        self.fill_range_check_trace(&rem, start_row, start_col + X1_Y_RANGECHECK_OFFSET);
    }

    pub fn fill_multiply_by_b_trace(&mut self, x: &[[u32; 12]; 2], start_row: usize, end_row: usize, start_col: usize) {
        for i in start_row..end_row + 1 {
            self.trace[i][start_col + MULTIPLY_B_SELECTOR_OFFSET] = F::ONE;
            self.assign_u32_in_series(i, start_col + MULTIPLY_B_X_OFFSET, &x[0]);
            self.assign_u32_in_series(i, start_col + MULTIPLY_B_X_OFFSET + 12, &x[1]);
        }
        self.trace[end_row][start_col + MULTIPLY_B_SELECTOR_OFFSET] = F::ZERO;
        let y = Fp::get_fp_from_biguint(BigUint::from(4 as u32)).0;
        self.fill_multiplication_trace_no_mod_reduction(&x[0], &y, start_row, end_row, start_col + MULTIPLY_B_X0_B_MUL_OFFSET);
        self.fill_multiplication_trace_no_mod_reduction(&x[1], &y, start_row, end_row, start_col + MULTIPLY_B_X1_B_MUL_OFFSET);
        let x0y = get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y.to_vec()));
        let x1y = get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y.to_vec()));
        let modulus = modulus();
        let modulus_sq = get_u32_vec_from_literal_24(modulus.clone() * modulus.clone());
        self.fill_addition_trace(&x0y, &modulus_sq, start_row + 11, start_col + MULTIPLY_B_ADD_MODSQ_OFFSET);
        let x0y_add_modsq =
            get_u32_vec_from_literal_24(BigUint::new(x0y.to_vec()) + BigUint::new(modulus_sq.to_vec()));
        self.fill_subtraction_trace(&x0y_add_modsq, &x1y, start_row + 11, start_col + MULTIPLY_B_SUB_OFFSET);
        let x0y_x1y = get_u32_vec_from_literal_24(
            BigUint::new(x0y_add_modsq.to_vec()) - BigUint::new(x1y.to_vec()),
        );
        let rem = self.fill_reduction_trace(&x0y_x1y, start_row, end_row, start_col + MULTIPLY_B_Z0_REDUCE_OFFSET);
        self.fill_range_check_trace(&rem, start_row, start_col + MULTIPLY_B_Z0_RANGECHECK_OFFSET);


        self.fill_addition_trace(&x0y, &x1y, start_row + 11, start_col + MULTIPLY_B_ADD_OFFSET);
        let x0y_x1y = get_u32_vec_from_literal_24(
            BigUint::new(x0y.to_vec()) + BigUint::new(x1y.to_vec()),
        );
        let rem = self.fill_reduction_trace(&x0y_x1y, start_row, end_row, start_col + MULTIPLY_B_Z1_REDUCE_OFFSET);
        self.fill_range_check_trace(&rem, start_row, start_col + MULTIPLY_B_Z1_RANGECHECK_OFFSET);
    }

    pub fn fill_trace_subtraction_with_reduction(&mut self, x: &[[u32; 12]; 2], y: &[[u32; 12]; 2], row: usize, start_col: usize) {
        let modulus = get_u32_vec_from_literal(modulus());
        self.fill_trace_addition_fp2(x, &[modulus, modulus], row, start_col);
        let x0_modulus = get_u32_vec_from_literal(
            BigUint::new(x[0].to_vec()) + BigUint::new(modulus.to_vec())
        );
        let x1_modulus = get_u32_vec_from_literal(
            BigUint::new(x[1].to_vec()) + BigUint::new(modulus.to_vec())
        );
        self.fill_trace_subtraction_fp2(&[x0_modulus, x1_modulus], y, row, start_col + FP2_ADDITION_TOTAL);
        let x0_y0 = get_u32_vec_from_literal(
            BigUint::new(x0_modulus.to_vec()) - BigUint::new(y[0].to_vec())
        );
        let x1_y1 = get_u32_vec_from_literal(
            BigUint::new(x1_modulus.to_vec()) - BigUint::new(y[1].to_vec())
        );
        let rem = self.fill_trace_reduce_single(&x0_y0, row, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL);
        self.fill_range_check_trace(&rem, row, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL);
        let rem = self.fill_trace_reduce_single(&x1_y1, row, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL);
        self.fill_range_check_trace(&rem, row, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL);
    }

    pub fn fill_trace_addition_with_reduction(&mut self, x: &[[u32; 12]; 2], y: &[[u32; 12]; 2], row: usize, start_col: usize) {
        self.fill_trace_addition_fp2(x, y, row, start_col);
        let x0_y0 = get_u32_vec_from_literal(
            BigUint::new(x[0].to_vec()) + BigUint::new(y[0].to_vec())
        );
        let x1_y1 = get_u32_vec_from_literal(
            BigUint::new(x[1].to_vec()) + BigUint::new(y[1].to_vec())
        );
        let rem = self.fill_trace_reduce_single(&x0_y0, row, start_col + FP2_ADDITION_TOTAL);
        self.fill_range_check_trace(&rem, row, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL);
        let rem = self.fill_trace_reduce_single(&x1_y1, row, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL);
        self.fill_range_check_trace(&rem, row, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL);
    }

    pub fn generate_trace(&mut self, x: [[u32; 12]; 2], y: [[u32; 12]; 2], z:[[u32; 12]; 2]) {
        /* 
            TODOS:
            1. Calculate z_inv -> constrain z*z_inv == 1 - done
            2. Qx, Qy, Qz rows fill start to end (assert eq all rows)
            3. Rx, Ry, Rz (assert first row)
        */ 
        let z_fp2  = Fp2([Fp(z[0]), Fp(z[1])]);
        let z_inv = z_fp2.invert();
        let z_inv_slice: [[u32; 12]; 2] = [z_inv.0[0].0, z_inv.0[1].0];
        self.generate_trace_fp2_mul(z, z_inv_slice, 0, self._num_rows-1, 0);

        // Calculate ax = x * (z_inv)
        self.generate_trace_fp2_mul(x, z_inv_slice, 0, self._num_rows-1, X_MULT_Z_INV_OFFSET);

        // Calculate ay = y * (z_inv)
        self.generate_trace_fp2_mul(y, z_inv_slice, 0, self._num_rows-1, Y_MULT_Z_INV_OFFSET);

        let (Qx, Qy, Qz) = calc_qs(
            Fp2([Fp(x[0]), Fp(x[1])]), Fp2([Fp(y[0]), Fp(y[1])]), Fp2([Fp(z[0]), Fp(z[1])])
        );

        // Fill Qx, Qy, Qz for all rows
        for row in 0..self._num_rows {
            for i in 0..12 {
                self.trace[row][QX_OFFSET + i] = F::from_canonical_u64(Qx.0[0].0[i] as u64);//self.trace[0][X_MULT_Z_INV_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i];
                self.trace[row][QX_OFFSET + i + 12] = F::from_canonical_u64(Qx.0[1].0[i] as u64);//self.trace[0][X_MULT_Z_INV_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i];
                self.trace[row][QY_OFFSET + i] = F::from_canonical_u64(Qy.0[0].0[i] as u64);//self.trace[0][Y_MULT_Z_INV_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i];
                self.trace[row][QY_OFFSET + i + 12] = F::from_canonical_u64(Qy.0[1].0[i] as u64);//self.trace[0][Y_MULT_Z_INV_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i];
                self.trace[row][QZ_OFFSET + i] = F::ZERO;
                self.trace[row][QZ_OFFSET + i + 12] = F::ZERO;
            }
            self.trace[row][QZ_OFFSET] = F::ONE;
        }

        let (Rx, Ry, Rz) = (Qx, Qy, Qz);
        for row in 0..12 {
            self.trace[row][FIRST_LOOP_SELECTOR_OFFSET] = F::ONE;
            for i in 0..24 {
                self.trace[row][RX_OFFSET + i] = self.trace[row][QX_OFFSET + i];
                self.trace[row][RY_OFFSET + i] = self.trace[row][QY_OFFSET + i];
                self.trace[row][RZ_OFFSET + i] = self.trace[row][QZ_OFFSET + i];
            }
        }
        self.trace[0][FIRST_ROW_SELECTOR_OFFSET] = F::ONE;

        // Loop 0
        let values_0 = calc_precomp_stuff_loop0(Qx, Qy, Qz, Qx, Qy, Qz);
        // t0
        self.generate_trace_fp2_mul(Ry.get_u32_slice(), Ry.get_u32_slice(), 0, 11, T0_CALC_OFFSET);
        // t1
        self.generate_trace_fp2_mul(Rz.get_u32_slice(), Rz.get_u32_slice(), 0, 11, T1_CALC_OFFSET);
        // x0
        self.fill_trace_fp2_fp_mul(&values_0[4].get_u32_slice(), &Fp::get_fp_from_biguint(BigUint::from_str("3").unwrap()).0, 0, 11, X0_CALC_OFFSET);
        // t2
        self.fill_multiply_by_b_trace(&values_0[5].get_u32_slice(), 0, 11, T2_CALC_OFFSET);
        // t3
        self.fill_trace_fp2_fp_mul(&values_0[6].get_u32_slice(), &Fp::get_fp_from_biguint(BigUint::from_str("3").unwrap()).0, 0, 11, T3_CALC_OFFSET);
        // x1
        self.generate_trace_fp2_mul(Ry.get_u32_slice(), Rz.get_u32_slice(), 0, 11, X1_CALC_OFFSET);
        // t4
        self.fill_trace_fp2_fp_mul(&values_0[8].get_u32_slice(), &Fp::get_fp_from_biguint(BigUint::from_str("2").unwrap()).0, 0, 11, T4_CALC_OFFSET);
        // x2
        for row in 0..12 {
            self.fill_trace_subtraction_with_reduction(&values_0[6].get_u32_slice(), &values_0[3].get_u32_slice(), row, X2_CALC_OFFSET);
        }
        // x3
        self.generate_trace_fp2_mul(Rx.get_u32_slice(), Rx.get_u32_slice(), 0, 11, X3_CALC_OFFSET);
        // x4
        self.fill_trace_fp2_fp_mul(&values_0[10].get_u32_slice(), &Fp::get_fp_from_biguint(BigUint::from_str("3").unwrap()).0, 0, 11, X4_CALC_OFFSET);
        // x5
        for row in 0..12 {
            self.fill_trace_negate_fp2(&values_0[9].get_u32_slice(), row, X5_CALC_OFFSET);
        }
        // x6
        for row in 0..12 {
            self.fill_trace_subtraction_with_reduction(&values_0[3].get_u32_slice(), &values_0[7].get_u32_slice(), row, X6_CALC_OFFSET);
        }
        // x7
        self.generate_trace_fp2_mul(Rx.get_u32_slice(), Ry.get_u32_slice(), 0, 11, X7_CALC_OFFSET);
        // x8
        self.generate_trace_fp2_mul(values_0[14].get_u32_slice(), values_0[15].get_u32_slice(), 0, 11, X8_CALC_OFFSET);
        // x9
        for row in 0..12 {
            self.fill_trace_addition_with_reduction(&values_0[3].get_u32_slice(), &values_0[7].get_u32_slice(), row, X9_CALC_OFFSET);
        }
        let k = get_u32_vec_from_literal(mod_inverse(BigUint::from(2 as u32), modulus()));
        // x10
        self.fill_trace_fp2_fp_mul(&values_0[17].get_u32_slice(), &k, 0, 11, X10_CALC_OFFSET);
        // x11
        self.generate_trace_fp2_mul(values_0[18].get_u32_slice(), values_0[18].get_u32_slice(), 0, 11, X11_CALC_OFFSET);
        // x12
        self.generate_trace_fp2_mul(values_0[6].get_u32_slice(), values_0[6].get_u32_slice(), 0, 11, X12_CALC_OFFSET);
        // x13
        self.fill_trace_fp2_fp_mul(&values_0[20].get_u32_slice(), &Fp::get_fp_from_biguint(BigUint::from_str("3").unwrap()).0, 0, 11, X13_CALC_OFFSET);
        // new Rx
        self.fill_trace_fp2_fp_mul(&values_0[16].get_u32_slice(), &k, 0, 11, NEW_RX_OFFSET);
        // new Ry
        for row in 0..12 {
            self.fill_trace_subtraction_with_reduction(&values_0[19].get_u32_slice(), &values_0[21].get_u32_slice(), row, NEW_RY_OFFSET);
        }
        // new Rz
        self.generate_trace_fp2_mul(values_0[3].get_u32_slice(), values_0[9].get_u32_slice(), 0, 11, NEW_RZ_OFFSET);

        for row in 12..self._num_rows {
            self.assign_u32_in_series(row, RX_OFFSET, &values_0[0].get_u32_slice()[0]);
            self.assign_u32_in_series(row, RX_OFFSET + 12, &values_0[0].get_u32_slice()[1]);
            self.assign_u32_in_series(row, RY_OFFSET, &values_0[1].get_u32_slice()[0]);
            self.assign_u32_in_series(row, RY_OFFSET + 12, &values_0[1].get_u32_slice()[1]);
            self.assign_u32_in_series(row, RZ_OFFSET, &values_0[2].get_u32_slice()[0]);
            self.assign_u32_in_series(row, RZ_OFFSET + 12, &values_0[2].get_u32_slice()[1]);
        }
        self.trace[12][FIRST_ROW_SELECTOR_OFFSET] = F::ONE;
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
            local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
            (
                local_values[start_col + X_INPUT_OFFSET + i]
                - next_values[start_col + X_INPUT_OFFSET + i]
            ),
        );
        yield_constr.constraint_transition(
            local_values[start_col + MULTIPLICATION_SELECTOR_OFFSET] *
            (
                local_values[start_col + Y_INPUT_OFFSET + i]
                - next_values[start_col + Y_INPUT_OFFSET + i]
            ),
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
        yield_constr.constraint(
            local_values[start_col + MULTIPLICATION_FIRST_ROW_OFFSET] *
            (
            local_values[start_col + SUM_OFFSET + j]
                - local_values[start_col + SHIFTED_XY_OFFSET + j]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLICATION_FIRST_ROW_OFFSET] *
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

pub fn add_addition_fp_constraints<
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
    for j in 0..12 {
        if j == 0 {
            yield_constr.constraint(
                local_values[start_col + FP_ADDITION_CHECK_OFFSET]
                    * (local_values[start_col + FP_ADDITION_SUM_OFFSET + j]
                        + (local_values[start_col + FP_ADDITION_CARRY_OFFSET + j]
                            * FE::from_canonical_u64(1 << 32))
                        - local_values[start_col + FP_ADDITION_X_OFFSET + j]
                        - local_values[start_col + FP_ADDITION_Y_OFFSET + j]),
            )
        } else {
            yield_constr.constraint(
                local_values[start_col + FP_ADDITION_CHECK_OFFSET]
                    * (local_values[start_col + FP_ADDITION_SUM_OFFSET + j]
                        + (local_values[start_col + FP_ADDITION_CARRY_OFFSET + j]
                            * FE::from_canonical_u64(1 << 32))
                        - local_values[start_col + FP_ADDITION_X_OFFSET + j]
                        - local_values[start_col + FP_ADDITION_Y_OFFSET + j]
                        - local_values[start_col + FP_ADDITION_CARRY_OFFSET + j - 1]),
            )
        }
    }
}

pub fn add_subtraction_fp_constraints<
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
    for j in 0..12 {
        if j == 0 {
            yield_constr.constraint(
                local_values[start_col + FP_SUBTRACTION_CHECK_OFFSET]
                    * (local_values[start_col + FP_SUBTRACTION_DIFF_OFFSET + j]
                        + local_values[start_col + FP_SUBTRACTION_Y_OFFSET + j]
                        - (local_values[start_col + FP_SUBTRACTION_BORROW_OFFSET + j]
                            * FE::from_canonical_u64(1 << 32))
                        - local_values[start_col + FP_SUBTRACTION_X_OFFSET + j]),
            )
        } else {
            yield_constr.constraint(
                local_values[start_col + FP_SUBTRACTION_CHECK_OFFSET]
                    * (local_values[start_col + FP_SUBTRACTION_DIFF_OFFSET + j]
                        + local_values[start_col + FP_SUBTRACTION_Y_OFFSET + j]
                        + local_values[start_col + FP_SUBTRACTION_BORROW_OFFSET + j - 1]
                        - (local_values[start_col + FP_SUBTRACTION_BORROW_OFFSET + j]
                            * FE::from_canonical_u64(1 << 32))
                        - local_values[start_col + FP_SUBTRACTION_X_OFFSET + j]),
            )
        }
    }
}

pub fn add_negate_fp_constraints<
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
    add_addition_fp_constraints(local_values, yield_constr, start_col);
    let mod_u32 = get_u32_vec_from_literal(modulus());
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP_ADDITION_SUM_OFFSET + i] - FE::from_canonical_u32(mod_u32[i])
            )
        );
    }
}

pub fn add_fp_single_multiply_constraints<
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
    for j in 0..12 {
        if j == 0 {
            yield_constr.constraint(
                local_values[start_col + FP_MULTIPLY_SINGLE_CHECK_OFFSET] *
                (local_values[start_col + FP_MULTIPLY_SINGLE_SUM_OFFSET + j]
                    + (local_values[start_col + FP_MULTIPLY_SINGLE_CARRY_OFFSET + j]
                        * FE::from_canonical_u64(1 << 32))
                    - local_values[start_col + FP_MULTIPLY_SINGLE_X_OFFSET + j]
                    * local_values[start_col + FP_MULTIPLY_SINGLE_Y_OFFSET]),
            )
        } else {
            yield_constr.constraint(
                local_values[start_col + FP_MULTIPLY_SINGLE_CHECK_OFFSET] *
                (local_values[start_col + FP_MULTIPLY_SINGLE_SUM_OFFSET + j]
                    + (local_values[start_col + FP_MULTIPLY_SINGLE_CARRY_OFFSET + j]
                        * FE::from_canonical_u64(1 << 32))
                    - local_values[start_col + FP_MULTIPLY_SINGLE_X_OFFSET + j]
                    * local_values[start_col + FP_MULTIPLY_SINGLE_Y_OFFSET]
                    - local_values[start_col + FP_MULTIPLY_SINGLE_CARRY_OFFSET + j - 1]),
            )
        }
    }
}

pub fn add_fp_reduce_single_constraints<
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
    let modulus = modulus();
    let modulus_u32 = get_u32_vec_from_literal(modulus);
    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[start_col + FP_SINGLE_REDUCE_MULTIPLICATION_OFFSET + FP_MULTIPLY_SINGLE_CHECK_OFFSET] * (
                local_values[start_col + FP_SINGLE_REDUCE_MULTIPLICATION_OFFSET + FP_MULTIPLY_SINGLE_X_OFFSET + i] -
                FE::from_canonical_u32(modulus_u32[i])
            )
        );
    }

    add_fp_single_multiply_constraints(local_values, yield_constr, start_col + FP_SINGLE_REDUCE_MULTIPLICATION_OFFSET);

    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[start_col + FP_SINGLE_REDUCTION_ADDITION_OFFSET + FP_ADDITION_CHECK_OFFSET]
                * (local_values[start_col + FP_SINGLE_REDUCE_MULTIPLICATION_OFFSET + FP_MULTIPLY_SINGLE_SUM_OFFSET + i]
                    - local_values[start_col + FP_SINGLE_REDUCTION_ADDITION_OFFSET + FP_ADDITION_X_OFFSET + i]),
        );
    }

    add_addition_fp_constraints(
        local_values,
        yield_constr,
        start_col + FP_SINGLE_REDUCTION_ADDITION_OFFSET,
    );

    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[start_col + FP_SINGLE_REDUCTION_ADDITION_OFFSET + FP_ADDITION_CHECK_OFFSET]
                * (local_values[start_col + FP_SINGLE_REDUCED_OFFSET + i]
                    - local_values
                        [start_col + FP_SINGLE_REDUCTION_ADDITION_OFFSET + FP_ADDITION_Y_OFFSET + i]),
        );
    }

    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[start_col + FP_SINGLE_REDUCTION_ADDITION_OFFSET + FP_ADDITION_CHECK_OFFSET]
                * (local_values[start_col + FP_SINGLE_REDUCE_X_OFFSET + i]
                    - local_values
                        [start_col + FP_SINGLE_REDUCTION_ADDITION_OFFSET + FP_ADDITION_SUM_OFFSET + i]),
        )
    }

}

pub fn add_addition_fp2_constraints<
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
    add_addition_fp_constraints(local_values, yield_constr, start_col + FP2_ADDITION_0_OFFSET);
    add_addition_fp_constraints(local_values, yield_constr, start_col + FP2_ADDITION_1_OFFSET);
}

pub fn add_subtraction_fp2_constraints<
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
    add_subtraction_fp_constraints(local_values, yield_constr, start_col + FP2_SUBTRACTION_0_OFFSET);
    add_subtraction_fp_constraints(local_values, yield_constr, start_col + FP2_SUBTRACTION_1_OFFSET);
}

pub fn add_fp2_single_multiply_constraints<
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
    add_fp_single_multiply_constraints(local_values, yield_constr, start_col + FP2_MULTIPLY_SINGLE_0_OFFSET);
    add_fp_single_multiply_constraints(local_values, yield_constr, start_col + FP2_MULTIPLY_SINGLE_1_OFFSET);
}

pub fn add_negate_fp2_constraints<
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
    add_addition_fp2_constraints(local_values, yield_constr, start_col);
    let mod_u32 = get_u32_vec_from_literal(modulus());
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i] - FE::from_canonical_u32(mod_u32[i])
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i] - FE::from_canonical_u32(mod_u32[i])
            )
        );
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
            yield_constr.constraint(
                local_values[start_col + RANGE_CHECK_SELECTOR_OFFSET] * (
                    local_values[start_col + RANGE_CHECK_SUM_OFFSET + i]
                        + (local_values[start_col + RANGE_CHECK_SUM_CARRY_OFFSET + i]
                            * FE::from_canonical_u64(1 << 32))
                        - FE::from_canonical_u32(y_u32[i])
                        - local_values[start_col - 12 + i]
                )
            );
        } else if i < 12 {
            yield_constr.constraint(
                local_values[start_col + RANGE_CHECK_SELECTOR_OFFSET] * (
                    local_values[start_col + RANGE_CHECK_SUM_OFFSET + i]
                        + (local_values[start_col + RANGE_CHECK_SUM_CARRY_OFFSET + i]
                            * FE::from_canonical_u64(1 << 32))
                        - FE::from_canonical_u32(y_u32[i])
                        - local_values[start_col - 12 + i]
                        - local_values[start_col + RANGE_CHECK_SUM_CARRY_OFFSET + i - 1]
                )
            );
        }
        let bit_col: usize = start_col + RANGE_CHECK_BIT_DECOMP_OFFSET;
        let val_reconstructed = bit_decomp_32!(local_values, bit_col, FE, P);
        yield_constr.constraint(
            local_values[start_col + RANGE_CHECK_SELECTOR_OFFSET] * (val_reconstructed - local_values[start_col + RANGE_CHECK_SUM_OFFSET + 11])
        );
        yield_constr.constraint(local_values[start_col + RANGE_CHECK_SELECTOR_OFFSET] * local_values[bit_col + 30]);
    }
}

fn add_reduce_constraints<
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
    selector_col: usize,
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let modulus = modulus();
    let modulus_u32 = get_u32_vec_from_literal(modulus);
    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[selector_col] *
            (
            local_values[start_col + REDUCE_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
                - FE::from_canonical_u32(modulus_u32[i])
            )
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
            local_values[selector_col] *
            (
            local_values[start_col + REDUCE_X_OFFSET + i]
                - next_values[start_col + REDUCE_X_OFFSET + i]
            )
        );
    }

    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[selector_col] *
            (
            local_values[start_col + REDUCED_OFFSET + i]
                - next_values[start_col + REDUCED_OFFSET + i]
            )
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

}

fn add_fp2_mul_constraints<
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
    // for i in 0..12 {
    //     yield_constr.constraint_transition(local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i])
    // }
    for i in 0..12 {
        yield_constr.constraint(local_values[start_col + FP2_FP2_SELECTOR_OFFSET] * 
            (local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(local_values[start_col + FP2_FP2_SELECTOR_OFFSET] * 
            (local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(local_values[start_col + FP2_FP2_SELECTOR_OFFSET] * 
            (local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(local_values[start_col + FP2_FP2_SELECTOR_OFFSET] * 
            (local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(local_values[start_col + FP2_FP2_SELECTOR_OFFSET] * 
            (local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(local_values[start_col + FP2_FP2_SELECTOR_OFFSET] * 
            (local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(local_values[start_col + FP2_FP2_SELECTOR_OFFSET] * 
            (local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(local_values[start_col + FP2_FP2_SELECTOR_OFFSET] * 
            (local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i + 12])
        );
    }

    // constrain X_0*Y_0
    add_multiplication_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + X_0_Y_0_MULTIPLICATION_OFFSET,
    );


    // constrain X_1*Y_1
    add_multiplication_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + X_1_Y_1_MULTIPLICATION_OFFSET,
    );

    // constrain X0*Y0 with X0*Y0 + modulus^2
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_X_OFFSET + i]
                    - local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
        );
    }

    // constrain modulus^2 with X0*Y0 + modulus^2
    let modulus = modulus();
    let modulus_sq_u32 = get_u32_vec_from_literal_24(modulus.clone() * modulus);
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_Y_OFFSET + i]
                    - FE::from_canonical_u32(modulus_sq_u32[i])),
        );
    }

    // constrain X0*Y0 + modulus^2
    add_addition_constraints(local_values, yield_constr, start_col + Z1_ADD_MODULUS_OFFSET);

    // constrain X0*Y0 + modulus^2 with X0*Y0 + modulus^2 - X1Y1
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]
                * (local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_X_OFFSET + i]
                    - local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_SUM_OFFSET + i]),
        );
    }

    // constrain X1*Y1 + modulus^2 with X0*Y0 + modulus^2 - X1Y1
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]
                * (local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_Y_OFFSET + i]
                    - local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
        );
    }

    // constrain X0*Y0 + modulus^2 - X1Y1
    add_subtraction_constraints(local_values, yield_constr, start_col + Z1_SUBTRACTION_OFFSET);

    // constrain X0*Y0 + modulus^2 - X1Y1 with reduction
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]
                * (local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_DIFF_OFFSET + i]
                    - local_values[start_col + Z1_REDUCE_OFFSET + REDUCE_X_OFFSET + i]),
        );
    }



    // constrain reduction
    add_reduce_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + Z1_REDUCE_OFFSET,
        start_col + FP2_FP2_SELECTOR_OFFSET,
    );
    add_range_check_constraints(local_values, yield_constr, start_col + Z1_RANGECHECK_OFFSET);



    // constrain X_1*Y_0
    add_multiplication_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + X_0_Y_1_MULTIPLICATION_OFFSET,
    );



    // constrain X_1*Y_0
    add_multiplication_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + X_1_Y_0_MULTIPLICATION_OFFSET,
    );

    // constrain X0*Y1 with X0*Y1 + X1*Y0
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_X_OFFSET + i]
                    - local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
        );
    }

    // constrain X1*Y0 with X0*Y1 + X1*Y0
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_Y_OFFSET + i]
                    - local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
        );
    }

    // constrain X0*Y1 + X1*Y0
    add_addition_constraints(local_values, yield_constr, start_col + Z2_ADDITION_OFFSET);

    // constrain X0*Y1 + X1*Y0 with reduction
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i]
                    - local_values[start_col + Z2_REDUCE_OFFSET + REDUCE_X_OFFSET + i]),
        );
    }

    // constrain reduction
    add_reduce_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + Z2_REDUCE_OFFSET,
        start_col + FP2_FP2_SELECTOR_OFFSET,
    );
    add_range_check_constraints(local_values, yield_constr, start_col + Z2_RANGECHECK_OFFSET);
}

pub fn add_fp2_fp_mul_constraints<
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
    // constrain inputs to multiplication
    for i in 0..12 {
        yield_constr.constraint_transition(
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[start_col + FP2_FP_X_INPUT_OFFSET + i] - local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint_transition(
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[start_col + FP2_FP_X_INPUT_OFFSET + 12 + i] - local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint_transition(
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[start_col + FP2_FP_Y_INPUT_OFFSET + i] - local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint_transition(
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[start_col + FP2_FP_Y_INPUT_OFFSET + i] - local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
            )
        );
    }
    add_multiplication_constraints(local_values, next_values, yield_constr, start_col + X0_Y_MULTIPLICATION_OFFSET);
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + X0_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + X0_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i] -
                local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + SUM_OFFSET + i]
            )
        );
    }
    add_reduce_constraints(local_values, next_values, yield_constr, start_col + X0_Y_REDUCE_OFFSET, start_col + FP2_FP_MUL_SELECTOR_OFFSET);
    add_range_check_constraints(local_values, yield_constr, start_col + X0_Y_RANGECHECK_OFFSET);
    add_multiplication_constraints(local_values, next_values, yield_constr, start_col + X1_Y_MULTIPLICATION_OFFSET);
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + X1_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + X1_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i] -
                local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + SUM_OFFSET + i]
            )
        );
    }
    add_reduce_constraints(local_values, next_values, yield_constr, start_col + X1_Y_REDUCE_OFFSET, start_col + FP2_FP_MUL_SELECTOR_OFFSET);
    add_range_check_constraints(local_values, yield_constr, start_col + X1_Y_RANGECHECK_OFFSET);
}

pub fn add_multiply_by_b_constraints<
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
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * (
                local_values[start_col + MULTIPLY_B_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + X_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * (
                local_values[start_col + MULTIPLY_B_X_OFFSET + 12 + i] - local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + X_INPUT_OFFSET + i]
            )
        );
        if i == 0 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * (
                    local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + Y_INPUT_OFFSET + i] - FE::from_canonical_u32(4)
                )
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * (
                    local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + Y_INPUT_OFFSET + i] - FE::from_canonical_u32(4)
                )
            );
        } else {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + Y_INPUT_OFFSET + i]
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + Y_INPUT_OFFSET + i]
            );
        }
    }
    add_multiplication_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_B_X0_B_MUL_OFFSET);
    add_multiplication_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_B_X1_B_MUL_OFFSET);
    let modulus = modulus();
    let modulus_sq_u32 = get_u32_vec_from_literal_24(modulus.clone() * modulus);
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_Y_OFFSET + i] - FE::from_canonical_u32(modulus_sq_u32[i])
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_Y_OFFSET + i] - local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_Y_OFFSET + i] - local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + SUM_OFFSET + i]
            )
        );
    }
    add_addition_constraints(local_values, yield_constr, start_col + MULTIPLY_B_ADD_MODSQ_OFFSET);
    add_subtraction_constraints(local_values, yield_constr, start_col + MULTIPLY_B_SUB_OFFSET);
    add_addition_constraints(local_values, yield_constr, start_col + MULTIPLY_B_ADD_OFFSET);
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_Z0_REDUCE_OFFSET + REDUCE_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_DIFF_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_Z1_REDUCE_OFFSET + REDUCE_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_SUM_OFFSET + i]
            )
        );
    }
    add_reduce_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_B_Z0_REDUCE_OFFSET, start_col + MULTIPLY_B_SELECTOR_OFFSET);
    add_range_check_constraints(local_values, yield_constr, start_col + MULTIPLY_B_Z0_RANGECHECK_OFFSET);
    add_reduce_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_B_Z1_REDUCE_OFFSET, start_col + MULTIPLY_B_SELECTOR_OFFSET);
    add_range_check_constraints(local_values, yield_constr, start_col + MULTIPLY_B_Z1_RANGECHECK_OFFSET);
}

pub fn add_subtraction_with_reduction_constranints<
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
    let modulus = get_u32_vec_from_literal(modulus());
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                FE::from_canonical_u32(modulus[i])
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                FE::from_canonical_u32(modulus[i])
            )
        );
    }
    add_addition_fp2_constraints(local_values, yield_constr, start_col);
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_X_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_X_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i]
            )
        );
    }
    add_subtraction_fp2_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL);
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_DIFF_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL);
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_DIFF_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL);
}

pub fn add_addition_with_reduction_constranints<
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
    add_addition_fp2_constraints(local_values, yield_constr, start_col);
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL);
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL);
}

// Implement constraint generator
impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for PairingPrecompStark<F, D> {
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

        //  ---- Constrain z * z_inv ---
        // Z = [X0, Y0]
        // Z_INV = [X1, Y1] // We dont need to public input constrain Z_INV
        // Z * Z_INV = [c1, c2] => [c1 => [1,..,0], c2 => [0,..,0]]
        for i in 0..12 {
            if i == 0 {
                yield_constr.constraint_first_row(
                    local_values[Z1_REDUCE_OFFSET + REDUCED_OFFSET + i] - FE::ONE
                )
            } else {
                yield_constr.constraint_first_row(
                    local_values[Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            }
            yield_constr.constraint_first_row(
                local_values[Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        }
        // let match_inputs_z_mult_z_inv: Vec<P> = [
        //     &public_inputs[Z0_PUBLIC_INPUTS_OFFSET..Z0_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[Z0_PUBLIC_INPUTS_OFFSET..Z0_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[Z1_PUBLIC_INPUTS_OFFSET..Z1_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[Z1_PUBLIC_INPUTS_OFFSET..Z1_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     ].concat();
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[Z_MULT_Z_INV_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - public_inputs[Z0_PUBLIC_INPUTS_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[Z_MULT_Z_INV_OFFSET + FP2_FP2_X_INPUT_OFFSET + 12 + i] - public_inputs[Z1_PUBLIC_INPUTS_OFFSET + i]
            );
        }
        add_fp2_mul_constraints(local_values, next_values,yield_constr, 0);


        // Constrain ax = x * z_inv
        // Constrain Z-inv matches with last Z_MULT_Z_INV
        // COnstraint X match with public input
        // let match_inputs_x_mult_z_inv: Vec<P> = [
        //     &public_inputs[X0_PUBLIC_INPUTS_OFFSET..X0_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[X0_PUBLIC_INPUTS_OFFSET..X0_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[X1_PUBLIC_INPUTS_OFFSET..X1_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[X1_PUBLIC_INPUTS_OFFSET..X1_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        // ].concat();
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[X_MULT_Z_INV_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - public_inputs[X0_PUBLIC_INPUTS_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[X_MULT_Z_INV_OFFSET + FP2_FP2_X_INPUT_OFFSET + 12 + i] - public_inputs[X1_PUBLIC_INPUTS_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[X_MULT_Z_INV_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[X_MULT_Z_INV_OFFSET + FP2_FP2_Y_INPUT_OFFSET + 12 + i] - local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
            );
        }
        add_fp2_mul_constraints(local_values, next_values,yield_constr, X_MULT_Z_INV_OFFSET);

        // Constrain ay = y * z_inv
        // Constrain Z-inv matches with last Z_MULT_Z_INV
        // COnstraint Y match with public input
        // let match_inputs_y_mult_z_inv: Vec<P> = [
        //     &public_inputs[Y0_PUBLIC_INPUTS_OFFSET..Y0_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[Y0_PUBLIC_INPUTS_OFFSET..Y0_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[Y1_PUBLIC_INPUTS_OFFSET..Y1_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        //     &public_inputs[Y1_PUBLIC_INPUTS_OFFSET..Y1_PUBLIC_INPUTS_OFFSET+12].iter().map(|x| P::ZEROS + x.clone()).collect::<Vec<P>>(),
        //     &local_values[Z_MULT_Z_INV_OFFSET + X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET..Z_MULT_Z_INV_OFFSET + X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET+12],
        // ].concat();
        for i in 0..12 {
            yield_constr.constraint_first_row(
                local_values[Y_MULT_Z_INV_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - public_inputs[Y0_PUBLIC_INPUTS_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[Y_MULT_Z_INV_OFFSET + FP2_FP2_X_INPUT_OFFSET + 12 + i] - public_inputs[Y1_PUBLIC_INPUTS_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[Y_MULT_Z_INV_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[Y_MULT_Z_INV_OFFSET + FP2_FP2_Y_INPUT_OFFSET + 12 + i] - local_values[Z_MULT_Z_INV_OFFSET + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
            );
        }
        add_fp2_mul_constraints(local_values, next_values, yield_constr, Y_MULT_Z_INV_OFFSET);

        // Constrain Qx, Qy, Qz
        for i in 0..12 {
            // Qx
            yield_constr.constraint_first_row(
                local_values[X_MULT_Z_INV_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i] -
                local_values[QX_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[X_MULT_Z_INV_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i] -
                local_values[QX_OFFSET + 12 + i]
            );
            // Qy
            yield_constr.constraint_first_row(
                local_values[Y_MULT_Z_INV_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i] -
                local_values[QY_OFFSET + i]
            );
            yield_constr.constraint_first_row(
                local_values[Y_MULT_Z_INV_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i] -
                local_values[QY_OFFSET + 12 + i]
            );
            if i == 0 {
                yield_constr.constraint_first_row(
                    local_values[QZ_OFFSET + i] - FE::ONE
                );
            } else {
                yield_constr.constraint_first_row(
                    local_values[QZ_OFFSET + i]
                );
            }
            yield_constr.constraint_first_row(
                local_values[QZ_OFFSET + 12 + i]
            );
        }
        for i in 0..24 {
            yield_constr.constraint_transition(local_values[QX_OFFSET + i] - next_values[QX_OFFSET + i]);
            yield_constr.constraint_transition(local_values[QY_OFFSET + i] - next_values[QY_OFFSET + i]);
            yield_constr.constraint_transition(local_values[QZ_OFFSET + i] - next_values[QZ_OFFSET + i]);
        }

        for i in 0..24 {
            yield_constr.constraint(
                local_values[FIRST_LOOP_SELECTOR_OFFSET] * local_values[FIRST_ROW_SELECTOR_OFFSET] *
                (local_values[RX_OFFSET + i] - local_values[QX_OFFSET + i])
            );
            yield_constr.constraint(
                local_values[FIRST_LOOP_SELECTOR_OFFSET] * local_values[FIRST_ROW_SELECTOR_OFFSET] *
                (local_values[RY_OFFSET + i] - local_values[QY_OFFSET + i])
            );
            yield_constr.constraint(
                local_values[FIRST_LOOP_SELECTOR_OFFSET] * local_values[FIRST_ROW_SELECTOR_OFFSET] *
                (local_values[RZ_OFFSET + i] - local_values[QZ_OFFSET + i])
            );
            if i < 12 {
                yield_constr.constraint(
                    (P::ONES - next_values[FIRST_LOOP_SELECTOR_OFFSET]) * next_values[FIRST_ROW_SELECTOR_OFFSET] *
                    (next_values[RX_OFFSET + i] - local_values[NEW_RX_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i])
                );
                yield_constr.constraint(
                    (P::ONES - next_values[FIRST_LOOP_SELECTOR_OFFSET]) * next_values[FIRST_ROW_SELECTOR_OFFSET] *
                    (next_values[RY_OFFSET + i] - local_values[NEW_RY_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i])
                );
                yield_constr.constraint(
                    (P::ONES - next_values[FIRST_LOOP_SELECTOR_OFFSET]) * next_values[FIRST_ROW_SELECTOR_OFFSET] *
                    (next_values[RZ_OFFSET + i] - local_values[NEW_RZ_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i])
                );
            } else {
                yield_constr.constraint(
                    (P::ONES - next_values[FIRST_LOOP_SELECTOR_OFFSET]) * next_values[FIRST_ROW_SELECTOR_OFFSET] *
                    (next_values[RX_OFFSET + i] - local_values[NEW_RX_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i - 12])
                );
                yield_constr.constraint(
                    (P::ONES - next_values[FIRST_LOOP_SELECTOR_OFFSET]) * next_values[FIRST_ROW_SELECTOR_OFFSET] *
                    (next_values[RY_OFFSET + i] - local_values[NEW_RY_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i - 12])
                );
                yield_constr.constraint(
                    (P::ONES - next_values[FIRST_LOOP_SELECTOR_OFFSET]) * next_values[FIRST_ROW_SELECTOR_OFFSET] *
                    (next_values[RZ_OFFSET + i] - local_values[NEW_RZ_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i - 12])
                );
            }
            yield_constr.constraint_transition(
                (P::ONES - next_values[FIRST_ROW_SELECTOR_OFFSET]) *
                (local_values[RX_OFFSET + i] - next_values[RX_OFFSET + i])
            );
            yield_constr.constraint_transition(
                (P::ONES - next_values[FIRST_ROW_SELECTOR_OFFSET]) *
                (local_values[RY_OFFSET + i] - next_values[RY_OFFSET + i])
            );
            yield_constr.constraint_transition(
                (P::ONES - next_values[FIRST_ROW_SELECTOR_OFFSET]) *
                (local_values[RZ_OFFSET + i] - next_values[RZ_OFFSET + i])
            );
        }


        // t0
        for i in 0..24 {
            yield_constr.constraint(
                local_values[T0_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
                (
                local_values[T0_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - 
                local_values[RY_OFFSET + i]
            )
            );
            yield_constr.constraint(
                local_values[T0_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
                (
                local_values[T0_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - 
                local_values[RY_OFFSET + i]
            )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, T0_CALC_OFFSET);


        // T1
        for i in 0..24 {
            yield_constr.constraint(
                local_values[T1_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
                (
                local_values[T1_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - 
                local_values[RZ_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[T1_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
                (
                local_values[T1_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - 
                local_values[RZ_OFFSET + i]
                )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, T1_CALC_OFFSET);


        // X0
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X0_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] *
                (
                local_values[X0_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + i] - 
                local_values[T1_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X0_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] *
                (
                local_values[X0_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + 12 + i] - 
                local_values[T1_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            if i == 0 {
                yield_constr.constraint(
                    local_values[X0_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] *
                (
                    local_values[X0_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET] - 
                    FE::from_canonical_u32(3 as u32)
                )
                );
            } else {
                yield_constr.constraint(
                    local_values[X0_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] *
                    local_values[X0_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i]

                );
            }
        }

        add_fp2_fp_mul_constraints(local_values, next_values, yield_constr, X0_CALC_OFFSET);

        // T2
        for i in 0..12 {
            yield_constr.constraint(
                local_values[T2_CALC_OFFSET + MULTIPLY_B_SELECTOR_OFFSET] * (
                local_values[X0_CALC_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i] -
                local_values[T2_CALC_OFFSET + MULTIPLY_B_X_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[T2_CALC_OFFSET + MULTIPLY_B_SELECTOR_OFFSET] * (
                local_values[X0_CALC_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i] -
                local_values[T2_CALC_OFFSET + MULTIPLY_B_X_OFFSET + i + 12]
                )
            );
            // if i == 0 {
            //     yield_constr.constraint_first_row(
            //         local_values[T2_CALC_OFFSET + MULTIPLY_B_X0_B_MUL_OFFSET + Y_INPUT_OFFSET + i] - 
            //         FE::from_canonical_u32(4 as u32)
            //     );
            // } else {
            //     yield_constr.constraint_first_row(
            //         local_values[T2_CALC_OFFSET + MULTIPLY_B_X0_B_MUL_OFFSET + Y_INPUT_OFFSET + i]
            //     );
            // }
            // if i == 0 {
            //     yield_constr.constraint_first_row(
            //         local_values[T2_CALC_OFFSET + MULTIPLY_B_X1_B_MUL_OFFSET + Y_INPUT_OFFSET + i] - 
            //         FE::from_canonical_u32(4 as u32)
            //     );
            // } else {
            //     yield_constr.constraint_first_row(
            //         local_values[T2_CALC_OFFSET + MULTIPLY_B_X1_B_MUL_OFFSET + Y_INPUT_OFFSET + i]
            //     );
            // }
        }
        add_multiply_by_b_constraints(local_values, next_values, yield_constr, T2_CALC_OFFSET);

        // T3
        for i in 0..12 {
            yield_constr.constraint(
                local_values[T3_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[T3_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + i] - 
                local_values[T2_CALC_OFFSET + MULTIPLY_B_Z0_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[T3_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[T3_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + 12 + i] - 
                local_values[T2_CALC_OFFSET + MULTIPLY_B_Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            if i == 0 {
                yield_constr.constraint(
                    local_values[T3_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[T3_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET] - 
                    FE::from_canonical_u32(3 as u32)
                    )
                );
            } else {
                yield_constr.constraint(
                    local_values[T3_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[T3_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i]
                    )
                );
            }
        }

        add_fp2_fp_mul_constraints(local_values, next_values, yield_constr, T3_CALC_OFFSET);

        // x1
        for i in 0..24 {
            yield_constr.constraint(
                local_values[X1_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X1_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - 
                local_values[RY_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X1_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X1_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - 
                local_values[RZ_OFFSET + i]
                )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, X1_CALC_OFFSET);

        // T4
        for i in 0..12 {
            yield_constr.constraint(
                local_values[T4_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[T4_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + i] - 
                local_values[X1_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[T4_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[T4_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + 12 + i] - 
                local_values[X1_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            if i == 0 {
                yield_constr.constraint(
                    local_values[T4_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[T4_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET] - 
                    FE::from_canonical_u32(2 as u32)
                    )
                );
            } else {
                yield_constr.constraint(
                    local_values[T4_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[T4_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i]
                    )
                );
            }
        }

        add_fp2_fp_mul_constraints(local_values, next_values, yield_constr, T4_CALC_OFFSET);

        // x2
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X2_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[X2_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                    local_values[T2_CALC_OFFSET + MULTIPLY_B_Z0_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X2_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[X2_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                    local_values[T2_CALC_OFFSET + MULTIPLY_B_Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X2_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[X2_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                    local_values[T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X2_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[X2_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                    local_values[T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
        }

        add_subtraction_with_reduction_constranints(local_values, yield_constr, X2_CALC_OFFSET);

        // x3
        for i in 0..24 {
            yield_constr.constraint(
                local_values[X3_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X3_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - 
                local_values[RX_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X3_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X3_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - 
                local_values[RX_OFFSET + i]
                )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, X3_CALC_OFFSET);

        // x4
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X4_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[X4_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + i] - 
                local_values[X3_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X4_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[X4_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + 12 + i] - 
                local_values[X3_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            if i == 0 {
                yield_constr.constraint(
                    local_values[X4_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[X4_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET] - 
                    FE::from_canonical_u32(3 as u32)
                    )
                );
            } else {
                yield_constr.constraint(
                    local_values[X4_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[X4_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i]
                    )
                );
            }
        }

        add_fp2_fp_mul_constraints(local_values, next_values, yield_constr, X4_CALC_OFFSET);

        // x5
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X5_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] *
                (
                    local_values[T4_CALC_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i] -
                    local_values[X5_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X5_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] *
                (
                    local_values[T4_CALC_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i] -
                    local_values[X5_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i]
                )
            );
        }
        add_negate_fp2_constraints(local_values, yield_constr, X5_CALC_OFFSET);
        
        // x6
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X6_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[X6_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                    local_values[T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X6_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[X6_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                    local_values[T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[X6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                    local_values[T3_CALC_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[X6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                    local_values[T3_CALC_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
        }

        add_subtraction_with_reduction_constranints(local_values, yield_constr, X6_CALC_OFFSET);

        // x7
        for i in 0..24 {
            yield_constr.constraint(
                local_values[X7_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X7_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] -
                local_values[RX_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X7_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X7_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] -
                local_values[RY_OFFSET + i]
                )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, X7_CALC_OFFSET);

        // x8
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X8_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                    local_values[X8_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] -
                    local_values[X6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X8_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                    local_values[X8_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i + 12] -
                    local_values[X6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X8_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X8_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] -
                local_values[X7_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X8_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X8_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i + 12] -
                local_values[X7_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, X8_CALC_OFFSET);

        // x9
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X9_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[X9_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                    local_values[T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X9_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[X9_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                    local_values[T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X9_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[X9_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                    local_values[T3_CALC_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X9_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[X9_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                    local_values[T3_CALC_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
        }

        add_addition_with_reduction_constranints(local_values, yield_constr, X9_CALC_OFFSET);

        let k = get_u32_vec_from_literal(mod_inverse(BigUint::from(2 as u32), modulus()));

        // x10
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X10_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[X10_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + i] -
                    local_values[X9_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X10_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[X10_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + 12 + i] -
                    local_values[X9_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X10_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[X10_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] -
                FE::from_canonical_u32(k[i])
                )
            );
        }

        add_fp2_fp_mul_constraints(local_values, next_values, yield_constr, X10_CALC_OFFSET);

        // x11
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X11_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X11_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] -
                local_values[X10_CALC_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X11_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X11_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i + 12] -
                local_values[X10_CALC_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X11_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X11_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] -
                local_values[X10_CALC_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X11_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X11_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i + 12] -
                local_values[X10_CALC_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, X11_CALC_OFFSET);

        // x12
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X12_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X12_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] -
                local_values[T2_CALC_OFFSET + MULTIPLY_B_Z0_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X12_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X12_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i + 12] -
                local_values[T2_CALC_OFFSET + MULTIPLY_B_Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X12_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X12_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] -
                local_values[T2_CALC_OFFSET + MULTIPLY_B_Z0_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X12_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[X12_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i + 12] -
                local_values[T2_CALC_OFFSET + MULTIPLY_B_Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, X12_CALC_OFFSET);

        // X13
        for i in 0..12 {
            yield_constr.constraint(
                local_values[X13_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[X13_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + i] -
                local_values[X12_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[X13_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[X13_CALC_OFFSET + FP2_FP_X_INPUT_OFFSET + 12 + i] -
                local_values[X12_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            if i == 0 {
                yield_constr.constraint(
                    local_values[X13_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[X13_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET] -
                    FE::from_canonical_u32(3 as u32)
                    )
                );
            } else {
                yield_constr.constraint(
                    local_values[X13_CALC_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                    local_values[X13_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i]
                    )
                );
            }
        }

        add_fp2_fp_mul_constraints(local_values, next_values, yield_constr, X13_CALC_OFFSET);

        // new Rx
        for i in 0..12 {
            yield_constr.constraint(
                local_values[NEW_RX_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[NEW_RX_OFFSET + FP2_FP_X_INPUT_OFFSET + i] -
                local_values[X8_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[NEW_RX_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[NEW_RX_OFFSET + FP2_FP_X_INPUT_OFFSET + 12 + i] -
                local_values[X8_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[NEW_RX_OFFSET + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[NEW_RX_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] -
                FE::from_canonical_u32(k[i])
                )
            );
        }

        add_fp2_fp_mul_constraints(local_values, next_values, yield_constr, NEW_RX_OFFSET);

        // new Ry
        for i in 0..12 {
            yield_constr.constraint(
                local_values[NEW_RY_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[NEW_RY_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                    local_values[X11_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[NEW_RY_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[NEW_RY_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                    local_values[X11_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[NEW_RY_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[NEW_RY_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                    local_values[X13_CALC_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[NEW_RY_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[NEW_RY_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                    local_values[X13_CALC_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
        }

        add_subtraction_with_reduction_constranints(local_values, yield_constr, NEW_RY_OFFSET);

        // new Rz
        for i in 0..12 {
            yield_constr.constraint(
                local_values[NEW_RZ_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[NEW_RZ_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] -
                local_values[T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[NEW_RZ_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[NEW_RZ_OFFSET + FP2_FP2_X_INPUT_OFFSET + i + 12] -
                local_values[T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[NEW_RZ_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[NEW_RZ_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] -
                local_values[T4_CALC_OFFSET + X0_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[NEW_RZ_OFFSET + FP2_FP2_SELECTOR_OFFSET] * (
                local_values[NEW_RZ_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i + 12] -
                local_values[T4_CALC_OFFSET + X1_Y_REDUCE_OFFSET + REDUCED_OFFSET + i]
                )
            );
        }

        add_fp2_mul_constraints(local_values, next_values, yield_constr, NEW_RZ_OFFSET);
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
        3
    }
}

#[cfg(test)]
mod tests {
    use super::PUBLIC_INPUTS;
    use crate::calc_pairing_precomp::PairingPrecompStark;
    use plonky2::field::types::Field;
    use plonky2::{
        plonk::config::{GenericConfig, PoseidonGoldilocksConfig},
        util::timing::TimingTree,
    };
    use starky::stark::Stark;
    use starky::util::trace_rows_to_poly_values;
    use starky::{config::StarkConfig, prover::prove, verifier::verify_stark_proof};

    #[test]
    fn test_fp2_mul() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = PairingPrecompStark<F, D>;

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
        let z: [u32; 12] = [
            3621225457, 1284733598, 2592173602, 2778433514, 3415298024, 3512038034, 2556930252,
            2289409521, 759431638, 3707643405, 216427024, 234777573,
        ];
        stark.generate_trace([x, x], [y, y], [z, z]);
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
        assert_eq!(public_inputs.len(), PUBLIC_INPUTS);
        println!("constraint_degree: {:?}", stark.constraint_degree());
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
