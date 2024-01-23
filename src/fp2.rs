use num_bigint::BigUint;
use plonky2::{field::{extension::{Extendable, FieldExtension}, packed::PackedField, types::Field}, hash::hash_types::RichField, iop::ext_target::ExtensionTarget, plonk::circuit_builder::CircuitBuilder};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::{native::{get_u32_vec_from_literal, get_u32_vec_from_literal_24, modulus, Fp, Fp2}, utils::*, fp::*};

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

// Fp2 addition layout offsets
pub const FP2_ADDITION_0_OFFSET: usize = 0;
pub const FP2_ADDITION_1_OFFSET: usize = FP2_ADDITION_0_OFFSET + FP_ADDITION_TOTAL;
pub const FP2_ADDITION_TOTAL: usize = FP2_ADDITION_1_OFFSET + FP_ADDITION_TOTAL;

// Fp2 subtraction layout offsets
pub const FP2_SUBTRACTION_0_OFFSET: usize = 0;
pub const FP2_SUBTRACTION_1_OFFSET: usize = FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_TOTAL;
pub const FP2_SUBTRACTION_TOTAL: usize = FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_TOTAL;

// Fp2 multiply single
pub const FP2_MULTIPLY_SINGLE_0_OFFSET: usize = 0;
pub const FP2_MULTIPLY_SINGLE_1_OFFSET: usize = FP2_MULTIPLY_SINGLE_0_OFFSET + FP_MULTIPLY_SINGLE_TOTAL;
pub const FP2_MULTIPLY_SINGLE_TOTAL: usize = FP2_MULTIPLY_SINGLE_1_OFFSET + FP_MULTIPLY_SINGLE_TOTAL;

// FP2 non residue multiplication
pub const FP2_NON_RESIDUE_MUL_CHECK_OFFSET: usize = 0;
pub const FP2_NON_RESIDUE_MUL_INPUT_OFFSET: usize = FP2_NON_RESIDUE_MUL_CHECK_OFFSET + 1;
pub const FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET: usize = FP2_NON_RESIDUE_MUL_INPUT_OFFSET + 24;
pub const FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET: usize = FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_TOTAL;
pub const FP2_NON_RESIDUE_MUL_Z0_RANGECHECK_OFFSET: usize = FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCE_TOTAL;
pub const FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET: usize = FP2_NON_RESIDUE_MUL_Z0_RANGECHECK_OFFSET + RANGE_CHECK_TOTAL;
pub const FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET: usize = FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_TOTAL;
pub const FP2_NON_RESIDUE_MUL_Z1_RANGECHECK_OFFSET: usize = FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCE_TOTAL;
pub const FP2_NON_RESIDUE_MUL_TOTAL: usize = FP2_NON_RESIDUE_MUL_Z1_RANGECHECK_OFFSET + RANGE_CHECK_TOTAL;

pub fn fill_trace_addition_fp2<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(
    trace: &mut Vec<[F; C]>,
    x: &[[u32; 12]; 2],
    y: &[[u32; 12]; 2],
    row: usize,
    start_col: usize,
) {
    fill_trace_addition_fp(trace, &x[0], &y[0], row, start_col + FP2_ADDITION_0_OFFSET);
    fill_trace_addition_fp(trace, &x[1], &y[1], row, start_col + FP2_ADDITION_1_OFFSET);
}

pub fn fill_trace_subtraction_fp2<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(
    trace: &mut Vec<[F; C]>,
    x: &[[u32; 12]; 2],
    y: &[[u32; 12]; 2],
    row: usize,
    start_col: usize,
) {
    fill_trace_subtraction_fp(trace, &x[0], &y[0], row, start_col + FP2_SUBTRACTION_0_OFFSET);
    fill_trace_subtraction_fp(trace, &x[1], &y[1], row, start_col + FP2_SUBTRACTION_1_OFFSET);
}

pub fn fill_trace_multiply_single_fp2<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(
    trace: &mut Vec<[F; C]>,
    x: &[[u32; 12]; 2],
    y: &[u32; 2],
    row: usize,
    start_col: usize,
) {
    fill_trace_multiply_single_fp(trace, &x[0], y[0], row, start_col + FP2_SUBTRACTION_0_OFFSET);
    fill_trace_multiply_single_fp(trace, &x[1], y[1], row, start_col + FP2_SUBTRACTION_1_OFFSET);
}

pub fn fill_trace_negate_fp2<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(
    trace: &mut Vec<[F; C]>,
    x: &[[u32; 12]; 2],
    row: usize,
    start_col: usize
) {
    let minus_x: [[u32; 12]; 2] = (-Fp2([Fp(x[0].to_owned()), Fp(x[1].to_owned())])).0.iter().map(|x| x.0).collect::<Vec<[u32; 12]>>().try_into().unwrap();
    fill_trace_addition_fp2(trace, x, &minus_x, row, start_col);
}

pub fn generate_trace_fp2_mul<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(trace: &mut Vec<[F; C]>, x: [[u32; 12]; 2], y: [[u32; 12]; 2], start_row: usize, end_row: usize,start_col: usize) {
    let modulus = modulus();

    for i in start_row..end_row+1 {
        trace[i][start_col + FP2_FP2_SELECTOR_OFFSET] = F::ONE;
        assign_u32_in_series(trace, i, start_col + FP2_FP2_X_INPUT_OFFSET, &x[0]);
        assign_u32_in_series(trace, i, start_col + FP2_FP2_X_INPUT_OFFSET+12, &x[1]);
        assign_u32_in_series(trace, i, start_col + FP2_FP2_Y_INPUT_OFFSET, &y[0]);
        assign_u32_in_series(trace, i, start_col + FP2_FP2_Y_INPUT_OFFSET+12, &y[1]);
    }
    trace[end_row][start_col + FP2_FP2_SELECTOR_OFFSET] = F::ZERO;
    // filling trace for X0*Y0 - X1*Y1
    fill_multiplication_trace_no_mod_reduction(trace, 
        &x[0],
        &y[0],
        start_row,
        end_row,
        start_col + X_0_Y_0_MULTIPLICATION_OFFSET,
    );
    fill_multiplication_trace_no_mod_reduction(trace, 
        &x[1],
        &y[1],
        start_row,
        end_row,
        start_col + X_1_Y_1_MULTIPLICATION_OFFSET,
    );

    let x0y0 =
        get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y[0].to_vec()));
    let modulus_sq = get_u32_vec_from_literal_24(modulus.clone() * modulus.clone());
    fill_addition_trace(trace, &x0y0, &modulus_sq, start_row + 11, start_col + Z1_ADD_MODULUS_OFFSET);

    let x0y0_add_modsq =
        get_u32_vec_from_literal_24(BigUint::new(x0y0.to_vec()) + modulus.clone() * modulus);
    let x1y1 =
        get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y[1].to_vec()));
    fill_subtraction_trace(trace, &x0y0_add_modsq, &x1y1, start_row + 11, start_col + Z1_SUBTRACTION_OFFSET);

    let x0y0_x1y1 = get_u32_vec_from_literal_24(
        BigUint::new(x0y0_add_modsq.to_vec()) - BigUint::new(x1y1.to_vec()),
    );
    let rem = fill_reduction_trace(trace, &x0y0_x1y1, start_row, end_row, start_col + Z1_REDUCE_OFFSET);
    fill_range_check_trace(trace, &rem, start_row, start_col + Z1_RANGECHECK_OFFSET);

    // filling trace for X0*Y1 + X1*Y0
    fill_multiplication_trace_no_mod_reduction(trace, 
        &x[0],
        &y[1],
        start_row,
        end_row,
        start_col + X_0_Y_1_MULTIPLICATION_OFFSET,
    );
    fill_multiplication_trace_no_mod_reduction(trace, 
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
    fill_addition_trace(trace, &x0y1, &x1y0, start_row + 11, start_col + Z2_ADDITION_OFFSET);

    let x0y1_x1y0 =
        get_u32_vec_from_literal_24(BigUint::new(x0y1.to_vec()) + BigUint::new(x1y0.to_vec()));
    let rem = fill_reduction_trace(trace, &x0y1_x1y0, start_row, end_row, start_col + Z2_REDUCE_OFFSET);
    fill_range_check_trace(trace, &rem, start_row, start_col + Z2_RANGECHECK_OFFSET);
}

pub fn fill_trace_fp2_fp_mul<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(trace: &mut Vec<[F; C]>, x: &[[u32; 12]; 2], y: &[u32; 12], start_row: usize, end_row: usize, start_col: usize) {
    for i in start_row..end_row + 1 {
        trace[i][start_col + FP2_FP_MUL_SELECTOR_OFFSET] = F::ONE;
        assign_u32_in_series(trace, i, start_col + FP2_FP_X_INPUT_OFFSET, &x[0]);
        assign_u32_in_series(trace, i, start_col + FP2_FP_X_INPUT_OFFSET + 12, &x[1]);
        assign_u32_in_series(trace, i, start_col + FP2_FP_Y_INPUT_OFFSET, y);
    }
    trace[end_row][start_col + FP2_FP_MUL_SELECTOR_OFFSET] = F::ZERO;
    fill_multiplication_trace_no_mod_reduction(trace, &x[0], y, start_row, end_row, start_col + X0_Y_MULTIPLICATION_OFFSET);
    let x0y = get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y.to_vec()));
    let rem = fill_reduction_trace(trace, &x0y, start_row, end_row, start_col + X0_Y_REDUCE_OFFSET);
    fill_range_check_trace(trace, &rem, start_row, start_col + X0_Y_RANGECHECK_OFFSET);
    fill_multiplication_trace_no_mod_reduction(trace, &x[1], y, start_row, end_row, start_col + X1_Y_MULTIPLICATION_OFFSET);
    let x1y = get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y.to_vec()));
    let rem = fill_reduction_trace(trace, &x1y, start_row, end_row, start_col + X1_Y_REDUCE_OFFSET);
    fill_range_check_trace(trace, &rem, start_row, start_col + X1_Y_RANGECHECK_OFFSET);
}

pub fn fill_trace_subtraction_with_reduction<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(trace: &mut Vec<[F; C]>, x: &[[u32; 12]; 2], y: &[[u32; 12]; 2], row: usize, start_col: usize) {
    let modulus = get_u32_vec_from_literal(modulus());
    fill_trace_addition_fp2(trace, x, &[modulus, modulus], row, start_col);
    let x0_modulus = get_u32_vec_from_literal(
        BigUint::new(x[0].to_vec()) + BigUint::new(modulus.to_vec())
    );
    let x1_modulus = get_u32_vec_from_literal(
        BigUint::new(x[1].to_vec()) + BigUint::new(modulus.to_vec())
    );
    fill_trace_subtraction_fp2(trace, &[x0_modulus, x1_modulus], y, row, start_col + FP2_ADDITION_TOTAL);
    let x0_y0 = get_u32_vec_from_literal(
        BigUint::new(x0_modulus.to_vec()) - BigUint::new(y[0].to_vec())
    );
    let x1_y1 = get_u32_vec_from_literal(
        BigUint::new(x1_modulus.to_vec()) - BigUint::new(y[1].to_vec())
    );
    let rem = fill_trace_reduce_single(trace, &x0_y0, row, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL);
    fill_range_check_trace(trace, &rem, row, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL);
    let rem = fill_trace_reduce_single(trace, &x1_y1, row, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL);
    fill_range_check_trace(trace, &rem, row, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL);
}

pub fn fill_multiply_by_b_trace<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(trace: &mut Vec<[F; C]>, x: &[[u32; 12]; 2], start_row: usize, end_row: usize, start_col: usize) {
    for i in start_row..end_row + 1 {
        trace[i][start_col + MULTIPLY_B_SELECTOR_OFFSET] = F::ONE;
        assign_u32_in_series(trace, i, start_col + MULTIPLY_B_X_OFFSET, &x[0]);
        assign_u32_in_series(trace, i, start_col + MULTIPLY_B_X_OFFSET + 12, &x[1]);
    }
    trace[end_row][start_col + MULTIPLY_B_SELECTOR_OFFSET] = F::ZERO;
    let y = Fp::get_fp_from_biguint(BigUint::from(4 as u32)).0;
    fill_multiplication_trace_no_mod_reduction(trace, &x[0], &y, start_row, end_row, start_col + MULTIPLY_B_X0_B_MUL_OFFSET);
    fill_multiplication_trace_no_mod_reduction(trace, &x[1], &y, start_row, end_row, start_col + MULTIPLY_B_X1_B_MUL_OFFSET);
    let x0y = get_u32_vec_from_literal_24(BigUint::new(x[0].to_vec()) * BigUint::new(y.to_vec()));
    let x1y = get_u32_vec_from_literal_24(BigUint::new(x[1].to_vec()) * BigUint::new(y.to_vec()));
    let modulus = modulus();
    let modulus_sq = get_u32_vec_from_literal_24(modulus.clone() * modulus.clone());
    fill_addition_trace(trace, &x0y, &modulus_sq, start_row + 11, start_col + MULTIPLY_B_ADD_MODSQ_OFFSET);
    let x0y_add_modsq =
        get_u32_vec_from_literal_24(BigUint::new(x0y.to_vec()) + BigUint::new(modulus_sq.to_vec()));
    fill_subtraction_trace(trace, &x0y_add_modsq, &x1y, start_row + 11, start_col + MULTIPLY_B_SUB_OFFSET);
    let x0y_x1y = get_u32_vec_from_literal_24(
        BigUint::new(x0y_add_modsq.to_vec()) - BigUint::new(x1y.to_vec()),
    );
    let rem = fill_reduction_trace(trace, &x0y_x1y, start_row, end_row, start_col + MULTIPLY_B_Z0_REDUCE_OFFSET);
    fill_range_check_trace(trace, &rem, start_row, start_col + MULTIPLY_B_Z0_RANGECHECK_OFFSET);


    fill_addition_trace(trace, &x0y, &x1y, start_row + 11, start_col + MULTIPLY_B_ADD_OFFSET);
    let x0y_x1y = get_u32_vec_from_literal_24(
        BigUint::new(x0y.to_vec()) + BigUint::new(x1y.to_vec()),
    );
    let rem = fill_reduction_trace(trace, &x0y_x1y, start_row, end_row, start_col + MULTIPLY_B_Z1_REDUCE_OFFSET);
    fill_range_check_trace(trace, &rem, start_row, start_col + MULTIPLY_B_Z1_RANGECHECK_OFFSET);
}

pub fn fill_trace_addition_with_reduction<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(trace: &mut Vec<[F; C]>, x: &[[u32; 12]; 2], y: &[[u32; 12]; 2], row: usize, start_col: usize) {
    fill_trace_addition_fp2(trace, x, y, row, start_col);
    let x0_y0 = get_u32_vec_from_literal(
        BigUint::new(x[0].to_vec()) + BigUint::new(y[0].to_vec())
    );
    let x1_y1 = get_u32_vec_from_literal(
        BigUint::new(x[1].to_vec()) + BigUint::new(y[1].to_vec())
    );
    let rem = fill_trace_reduce_single(trace, &x0_y0, row, start_col + FP2_ADDITION_TOTAL);
    fill_range_check_trace(trace, &rem, row, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL);
    let rem = fill_trace_reduce_single(trace, &x1_y1, row, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL);
    fill_range_check_trace(trace, &rem, row, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL);
}

pub fn fill_trace_non_residue_multiplication<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(trace: &mut Vec<[F; C]>, x: &[[u32; 12]; 2], row: usize, start_col: usize) {
    trace[row][start_col + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] = F::ONE;
    assign_u32_in_series(trace, row, start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET, &x.concat());
    fill_trace_addition_fp(trace, &x[0], &get_u32_vec_from_literal(modulus()), row, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET);
    let add_modulus = get_u32_vec_from_literal(
        BigUint::new(x[0].to_vec()) + modulus()
    );
    fill_trace_subtraction_fp(trace, &add_modulus, &x[1], row, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL);
    let c0_c1_sub = get_u32_vec_from_literal(
        BigUint::new(add_modulus.to_vec()) - BigUint::new(x[1].to_vec())
    );
    let rem = fill_trace_reduce_single(trace, &c0_c1_sub, row, start_col + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET);
    fill_range_check_trace(trace, &rem, row, start_col + FP2_NON_RESIDUE_MUL_Z0_RANGECHECK_OFFSET);
    fill_trace_addition_fp(trace, &x[0], &x[1], row, start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET);
    let c0_c1_add = get_u32_vec_from_literal(
        BigUint::new(x[0].to_vec()) + BigUint::new(x[1].to_vec())
    );
    let rem = fill_trace_reduce_single(trace, &c0_c1_add, row, start_col + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET);
    fill_range_check_trace(trace, &rem, row, start_col + FP2_NON_RESIDUE_MUL_Z1_RANGECHECK_OFFSET);
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
    bit_selector: Option<P>,
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    add_addition_fp_constraints(local_values, yield_constr, start_col + FP2_ADDITION_0_OFFSET, bit_selector);
    add_addition_fp_constraints(local_values, yield_constr, start_col + FP2_ADDITION_1_OFFSET, bit_selector);
}

pub fn add_addition_fp2_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    add_addition_fp_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_0_OFFSET, bit_selector);
    add_addition_fp_constraints_ext_circuit(builder, yield_constr, local_values,start_col + FP2_ADDITION_1_OFFSET, bit_selector);
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
    bit_selector: Option<P>,
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    add_subtraction_fp_constraints(local_values, yield_constr, start_col + FP2_SUBTRACTION_0_OFFSET, bit_selector);
    add_subtraction_fp_constraints(local_values, yield_constr, start_col + FP2_SUBTRACTION_1_OFFSET, bit_selector);
}

pub fn add_subtraction_fp2_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    add_subtraction_fp_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_SUBTRACTION_0_OFFSET, bit_selector);
    add_subtraction_fp_constraints_ext_circuit(builder, yield_constr, local_values,start_col + FP2_SUBTRACTION_1_OFFSET, bit_selector);
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
    bit_selector: Option<P>,
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    add_fp_single_multiply_constraints(local_values, yield_constr, start_col + FP2_MULTIPLY_SINGLE_0_OFFSET, bit_selector);
    add_fp_single_multiply_constraints(local_values, yield_constr, start_col + FP2_MULTIPLY_SINGLE_1_OFFSET, bit_selector);
}

pub fn add_fp2_single_multiply_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    add_fp_single_multiply_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_MULTIPLY_SINGLE_0_OFFSET, bit_selector);
    add_fp_single_multiply_constraints_ext_circuit(builder, yield_constr, local_values,start_col + FP2_MULTIPLY_SINGLE_1_OFFSET, bit_selector);
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
    bit_selector: Option<P>,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    add_addition_fp2_constraints(local_values, yield_constr, start_col, bit_selector);
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    let mod_u32 = get_u32_vec_from_literal(modulus());
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i] - FE::from_canonical_u32(mod_u32[i])
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i] - FE::from_canonical_u32(mod_u32[i])
            )
        );
    }
}

pub fn add_negate_fp2_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));

    add_addition_fp2_constraints_ext_circuit(builder, yield_constr, local_values, start_col, bit_selector);
    let mod_u32 = get_u32_vec_from_literal(modulus());
    for i in 0..12 {

        let lc = builder.constant_extension(F::Extension::from_canonical_u32(mod_u32[i]));

        let mul_tmp1 = builder.mul_extension(bit_selector_val , local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] );
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i] , lc );

        let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c1);

        let mul_tmp2 = builder.mul_extension(bit_selector_val , local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET]);
        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i],lc);
        
        let c2 = builder.mul_extension(mul_tmp2, sub_tmp2);
        yield_constr.constraint(builder, c2);

    }
}   

pub fn add_fp2_mul_constraints<
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
    bit_selector: Option<P>,
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    // for i in 0..12 {
    //     yield_constr.constraint_transition(local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i])
    // }
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    for i in 0..24 {
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i] - next_values[start_col + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i] - next_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i])
        );
    }

    for i in 0..12 {
        yield_constr.constraint(bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(bit_selector_val *
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
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
        bit_selector,
    );


    // constrain X_1*Y_1
    add_multiplication_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + X_1_Y_1_MULTIPLICATION_OFFSET,
        bit_selector,
    );

    // constrain X0*Y0 with X0*Y0 + modulus^2
    for i in 0..24 {
        yield_constr.constraint_transition(bit_selector_val *
            local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_X_OFFSET + i]
                    - local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
        );
    }

    // constrain modulus^2 with X0*Y0 + modulus^2
    let modulus = modulus();
    let modulus_sq_u32 = get_u32_vec_from_literal_24(modulus.clone() * modulus);
    for i in 0..24 {
        yield_constr.constraint_transition(bit_selector_val *
            local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_Y_OFFSET + i]
                    - FE::from_canonical_u32(modulus_sq_u32[i])),
        );
    }

    // constrain X0*Y0 + modulus^2
    add_addition_constraints(local_values, yield_constr, start_col + Z1_ADD_MODULUS_OFFSET, bit_selector);

    // constrain X0*Y0 + modulus^2 with X0*Y0 + modulus^2 - X1Y1
    for i in 0..24 {
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]
                * (local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_X_OFFSET + i]
                    - local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_SUM_OFFSET + i]),
        );
    }

    // constrain X1*Y1 + modulus^2 with X0*Y0 + modulus^2 - X1Y1
    for i in 0..24 {
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]
                * (local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_Y_OFFSET + i]
                    - local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
        );
    }

    // constrain X0*Y0 + modulus^2 - X1Y1
    add_subtraction_constraints(local_values, yield_constr, start_col + Z1_SUBTRACTION_OFFSET, bit_selector);

    // constrain X0*Y0 + modulus^2 - X1Y1 with reduction
    for i in 0..24 {
        yield_constr.constraint_transition(
            bit_selector_val *
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
        bit_selector,
    );
    add_range_check_constraints(local_values, yield_constr, start_col + Z1_RANGECHECK_OFFSET, bit_selector);



    // constrain X_1*Y_0
    add_multiplication_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + X_0_Y_1_MULTIPLICATION_OFFSET,
        bit_selector,
    );



    // constrain X_1*Y_0
    add_multiplication_constraints(
        local_values,
        next_values,
        yield_constr,
        start_col + X_1_Y_0_MULTIPLICATION_OFFSET,
        bit_selector,
    );

    // constrain X0*Y1 with X0*Y1 + X1*Y0
    for i in 0..24 {
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_X_OFFSET + i]
                    - local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
        );
    }

    // constrain X1*Y0 with X0*Y1 + X1*Y0
    for i in 0..24 {
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]
                * (local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_Y_OFFSET + i]
                    - local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + SUM_OFFSET + i]),
        );
    }

    // constrain X0*Y1 + X1*Y0
    add_addition_constraints(local_values, yield_constr, start_col + Z2_ADDITION_OFFSET, bit_selector);

    // constrain X0*Y1 + X1*Y0 with reduction
    for i in 0..24 {
        yield_constr.constraint_transition(
            bit_selector_val *
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
        bit_selector,
    );
    add_range_check_constraints(local_values, yield_constr, start_col + Z2_RANGECHECK_OFFSET, bit_selector);
}

pub fn add_fp2_mul_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    next_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    // let constant = builder.constant_extension(F::Extension::from_canonical_u64(1<<32));
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_FP2_SELECTOR_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i] , next_values[start_col + FP2_FP2_X_INPUT_OFFSET + i]);

        let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c1);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i] , next_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i]);

        let c2 = builder.mul_extension(mul_tmp1, sub_tmp2);
        yield_constr.constraint_transition(builder, c2);

    }

    for i in 0..12 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_FP2_SELECTOR_OFFSET]);
        
        let sub_tmp1 = builder.sub_extension(local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] , local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i]);
        let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c1);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] , local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i]);
        let c2 = builder.mul_extension(mul_tmp1, sub_tmp2);
        yield_constr.constraint(builder, c2);

        let sub_tmp3 = builder.sub_extension(local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] , local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i]);
        let c3 = builder.mul_extension(mul_tmp1,sub_tmp3);
        yield_constr.constraint(builder, c3);

        let sub_tmp4 = builder.sub_extension(local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] , local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i + 12]);
        let c4 = builder.mul_extension(mul_tmp1, sub_tmp4);
        yield_constr.constraint(builder,c4);

        let sub_tmp5 = builder.sub_extension(local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] ,local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i + 12]);
        let c5 = builder.mul_extension(mul_tmp1, sub_tmp5);
        yield_constr.constraint(builder, c5);

        let sub_tmp6 = builder.sub_extension(local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] , local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i]);
        let c6 = builder.mul_extension(mul_tmp1, sub_tmp6);
        yield_constr.constraint(builder, c6);

        let sub_tmp7 = builder.sub_extension(local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] , local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i + 12]);
        let c7 = builder.mul_extension(mul_tmp1, sub_tmp7);
        yield_constr.constraint(builder,c7);

        let sub_tmp8 = builder.sub_extension(local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] , local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i + 12]);
        let c8 = builder.mul_extension(mul_tmp1, sub_tmp8);
        yield_constr.constraint(builder, c8);    
    }

    add_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + X_0_Y_0_MULTIPLICATION_OFFSET, bit_selector);
    add_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + X_1_Y_1_MULTIPLICATION_OFFSET, bit_selector);


    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_X_OFFSET + i], local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + SUM_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }

    let modulus = modulus();
    let modulus_sq_u32 = get_u32_vec_from_literal_24(modulus.clone() * modulus);
    for i in 0..24 {
        let lc = builder.constant_extension(F::Extension::from_canonical_u32(modulus_sq_u32[i]));

        let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_Y_OFFSET + i], lc);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }

    add_addition_constraints_ext_circuit(builder, yield_constr, local_values, start_col + Z1_ADD_MODULUS_OFFSET, bit_selector);

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_X_OFFSET + i], local_values[start_col + Z1_ADD_MODULUS_OFFSET + ADDITION_SUM_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val,  local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_Y_OFFSET + i], local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + SUM_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }
    
    add_subtraction_constraints_ext_circuit(builder, yield_constr, local_values, start_col + Z1_SUBTRACTION_OFFSET, bit_selector);

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val , local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + Z1_SUBTRACTION_OFFSET + SUBTRACTION_DIFF_OFFSET + i], local_values[start_col + Z1_REDUCE_OFFSET + REDUCE_X_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }
    
    add_reduce_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + Z1_REDUCE_OFFSET, start_col + FP2_FP2_SELECTOR_OFFSET ,bit_selector);

    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + Z1_RANGECHECK_OFFSET, bit_selector);

    add_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + X_0_Y_1_MULTIPLICATION_OFFSET, bit_selector);

    add_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + X_1_Y_0_MULTIPLICATION_OFFSET, bit_selector);

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_X_OFFSET + i], local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + SUM_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_Y_OFFSET + i], local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + SUM_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }

    add_addition_constraints_ext_circuit(builder, yield_constr, local_values, start_col + Z2_ADDITION_OFFSET, bit_selector);

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val , local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + Z2_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i], local_values[start_col + Z2_REDUCE_OFFSET + REDUCE_X_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }

    
    add_reduce_constraints_ext_circuit(builder, yield_constr, local_values, next_values,start_col + Z2_REDUCE_OFFSET,start_col + FP2_FP2_SELECTOR_OFFSET,bit_selector);

    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + Z2_RANGECHECK_OFFSET, bit_selector);

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
    bit_selector: Option<P>,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    for i in 0..12 {
        for j in 0..2 {
            yield_constr.constraint_transition(
                bit_selector_val *
                local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] *
                (local_values[start_col + FP2_FP_X_INPUT_OFFSET + j*12 + i] - next_values[start_col + FP2_FP_X_INPUT_OFFSET + j*12 + i])
            );
        }
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP2_FP_Y_INPUT_OFFSET + i] - next_values[start_col + FP2_FP_Y_INPUT_OFFSET + i])
        );
    }
    // constrain inputs to multiplication
    for i in 0..12 {
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[start_col + FP2_FP_X_INPUT_OFFSET + i] - local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[start_col + FP2_FP_X_INPUT_OFFSET + 12 + i] - local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[start_col + FP2_FP_Y_INPUT_OFFSET + i] - local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET] * (
                local_values[start_col + FP2_FP_Y_INPUT_OFFSET + i] - local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]
            )
        );
    }
    add_multiplication_constraints(local_values, next_values, yield_constr, start_col + X0_Y_MULTIPLICATION_OFFSET, bit_selector);
    for i in 0..24 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + X0_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + X0_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i] -
                local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + SUM_OFFSET + i]
            )
        );
    }
    add_reduce_constraints(local_values, next_values, yield_constr, start_col + X0_Y_REDUCE_OFFSET, start_col + FP2_FP_MUL_SELECTOR_OFFSET, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + X0_Y_RANGECHECK_OFFSET, bit_selector);
    add_multiplication_constraints(local_values, next_values, yield_constr, start_col + X1_Y_MULTIPLICATION_OFFSET, bit_selector);
    for i in 0..24 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + X1_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + X1_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i] -
                local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + SUM_OFFSET + i]
            )
        );
    }
    add_reduce_constraints(local_values, next_values, yield_constr, start_col + X1_Y_REDUCE_OFFSET, start_col + FP2_FP_MUL_SELECTOR_OFFSET, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + X1_Y_RANGECHECK_OFFSET, bit_selector);
}

pub fn add_fp2_fp_mul_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    next_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));
    
    for i in 0..12 {
        for j in 0..2 {
            let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET]);
            let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_FP_X_INPUT_OFFSET + j*12 + i] , next_values[start_col + FP2_FP_X_INPUT_OFFSET + j*12 + i]);

            let c = builder.mul_extension(mul_tmp1, sub_tmp1);
            yield_constr.constraint_transition(builder, c);
        }
        let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_FP_Y_INPUT_OFFSET + i] , next_values[start_col + FP2_FP_Y_INPUT_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
        
    }

    for i in 0..12 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_FP_MUL_SELECTOR_OFFSET]);

        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_FP_X_INPUT_OFFSET + i] , local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i]);
        let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c1);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP2_FP_X_INPUT_OFFSET + 12 + i] , local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i]);
        let c2 = builder.mul_extension(mul_tmp1, sub_tmp2);
        yield_constr.constraint_transition(builder, c2);

        let sub_tmp3 = builder.sub_extension(local_values[start_col + FP2_FP_Y_INPUT_OFFSET + i] , local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]);
        let c3 = builder.mul_extension(mul_tmp1, sub_tmp3);
        yield_constr.constraint_transition(builder,c3);

        let sub_tmp4 = builder.sub_extension(local_values[start_col + FP2_FP_Y_INPUT_OFFSET + i] , local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i]);
        let c4 = builder.mul_extension(mul_tmp1, sub_tmp4);
        yield_constr.constraint_transition(builder, c4);
    }

    add_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + X0_Y_MULTIPLICATION_OFFSET, bit_selector);
    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val , local_values[start_col + X0_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + X0_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i], local_values[start_col + X0_Y_MULTIPLICATION_OFFSET + SUM_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c);
    }

    add_reduce_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col+ X0_Y_REDUCE_OFFSET, start_col + FP2_FP_MUL_SELECTOR_OFFSET,bit_selector);
    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + X0_Y_RANGECHECK_OFFSET, bit_selector);
    add_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + X1_Y_MULTIPLICATION_OFFSET, bit_selector);

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + X1_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + X1_Y_REDUCE_OFFSET + REDUCTION_ADDITION_OFFSET + ADDITION_SUM_OFFSET + i], local_values[start_col + X1_Y_MULTIPLICATION_OFFSET + SUM_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c);
    }

    add_reduce_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + X1_Y_REDUCE_OFFSET, start_col + FP2_FP_MUL_SELECTOR_OFFSET, bit_selector);
    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + X1_Y_RANGECHECK_OFFSET, bit_selector);
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
    bit_selector: Option<P>,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    for i in 0..24 {
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_B_X_OFFSET + i] - next_values[start_col + MULTIPLY_B_X_OFFSET + i])
        );
    }
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * (
                local_values[start_col + MULTIPLY_B_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + X_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * (
                local_values[start_col + MULTIPLY_B_X_OFFSET + 12 + i] - local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + X_INPUT_OFFSET + i]
            )
        );
        if i == 0 {
            yield_constr.constraint(
                bit_selector_val *
                local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * (
                    local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + Y_INPUT_OFFSET + i] - FE::from_canonical_u32(4)
                )
            );
            yield_constr.constraint(
                bit_selector_val *
                local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * (
                    local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + Y_INPUT_OFFSET + i] - FE::from_canonical_u32(4)
                )
            );
        } else {
            yield_constr.constraint(
                bit_selector_val *
                local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + Y_INPUT_OFFSET + i]
            );
            yield_constr.constraint(
                bit_selector_val *
                local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET] * local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + Y_INPUT_OFFSET + i]
            );
        }
    }
    add_multiplication_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_B_X0_B_MUL_OFFSET, bit_selector);
    add_multiplication_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_B_X1_B_MUL_OFFSET, bit_selector);
    let modulus = modulus();
    let modulus_sq_u32 = get_u32_vec_from_literal_24(modulus.clone() * modulus);
    for i in 0..24 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_Y_OFFSET + i] - FE::from_canonical_u32(modulus_sq_u32[i])
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_Y_OFFSET + i] - local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_Y_OFFSET + i] - local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + SUM_OFFSET + i]
            )
        );
    }
    add_addition_constraints(local_values, yield_constr, start_col + MULTIPLY_B_ADD_MODSQ_OFFSET, bit_selector);
    add_subtraction_constraints(local_values, yield_constr, start_col + MULTIPLY_B_SUB_OFFSET, bit_selector);
    add_addition_constraints(local_values, yield_constr, start_col + MULTIPLY_B_ADD_OFFSET, bit_selector);
    for i in 0..24 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_Z0_REDUCE_OFFSET + REDUCE_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_DIFF_OFFSET + i]
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_B_Z1_REDUCE_OFFSET + REDUCE_X_OFFSET + i] - local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_SUM_OFFSET + i]
            )
        );
    }
    add_reduce_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_B_Z0_REDUCE_OFFSET, start_col + MULTIPLY_B_SELECTOR_OFFSET, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + MULTIPLY_B_Z0_RANGECHECK_OFFSET, bit_selector);
    add_reduce_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_B_Z1_REDUCE_OFFSET, start_col + MULTIPLY_B_SELECTOR_OFFSET, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + MULTIPLY_B_Z1_RANGECHECK_OFFSET, bit_selector);
}

pub fn add_multiply_by_b_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    next_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    let constant = builder.constant_extension(F::Extension::from_canonical_u32(4));
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));

    for i in 0..24 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_B_X_OFFSET + i] , next_values[start_col + MULTIPLY_B_X_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint_transition(builder, c);
    }
    
    for i in 0..12 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET]);

        let sub_tmp1 = builder.sub_extension( local_values[start_col + MULTIPLY_B_X_OFFSET + i] , local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + X_INPUT_OFFSET + i]);
        let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c1);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_B_X_OFFSET + 12 + i] , local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + X_INPUT_OFFSET + i]);
        let c2 = builder.mul_extension(mul_tmp1, sub_tmp2);
        yield_constr.constraint(builder, c2);

        if i == 0 {
            let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET]);
            
            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + Y_INPUT_OFFSET + i] , constant);
            let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
            yield_constr.constraint(builder, c1);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + Y_INPUT_OFFSET + i], constant);
            let c2 = builder.mul_extension(mul_tmp1,sub_tmp2);
            yield_constr.constraint(builder, c2);
            
        }else {
            let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + MULTIPLY_B_SELECTOR_OFFSET]);

            let c1 = builder.mul_extension(mul_tmp1, local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + Y_INPUT_OFFSET + i]);
            yield_constr.constraint(builder, c1);

            let c2 = builder.mul_extension(mul_tmp1,local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + Y_INPUT_OFFSET + i]);
            yield_constr.constraint(builder, c2);
        }
    }

        add_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + MULTIPLY_B_X0_B_MUL_OFFSET, bit_selector);
        add_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col  + MULTIPLY_B_X1_B_MUL_OFFSET, bit_selector);
        let modulus = modulus();
        let modulus_sq_u32 = get_u32_vec_from_literal_24(modulus.clone() * modulus);
        for i in 0..24 {

            let lc = builder.constant_extension(F::Extension::from_canonical_u32(modulus_sq_u32[i]));

            let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_CHECK_OFFSET]);

            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_X_OFFSET + i] , local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + SUM_OFFSET + i]);
            let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
            yield_constr.constraint(builder, c1);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_Y_OFFSET + i], lc);
            let c2 = builder.mul_extension(mul_tmp1, sub_tmp2);
            yield_constr.constraint(builder, c2);

            let mul_tmp2 = builder.mul_extension(bit_selector_val , local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_CHECK_OFFSET]);

            let sub_tmp3 = builder.sub_extension(local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_X_OFFSET + i] , local_values[start_col + MULTIPLY_B_ADD_MODSQ_OFFSET + ADDITION_SUM_OFFSET + i]);
            let c3 = builder.mul_extension(mul_tmp2, sub_tmp3);
            yield_constr.constraint(builder, c3);

            let sub_tmp4 = builder.sub_extension(local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_Y_OFFSET + i] , local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + SUM_OFFSET + i]);
            let c4 = builder.mul_extension(mul_tmp2, sub_tmp4);
            yield_constr.constraint(builder, c4);

            let mul_tmp3 = builder.mul_extension(bit_selector_val, local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_CHECK_OFFSET]);

            let sub_tmp5 = builder.sub_extension(local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_X_OFFSET + i], local_values[start_col + MULTIPLY_B_X0_B_MUL_OFFSET + SUM_OFFSET + i]);
            let c5 = builder.mul_extension(mul_tmp3, sub_tmp5);
            yield_constr.constraint(builder, c5);

            let sub_tmp6 = builder.sub_extension(local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_Y_OFFSET + i] , local_values[start_col + MULTIPLY_B_X1_B_MUL_OFFSET + SUM_OFFSET + i]);
            let c6 = builder.mul_extension(mul_tmp3, sub_tmp6);
            yield_constr.constraint(builder, c6);
            
        }

        add_addition_constraints_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_B_ADD_MODSQ_OFFSET, bit_selector);
        add_subtraction_constraints_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_B_SUB_OFFSET, bit_selector);
        add_addition_constraints_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_B_ADD_OFFSET, bit_selector);
        for i in 0..24 {

            let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_CHECK_OFFSET]);
            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_B_Z0_REDUCE_OFFSET + REDUCE_X_OFFSET + i] , local_values[start_col + MULTIPLY_B_SUB_OFFSET + SUBTRACTION_DIFF_OFFSET + i]);
            let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
            yield_constr.constraint(builder, c1);


            let mul_tmp2 = builder.mul_extension(bit_selector_val, local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_CHECK_OFFSET]);
            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_B_Z1_REDUCE_OFFSET + REDUCE_X_OFFSET + i] , local_values[start_col + MULTIPLY_B_ADD_OFFSET + ADDITION_SUM_OFFSET + i]);
            let c2 = builder.mul_extension(mul_tmp2,sub_tmp2);
            yield_constr.constraint(builder, c2);

        }

        add_reduce_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + MULTIPLY_B_Z0_REDUCE_OFFSET, start_col + MULTIPLY_B_SELECTOR_OFFSET, bit_selector);
        add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_B_Z0_RANGECHECK_OFFSET, bit_selector);
        add_reduce_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + MULTIPLY_B_Z1_REDUCE_OFFSET, start_col + MULTIPLY_B_SELECTOR_OFFSET, bit_selector);
        add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_B_Z1_RANGECHECK_OFFSET, bit_selector)

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
    bit_selector: Option<P>,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    let modulus = get_u32_vec_from_literal(modulus());
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                FE::from_canonical_u32(modulus[i])
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                FE::from_canonical_u32(modulus[i])
            )
        );
    }
    add_addition_fp2_constraints(local_values, yield_constr, start_col, bit_selector);
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_X_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i]
            )
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_X_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i]
            )
        );
    }
    add_subtraction_fp2_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL, bit_selector);
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_DIFF_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL, bit_selector);
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_DIFF_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL, bit_selector);
}

pub fn add_subtraction_with_reduction_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    let modulus = get_u32_vec_from_literal(modulus());
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));

    for i in 0..12 {
        let lc = builder.constant_extension(F::Extension::from_canonical_u32(modulus[i]));

        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension( local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i], lc);
        let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c1);

        let mul_tmp2 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET]);
        let sub_tmp2 = builder.sub_extension( local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i], lc);
        let c2 = builder.mul_extension(mul_tmp2, sub_tmp2);
        yield_constr.constraint(builder, c2);
    }
    add_addition_fp2_constraints_ext_circuit(builder, yield_constr, local_values, start_col, bit_selector);
    
    for i in 0..12 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension( local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_X_OFFSET + i],local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i]);
        let c1 = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c1);

        let mul_tmp2 = builder.mul_extension(bit_selector_val,local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET]);
        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_X_OFFSET + i],local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i]);
        let c2 = builder.mul_extension(mul_tmp2, sub_tmp2);
        yield_constr.constraint(builder, c2);
    }
    add_subtraction_fp2_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL, bit_selector);
    for i in 0..12 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_DIFF_OFFSET + i],local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]);
        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c);
    }
    add_fp_reduce_single_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL, bit_selector);
    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL, bit_selector);
    for i in 0..12 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_DIFF_OFFSET + i], local_values[start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]);
        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c);
    }

    add_fp_reduce_single_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL, bit_selector);
    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL, bit_selector);
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
    bit_selector: Option<P>,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    add_addition_fp2_constraints(local_values, yield_constr, start_col, bit_selector);
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL, bit_selector);
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i] -
                local_values[start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL, bit_selector);
}

pub fn add_addition_with_reduction_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
) {
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));

    add_addition_fp2_constraints_ext_circuit(builder, yield_constr, local_values, start_col, bit_selector);
    for i in 0..12 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val,local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i], local_values[start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]);
        
        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c);
    }
    add_fp_reduce_single_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL, bit_selector);
    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL, bit_selector);
    for i in 0..12 {
        let mul_tmp1 = builder.mul_extension(bit_selector_val, local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET]);
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i],local_values[start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCE_X_OFFSET + i]);

        let c = builder.mul_extension(mul_tmp1, sub_tmp1);
        yield_constr.constraint(builder, c);
    }
    add_fp_reduce_single_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL, bit_selector);
    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL*2 + RANGE_CHECK_TOTAL, bit_selector);
}

pub fn add_non_residue_multiplication_constraints<F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
    >(
    local_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize,
    bit_selector: Option<P>,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let modulus = get_u32_vec_from_literal(modulus());
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_X_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_Y_OFFSET + i] - FE::from_canonical_u32(modulus[i]))
        );
    }
    add_addition_fp_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET, bit_selector);
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_X_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_SUM_OFFSET + i])
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_Y_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12])
        );
    }
    add_subtraction_fp_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL, bit_selector);
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_DIFF_OFFSET + i] -
                local_values[start_col + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_Z0_RANGECHECK_OFFSET, bit_selector);
    
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_X_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_Y_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12])
        );
    }
    add_addition_fp_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET, bit_selector);
    for i in 0..12 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_TOTAL + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_SUM_OFFSET + i] -
                local_values[start_col + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET, bit_selector);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_Z1_RANGECHECK_OFFSET, bit_selector);
}

pub fn add_non_residue_multiplication_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
){
    let modulus = get_u32_vec_from_literal(modulus());
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));

    for i in 0..12 {
        let lc  = builder.constant_extension(F::Extension::from_canonical_u32(modulus[i]));

        let mul_tmp = local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_CHECK_OFFSET];
        
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_X_OFFSET + i] , local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i]);
        let c1 = builder.mul_extension(mul_tmp,sub_tmp1);
        let c = builder.mul_extension(bit_selector_val, c1);
        yield_constr.constraint(builder, c);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_Y_OFFSET + i] , lc);
        let c2 = builder.mul_extension(mul_tmp, sub_tmp2);
        let c = builder.mul_extension(bit_selector_val, c2);
        yield_constr.constraint(builder, c);
    }
    add_addition_fp_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET, bit_selector);
    for i in 0..12 {
        let mul_tmp = local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_CHECK_OFFSET];

        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_X_OFFSET + i] , local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_SUM_OFFSET + i]);
        let c1 = builder.mul_extension(mul_tmp,sub_tmp1);
        let c = builder.mul_extension(bit_selector_val, c1);
        yield_constr.constraint(builder, c);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_Y_OFFSET + i] , local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12]);
        let c2 = builder.mul_extension(mul_tmp, sub_tmp2);
        let c = builder.mul_extension(bit_selector_val, c2);
        yield_constr.constraint(builder, c);
    }
    add_subtraction_fp_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL, bit_selector);
    for i in 0..12 {
        let sub_tmp = builder.sub_extension(  local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_DIFF_OFFSET + i] , local_values[start_col + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCE_X_OFFSET + i]);
        let c = builder.mul_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_CHECK_OFFSET], sub_tmp);
        let c = builder.mul_extension(bit_selector_val,c);
        yield_constr.constraint(builder, c);
    }
    add_fp_reduce_single_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET, bit_selector);
    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_NON_RESIDUE_MUL_Z0_RANGECHECK_OFFSET, bit_selector);

    for i in 0..12 {
        let mul_tmp = local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_CHECK_OFFSET];

        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_X_OFFSET + i] ,local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i]);
        let c1 = builder.mul_extension(mul_tmp,sub_tmp1);
        let c = builder.mul_extension(bit_selector_val, c1);
        yield_constr.constraint(builder,c);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_Y_OFFSET + i] , local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12]);
        let c2 = builder.mul_extension(mul_tmp, sub_tmp2);
        let c = builder.mul_extension(bit_selector_val, c2);
        yield_constr.constraint(builder,c); 
    }
    add_addition_fp_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET, bit_selector);
    for i in 0..12 {
        let sub_tmp = builder.sub_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_SUM_OFFSET + i] , local_values[start_col + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCE_X_OFFSET + i]);
        let c = builder.mul_extension(local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_TOTAL + FP_ADDITION_CHECK_OFFSET] , sub_tmp);
        let c = builder.mul_extension(bit_selector_val,c);
        yield_constr.constraint(builder,c);
    }
    add_fp_reduce_single_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET, bit_selector);
    add_range_check_constraints_ext_circuit(builder, yield_constr, local_values, start_col + FP2_NON_RESIDUE_MUL_Z1_RANGECHECK_OFFSET, bit_selector);
}