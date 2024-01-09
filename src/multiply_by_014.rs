use std::{str::FromStr, cmp::min};

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
    multiply_by_slice, sub_u32_slices, Fp, Fp2, calc_qs, calc_precomp_stuff_loop0, sub_u32_slices_12, mul_u32_slice_u32, mod_inverse, get_bls_12_381_parameter, calc_precomp_stuff_loop1, Fp6, Fp12, mul_by_nonresidue,
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

// FP6 multiplication offsets
pub const FP6_MUL_SELECTOR_OFFSET: usize = 0;
pub const FP6_MUL_X_INPUT_OFFSET: usize = FP6_MUL_SELECTOR_OFFSET + 1;
pub const FP6_MUL_Y_INPUT_OFFSET: usize = FP6_MUL_X_INPUT_OFFSET + 24*3;
pub const FP6_MUL_T0_CALC_OFFSET: usize = FP6_MUL_Y_INPUT_OFFSET + 24*3;
pub const FP6_MUL_T1_CALC_OFFSET: usize = FP6_MUL_T0_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const FP6_MUL_T2_CALC_OFFSET: usize = FP6_MUL_T1_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const FP6_MUL_T3_CALC_OFFSET: usize = FP6_MUL_T2_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const FP6_MUL_T4_CALC_OFFSET: usize = FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T5_CALC_OFFSET: usize = FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T6_CALC_OFFSET: usize = FP6_MUL_T5_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const FP6_MUL_T7_CALC_OFFSET: usize = FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T8_CALC_OFFSET: usize = FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_X_CALC_OFFSET: usize = FP6_MUL_T8_CALC_OFFSET + FP2_NON_RESIDUE_MUL_TOTAL;
pub const FP6_MUL_T9_CALC_OFFSET: usize = FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T10_CALC_OFFSET: usize = FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T11_CALC_OFFSET: usize = FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T12_CALC_OFFSET: usize = FP6_MUL_T11_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const FP6_MUL_T13_CALC_OFFSET: usize = FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T14_CALC_OFFSET: usize = FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_Y_CALC_OFFSET: usize = FP6_MUL_T14_CALC_OFFSET + FP2_NON_RESIDUE_MUL_TOTAL;
pub const FP6_MUL_T15_CALC_OFFSET: usize = FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T16_CALC_OFFSET: usize = FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T17_CALC_OFFSET: usize = FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_T18_CALC_OFFSET: usize = FP6_MUL_T17_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const FP6_MUL_T19_CALC_OFFSET: usize = FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_Z_CALC_OFFSET: usize = FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const FP6_MUL_TOTAL_COLUMNS: usize = FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;

// FP6 non residue multiplication
pub const FP6_NON_RESIDUE_MUL_CHECK_OFFSET: usize = 0;
pub const FP6_NON_RESIDUE_MUL_INPUT_OFFSET: usize = FP6_NON_RESIDUE_MUL_CHECK_OFFSET + 1;
pub const FP6_NON_RESIDUE_MUL_C2: usize = FP6_NON_RESIDUE_MUL_INPUT_OFFSET + 24*3;
pub const FP6_NON_RESIDUE_MUL_TOTAL: usize = FP6_NON_RESIDUE_MUL_C2 + FP2_NON_RESIDUE_MUL_TOTAL;

// FP6 add
pub const FP6_ADDITION_0_OFFSET: usize = 0;
pub const FP6_ADDITION_1_OFFSET: usize = FP6_ADDITION_0_OFFSET + FP2_ADDITION_TOTAL;
pub const FP6_ADDITION_2_OFFSET: usize = FP6_ADDITION_1_OFFSET + FP2_ADDITION_TOTAL;
pub const FP6_ADDITION_TOTAL: usize = FP6_ADDITION_2_OFFSET + FP2_ADDITION_TOTAL;

// FP6 add
pub const FP6_SUBTRACTION_0_OFFSET: usize = 0;
pub const FP6_SUBTRACTION_1_OFFSET: usize = FP6_SUBTRACTION_0_OFFSET + FP2_SUBTRACTION_TOTAL;
pub const FP6_SUBTRACTION_2_OFFSET: usize = FP6_SUBTRACTION_1_OFFSET + FP2_SUBTRACTION_TOTAL;
pub const FP6_SUBTRACTION_TOTAL: usize = FP6_SUBTRACTION_2_OFFSET + FP2_SUBTRACTION_TOTAL;

// MultiplyBy01
pub const MULTIPLY_BY_01_SELECTOR_OFFSET: usize = 0;
pub const MULTIPLY_BY_01_INPUT_OFFSET: usize = MULTIPLY_BY_01_SELECTOR_OFFSET + 1;
pub const MULTIPLY_BY_01_B0_OFFSET: usize = MULTIPLY_BY_01_INPUT_OFFSET + 24*3;
pub const MULTIPLY_BY_01_B1_OFFSET: usize = MULTIPLY_BY_01_B0_OFFSET + 24;
pub const MULTIPLY_BY_01_T0_CALC_OFFSET: usize = MULTIPLY_BY_01_B1_OFFSET + 24;
pub const MULTIPLY_BY_01_T1_CALC_OFFSET: usize = MULTIPLY_BY_01_T0_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const MULTIPLY_BY_01_T2_CALC_OFFSET: usize = MULTIPLY_BY_01_T1_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const MULTIPLY_BY_01_T3_CALC_OFFSET: usize = MULTIPLY_BY_01_T2_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const MULTIPLY_BY_01_X_CALC_OFFSET: usize = MULTIPLY_BY_01_T3_CALC_OFFSET + FP2_NON_RESIDUE_MUL_TOTAL;
pub const MULTIPLY_BY_01_T4_CALC_OFFSET: usize = MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const MULTIPLY_BY_01_T5_CALC_OFFSET: usize = MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const MULTIPLY_BY_01_T6_CALC_OFFSET: usize = MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const MULTIPLY_BY_01_T7_CALC_OFFSET: usize = MULTIPLY_BY_01_T6_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const MULTIPLY_BY_01_Y_CALC_OFFSET: usize = MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const MULTIPLY_BY_01_T8_CALC_OFFSET: usize = MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;
pub const MULTIPLY_BY_01_Z_CALC_OFFSET: usize = MULTIPLY_BY_01_T8_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const MULTIPLY_BY_01_TOTAL: usize = MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * 2;

// MultiplyBy1
pub const MULTIPLY_BY_1_SELECTOR_OFFSET: usize = 0;
pub const MULTIPLY_BY_1_INPUT_OFFSET: usize = MULTIPLY_BY_1_SELECTOR_OFFSET + 1;
pub const MULTIPLY_BY_1_B1_OFFSET: usize = MULTIPLY_BY_1_INPUT_OFFSET + 24*3;
pub const MULTIPLY_BY_1_T0_CALC_OFFSET: usize = MULTIPLY_BY_1_B1_OFFSET + 24;
pub const MULTIPLY_BY_1_X_CALC_OFFSET: usize = MULTIPLY_BY_1_T0_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const MULTIPLY_BY_1_Y_CALC_OFFSET: usize = MULTIPLY_BY_1_X_CALC_OFFSET + FP2_NON_RESIDUE_MUL_TOTAL;
pub const MULTIPLY_BY_1_Z_CALC_OFFSET: usize = MULTIPLY_BY_1_Y_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;
pub const MULTIPLY_BY_1_TOTAL: usize = MULTIPLY_BY_1_Z_CALC_OFFSET + TOTAL_COLUMNS_FP2_MULTIPLICATION;

// MultiplyBy014
pub const MULTIPLY_BY_014_SELECTOR_OFFSET: usize = 0;
pub const MULTIPLY_BY_014_INPUT_OFFSET: usize = MULTIPLY_BY_014_SELECTOR_OFFSET + 1;
pub const MULTIPLY_BY_014_O0_OFFSET: usize = MULTIPLY_BY_014_INPUT_OFFSET + 24*3*2;
pub const MULTIPLY_BY_014_O1_OFFSET: usize = MULTIPLY_BY_014_O0_OFFSET + 24;
pub const MULTIPLY_BY_014_O4_OFFSET: usize = MULTIPLY_BY_014_O1_OFFSET + 24;
pub const MULTIPLY_BY_014_T0_CALC_OFFSET: usize = MULTIPLY_BY_014_O4_OFFSET + 24;
pub const MULTIPLY_BY_014_T1_CALC_OFFSET: usize = MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_TOTAL;
pub const MULTIPLY_BY_014_T2_CALC_OFFSET: usize = MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_TOTAL;
pub const MULTIPLY_BY_014_X_CALC_OFFSET: usize = MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_TOTAL;
pub const MULTIPLY_BY_014_T3_CALC_OFFSET: usize = MULTIPLY_BY_014_X_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;
pub const MULTIPLY_BY_014_T4_CALC_OFFSET: usize = MULTIPLY_BY_014_T3_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;
pub const MULTIPLY_BY_014_T5_CALC_OFFSET: usize = MULTIPLY_BY_014_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*2;
pub const MULTIPLY_BY_014_T6_CALC_OFFSET: usize = MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_TOTAL;
pub const MULTIPLY_BY_014_Y_CALC_OFFSET: usize = MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;
pub const MULTIPLY_BY_014_TOTAL: usize = MULTIPLY_BY_014_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;

// FP12 multiplication offsets
pub const FP12_MUL_SELECTOR_OFFSET: usize = 0;
pub const FP12_MUL_X_INPUT_OFFSET: usize = FP12_MUL_SELECTOR_OFFSET + 1;
pub const FP12_MUL_Y_INPUT_OFFSET: usize = FP12_MUL_X_INPUT_OFFSET + 24*3*2;
pub const FP12_MUL_T0_CALC_OFFSET: usize = FP12_MUL_Y_INPUT_OFFSET + 24*3*2;
pub const FP12_MUL_T1_CALC_OFFSET: usize = FP12_MUL_T0_CALC_OFFSET + FP6_MUL_TOTAL_COLUMNS;
pub const FP12_MUL_T2_CALC_OFFSET: usize = FP12_MUL_T1_CALC_OFFSET + FP6_MUL_TOTAL_COLUMNS;
pub const FP12_MUL_X_CALC_OFFSET: usize = FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_TOTAL;
pub const FP12_MUL_T3_CALC_OFFSET: usize = FP12_MUL_X_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;
pub const FP12_MUL_T4_CALC_OFFSET: usize = FP12_MUL_T3_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;
pub const FP12_MUL_T5_CALC_OFFSET: usize = FP12_MUL_T4_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;
pub const FP12_MUL_T6_CALC_OFFSET: usize = FP12_MUL_T5_CALC_OFFSET + FP6_MUL_TOTAL_COLUMNS;
pub const FP12_MUL_Y_CALC_OFFSET: usize = FP12_MUL_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;
pub const FP12_MUL_TOTAL_COLUMNS: usize = FP12_MUL_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*6;

pub const TOTAL_COLUMNS: usize = MULTIPLY_BY_014_TOTAL;
pub const COLUMNS: usize = TOTAL_COLUMNS;

pub const PUBLIC_INPUT_X_OFFSET: usize = 0;
pub const PUBLIC_INPUT_O0_OFFSET: usize = PUBLIC_INPUT_X_OFFSET + 24*3*2;
pub const PUBLIC_INPUT_O1_OFFSET: usize = PUBLIC_INPUT_O0_OFFSET + 24;
pub const PUBLIC_INPUT_O4_OFFSET: usize = PUBLIC_INPUT_O1_OFFSET + 24;
pub const PUBLIC_INPUT_RES_OFFSET: usize = PUBLIC_INPUT_O4_OFFSET + 24;
pub const PUBLIC_INPUTS: usize = PUBLIC_INPUT_RES_OFFSET + 24*3*2;

macro_rules! bit_decomp_32 {
    ($row:expr, $col:expr, $f:ty, $p:ty) => {
        ((0..32).fold(<$p>::ZEROS, |acc, i| {
            acc + $row[$col + i] * <$f>::from_canonical_u64(1 << i)
        }))
    };
}

// A (Fp) * B (Fp) => C (Fp)
#[derive(Clone)]
pub struct MultiplyBy014Stark<F: RichField + Extendable<D>, const D: usize> {
    pub trace: Vec<[F; TOTAL_COLUMNS]>,
    num_rows: usize,
}

// Implement trace generator
impl<F: RichField + Extendable<D>, const D: usize> MultiplyBy014Stark<F, D> {
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
        // println!("rem {:?}", rem_24);
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

    pub fn fill_trace_non_residue_multiplication(&mut self, x: &[[u32; 12]; 2], row: usize, start_col: usize) {
        self.trace[row][start_col + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] = F::ONE;
        self.assign_u32_in_series(row, start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET, &x.concat());
        self.fill_trace_addition_fp(&x[0], &get_u32_vec_from_literal(modulus()), row, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET);
        let add_modulus = get_u32_vec_from_literal(
            BigUint::new(x[0].to_vec()) + modulus()
        );
        self.fill_trace_subtraction_fp(&add_modulus, &x[1], row, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL);
        let c0_c1_sub = get_u32_vec_from_literal(
            BigUint::new(add_modulus.to_vec()) - BigUint::new(x[1].to_vec())
        );
        let rem = self.fill_trace_reduce_single(&c0_c1_sub, row, start_col + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET);
        self.fill_range_check_trace(&rem, row, start_col + FP2_NON_RESIDUE_MUL_Z0_RANGECHECK_OFFSET);
        self.fill_trace_addition_fp(&x[0], &x[1], row, start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET);
        let c0_c1_add = get_u32_vec_from_literal(
            BigUint::new(x[0].to_vec()) + BigUint::new(x[1].to_vec())
        );
        let rem = self.fill_trace_reduce_single(&c0_c1_add, row, start_col + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET);
        self.fill_range_check_trace(&rem, row, start_col + FP2_NON_RESIDUE_MUL_Z1_RANGECHECK_OFFSET);
    }

    pub fn fill_trace_addition_fp6(&mut self, x: &[[u32; 12]; 6], y: &[[u32; 12]; 6], row: usize, start_col: usize) {
        self.fill_trace_addition_fp2(&[x[0], x[1]], &[y[0], y[1]], row, start_col + FP6_ADDITION_0_OFFSET);
        self.fill_trace_addition_fp2(&[x[2], x[3]], &[y[2], y[3]], row, start_col + FP6_ADDITION_1_OFFSET);
        self.fill_trace_addition_fp2(&[x[4], x[5]], &[y[4], y[5]], row, start_col + FP6_ADDITION_2_OFFSET);
    }

    pub fn fill_trace_addition_with_reduction_fp6(&mut self, x: &Fp6, y: &Fp6, row: usize, start_col: usize) {
        self.fill_trace_addition_fp6(&x.get_u32_slice(), &y.get_u32_slice(), row, start_col);
        for i in 0..6 {
            let sum = get_u32_vec_from_literal(
                BigUint::new(x.0[i].0.to_vec()) + BigUint::new(y.0[i].0.to_vec())
            );
            let rem = self.fill_trace_reduce_single(&sum, row, start_col + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i);
            self.fill_range_check_trace(&rem, row, start_col + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i + FP_SINGLE_REDUCE_TOTAL);
        }
    }

    pub fn fill_trace_subtraction_with_reduction_fp6(&mut self, x: &Fp6, y: &Fp6, row: usize, start_col: usize) {
        let modulus = vec![get_u32_vec_from_literal(modulus()); 6].try_into().unwrap();
        self.fill_trace_addition_fp6(&x.get_u32_slice(), &modulus, row, start_col);
        let x_modulus = modulus
            .iter()
            .zip(x.get_u32_slice())
            .map(|(m, f)| get_u32_vec_from_literal(
                BigUint::new(m.to_vec()) + BigUint::new(f.to_vec())
            ))
            .collect::<Vec<[u32; 12]>>()
            .try_into()
            .unwrap();
        self.fill_trace_subtraction_fp6(&x_modulus, &y.get_u32_slice(), row, start_col + FP6_ADDITION_TOTAL);
        for i in 0..6 {
            let diff = get_u32_vec_from_literal(
                BigUint::new(x_modulus[i].to_vec()) - BigUint::new(y.0[i].0.to_vec())
            );
            let rem = self.fill_trace_reduce_single(&diff, row, start_col + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i);
            self.fill_range_check_trace(&rem, row, start_col + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i + FP_SINGLE_REDUCE_TOTAL);
        }
    }

    pub fn fill_trace_subtraction_fp6(&mut self, x: &[[u32; 12]; 6], y: &[[u32; 12]; 6], row: usize, start_col: usize) {
        self.fill_trace_subtraction_fp2(&[x[0], x[1]], &[y[0], y[1]], row, start_col + FP6_SUBTRACTION_0_OFFSET);
        self.fill_trace_subtraction_fp2(&[x[2], x[3]], &[y[2], y[3]], row, start_col + FP6_SUBTRACTION_1_OFFSET);
        self.fill_trace_subtraction_fp2(&[x[4], x[5]], &[y[4], y[5]], row, start_col + FP6_SUBTRACTION_2_OFFSET);
    }

    pub fn fill_trace_non_residue_multiplication_fp6(&mut self, x: &Fp6, row: usize, start_col: usize) {
        self.trace[row][start_col + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] = F::ONE;
        for (i, e) in x.0.iter().enumerate() {
            self.assign_u32_in_series(row, start_col + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i*12, &e.0);
        }
        let c2 = Fp2([x.0[4], x.0[5]]);
        self.fill_trace_non_residue_multiplication(&c2.get_u32_slice(), row, start_col + FP6_NON_RESIDUE_MUL_C2);
    }

    pub fn fill_trace_fp6_multiplication(&mut self, x: &Fp6, y: &Fp6, start_row: usize, end_row: usize, start_col: usize) {
        for i in 0..6 {
            for row in start_row..end_row+1 {
                self.assign_u32_in_series(row, start_col + FP6_MUL_X_INPUT_OFFSET + 12*i, &x.0[i].0);
                self.assign_u32_in_series(row, start_col + FP6_MUL_Y_INPUT_OFFSET + 12*i, &y.0[i].0);
                self.trace[row][start_col + FP6_MUL_SELECTOR_OFFSET] = F::ONE;
            }
        }
        self.trace[end_row][start_col + FP6_MUL_SELECTOR_OFFSET] = F::ZERO;
        let (c0, c1, c2) = (Fp2([x.0[0], x.0[1]]), Fp2([x.0[2], x.0[3]]), Fp2([x.0[4], x.0[5]]));
        let (r0, r1, r2) = (Fp2([y.0[0], y.0[1]]), Fp2([y.0[2], y.0[3]]), Fp2([y.0[4], y.0[5]]));
        
        let t0 = c0*r0;
        self.generate_trace_fp2_mul(c0.get_u32_slice(), r0.get_u32_slice(), start_row, end_row, start_col + FP6_MUL_T0_CALC_OFFSET);
        let t1 = c1*r1;
        self.generate_trace_fp2_mul(c1.get_u32_slice(), r1.get_u32_slice(), start_row, end_row, start_col + FP6_MUL_T1_CALC_OFFSET);
        let t2 = c2*r2;
        self.generate_trace_fp2_mul(c2.get_u32_slice(), r2.get_u32_slice(), start_row, end_row, start_col + FP6_MUL_T2_CALC_OFFSET);

        let t3 = c1+c2;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&c1.get_u32_slice(), &c2.get_u32_slice(), row, start_col + FP6_MUL_T3_CALC_OFFSET);
        }
        let t4 = r1+r2;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&r1.get_u32_slice(), &r2.get_u32_slice(), row, start_col + FP6_MUL_T4_CALC_OFFSET);
        }
        let t5 = t3*t4;
        self.generate_trace_fp2_mul(t3.get_u32_slice(), t4.get_u32_slice(), start_row, end_row, start_col + FP6_MUL_T5_CALC_OFFSET);
        let t6 = t5-t1;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction(&t5.get_u32_slice(), &t1.get_u32_slice(), row, start_col + FP6_MUL_T6_CALC_OFFSET);
        }
        let t7 = t6-t2;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction(&t6.get_u32_slice(), &t2.get_u32_slice(), row, start_col + FP6_MUL_T7_CALC_OFFSET);
        }
        let t8 = t7.mul_by_nonresidue();
        for row in start_row..end_row+1 {
            self.fill_trace_non_residue_multiplication(&t7.get_u32_slice(), row, start_col + FP6_MUL_T8_CALC_OFFSET);
        }
        let _x = t8+t0;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&t8.get_u32_slice(), &t0.get_u32_slice(), row, start_col + FP6_MUL_X_CALC_OFFSET);
        }

        let t9 = c0+c1;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&c0.get_u32_slice(), &c1.get_u32_slice(), row, start_col + FP6_MUL_T9_CALC_OFFSET);
        }
        let t10 = r0+r1;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&r0.get_u32_slice(), &r1.get_u32_slice(), row, start_col + FP6_MUL_T10_CALC_OFFSET);
        }
        let t11 = t9*t10;
        self.generate_trace_fp2_mul(t9.get_u32_slice(), t10.get_u32_slice(), start_row, end_row, start_col + FP6_MUL_T11_CALC_OFFSET);
        let t12 = t11-t0;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction(&t11.get_u32_slice(), &t0.get_u32_slice(), row, start_col + FP6_MUL_T12_CALC_OFFSET);
        }
        let t13 = t12-t1;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction(&t12.get_u32_slice(), &t1.get_u32_slice(), row, start_col + FP6_MUL_T13_CALC_OFFSET);
        }
        let t14 = t2.mul_by_nonresidue();
        for row in start_row..end_row+1 {
            self.fill_trace_non_residue_multiplication(&t2.get_u32_slice(), row, start_col + FP6_MUL_T14_CALC_OFFSET);
        }
        let _y = t13+t14;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&t13.get_u32_slice(), &t14.get_u32_slice(), row, start_col + FP6_MUL_Y_CALC_OFFSET);
        }

        let t15 = c0+c2;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&c0.get_u32_slice(), &c2.get_u32_slice(), row, start_col + FP6_MUL_T15_CALC_OFFSET);
        }
        let t16 = r0+r2;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&r0.get_u32_slice(), &r2.get_u32_slice(), row, start_col + FP6_MUL_T16_CALC_OFFSET);
        }
        let t17 = t15*t16;
        self.generate_trace_fp2_mul(t15.get_u32_slice(), t16.get_u32_slice(), start_row, end_row, start_col + FP6_MUL_T17_CALC_OFFSET);
        let t18 = t17-t0;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction(&t17.get_u32_slice(), &t0.get_u32_slice(), row, start_col + FP6_MUL_T18_CALC_OFFSET);
        }
        let t19 = t18-t2;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction(&t18.get_u32_slice(), &t2.get_u32_slice(), row, start_col + FP6_MUL_T19_CALC_OFFSET);
        }
        let _z = t19+t1;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&t19.get_u32_slice(), &t1.get_u32_slice(), row, start_col + FP6_MUL_Z_CALC_OFFSET);
        }
    }

    pub fn fill_trace_multiply_by_1(&mut self, x: &Fp6, b1: &Fp2, start_row: usize, end_row: usize, start_col: usize) {
        for row in start_row..end_row+1 {
            for i in 0..6 {
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_1_INPUT_OFFSET + i*12, &x.0[i].0);
            }
            for i in 0..2 {
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_1_B1_OFFSET + i*12, &b1.0[i].0);
            }
            self.trace[row][start_col + MULTIPLY_BY_1_SELECTOR_OFFSET] = F::ONE;
        }
        self.trace[end_row][start_col + MULTIPLY_BY_1_SELECTOR_OFFSET] = F::ZERO;

        let c0 = Fp2([x.0[0], x.0[1]]);
        let c1 = Fp2([x.0[2], x.0[3]]);
        let c2 = Fp2([x.0[4], x.0[5]]);
        let t0 = c2*(*b1);
        self.generate_trace_fp2_mul(c2.get_u32_slice(), b1.get_u32_slice(), start_row, end_row, start_col + MULTIPLY_BY_1_T0_CALC_OFFSET);
        let _x = t0.mul_by_nonresidue();
        for row in start_row..end_row+1 { 
            self.fill_trace_non_residue_multiplication(&t0.get_u32_slice(), row, start_col + MULTIPLY_BY_1_X_CALC_OFFSET);
        }
        let _y = c0*(*b1);
        self.generate_trace_fp2_mul(c0.get_u32_slice(), b1.get_u32_slice(), start_row, end_row, start_col + MULTIPLY_BY_1_Y_CALC_OFFSET);
        let _z = c1*(*b1);
        self.generate_trace_fp2_mul(c1.get_u32_slice(), b1.get_u32_slice(), start_row, end_row, start_col + MULTIPLY_BY_1_Z_CALC_OFFSET);
    }

    pub fn fill_trace_multiply_by_01(&mut self, x: &Fp6, b0: &Fp2, b1: &Fp2, start_row: usize, end_row: usize, start_col: usize) {
        for row in start_row..end_row+1 {
            for i in 0..6 {
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_01_INPUT_OFFSET + i*12, &x.0[i].0);
            }
            for i in 0..2 {
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_01_B0_OFFSET + i*12, &b0.0[i].0);
            }
            for i in 0..2 {
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_01_B1_OFFSET + i*12, &b1.0[i].0);
            }
            self.trace[row][start_col + MULTIPLY_BY_01_SELECTOR_OFFSET] = F::ONE;
        }
        self.trace[end_row][start_col + MULTIPLY_BY_01_SELECTOR_OFFSET] = F::ZERO;

        let c0 = Fp2([x.0[0], x.0[1]]);
        let c1 = Fp2([x.0[2], x.0[3]]);
        let c2 = Fp2([x.0[4], x.0[5]]);

        let t0 = c0*(*b0);
        self.generate_trace_fp2_mul(c0.get_u32_slice(), b0.get_u32_slice(), start_row, end_row, start_col + MULTIPLY_BY_01_T0_CALC_OFFSET);
        let t1 = c1*(*b1);
        self.generate_trace_fp2_mul(c1.get_u32_slice(), b1.get_u32_slice(), start_row, end_row, start_col + MULTIPLY_BY_01_T1_CALC_OFFSET);

        let t2 = c2*(*b1);
        self.generate_trace_fp2_mul(c2.get_u32_slice(), b1.get_u32_slice(), start_row, end_row, start_col + MULTIPLY_BY_01_T2_CALC_OFFSET);
        let t3 = t2.mul_by_nonresidue();
        for row in start_row..end_row+1 {
            self.fill_trace_non_residue_multiplication(&t2.get_u32_slice(), row, start_col + MULTIPLY_BY_01_T3_CALC_OFFSET);
        }
        let _x = t3+t0;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&t3.get_u32_slice(), &t0.get_u32_slice(), row, start_col + MULTIPLY_BY_01_X_CALC_OFFSET);
        }

        let t4 = (*b0)+(*b1);
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&b0.get_u32_slice(), &b1.get_u32_slice(), row, start_col + MULTIPLY_BY_01_T4_CALC_OFFSET);
        }
        let t5 = c0+c1;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&c0.get_u32_slice(), &c1.get_u32_slice(), row, start_col + MULTIPLY_BY_01_T5_CALC_OFFSET);
        }
        let t6 = t4*t5;
        self.generate_trace_fp2_mul(t4.get_u32_slice(), t5.get_u32_slice(), start_row, end_row, start_col + MULTIPLY_BY_01_T6_CALC_OFFSET);
        let t7 = t6-t0;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction(&t6.get_u32_slice(), &t0.get_u32_slice(), row, start_col + MULTIPLY_BY_01_T7_CALC_OFFSET);
        }
        let _y = t7-t1;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction(&t7.get_u32_slice(), &t1.get_u32_slice(), row, start_col + MULTIPLY_BY_01_Y_CALC_OFFSET);
        }

        let t8 = c2*(*b0);
        self.generate_trace_fp2_mul(c2.get_u32_slice(), b0.get_u32_slice(), start_row, end_row, start_col + MULTIPLY_BY_01_T8_CALC_OFFSET);
        let _z = t8+t1;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&t8.get_u32_slice(), &t1.get_u32_slice(), row, start_col + MULTIPLY_BY_01_Z_CALC_OFFSET);
        }
    }

    pub fn fill_trace_multiply_by_014(&mut self, x: &Fp12, o0: &Fp2, o1: &Fp2, o4: &Fp2, start_row: usize, end_row: usize, start_col: usize) {
        for row in start_row..end_row+1 {
            for i in 0..12 {
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_014_INPUT_OFFSET + i*12, &x.0[i].0);
            }
            for i in 0..2 {
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_014_O0_OFFSET + i*12, &o0.0[i].0);
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_014_O1_OFFSET + i*12, &o1.0[i].0);
                self.assign_u32_in_series(row, start_col + MULTIPLY_BY_014_O4_OFFSET + i*12, &o4.0[i].0);
            }
            self.trace[row][start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] = F::ONE;
        }
        self.trace[end_row][start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] = F::ZERO;
        
        let c0 = Fp6(x.0[..6].try_into().unwrap());
        let c1 = Fp6(x.0[6..].try_into().unwrap());

        let t0 = c0.multiplyBy01(*o0, *o1);
        self.fill_trace_multiply_by_01(&c0, o0, o1, start_row, end_row, start_col + MULTIPLY_BY_014_T0_CALC_OFFSET);
        let t1 = c1.multiplyBy1(*o4);
        self.fill_trace_multiply_by_1(&c1, o4, start_row, end_row, start_col + MULTIPLY_BY_014_T1_CALC_OFFSET);
        let t2 = mul_by_nonresidue(t1.0);
        for row in start_row..end_row+1 {
            self.fill_trace_non_residue_multiplication_fp6(&t1, row, start_col + MULTIPLY_BY_014_T2_CALC_OFFSET);
        }
        let _x = t2+t0;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction_fp6(&t2, &t0, row, start_col + MULTIPLY_BY_014_X_CALC_OFFSET);
        }

        let t3 = c0+c1;
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction_fp6(&c0, &c1, row, start_col + MULTIPLY_BY_014_T3_CALC_OFFSET);
        }
        let t4 = (*o1)+(*o4);
        for row in start_row..end_row+1 {
            self.fill_trace_addition_with_reduction(&o1.get_u32_slice(), &o4.get_u32_slice(), row, start_col + MULTIPLY_BY_014_T4_CALC_OFFSET);
        }
        let t5 = t3.multiplyBy01(*o0, t4);
        self.fill_trace_multiply_by_01(&t3, o0, &t4, start_row, end_row, start_col + MULTIPLY_BY_014_T5_CALC_OFFSET);
        let t6 = t5-t0;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction_fp6(&t5, &t0, row, start_col + MULTIPLY_BY_014_T6_CALC_OFFSET);
        }
        let _y = t6-t1;
        for row in start_row..end_row+1 {
            self.fill_trace_subtraction_with_reduction_fp6(&t6, &t1, row, start_col + MULTIPLY_BY_014_Y_CALC_OFFSET);
        }
    }

    pub fn generate_trace(&mut self, x: Fp12, o0: Fp2, o1: Fp2, o4: Fp2) {
        self.fill_trace_multiply_by_014(&x, &o0, &o1, &o4, 0, self.num_rows-1, 0);
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
        yield_constr.constraint( local_values[start_col + RANGE_CHECK_SELECTOR_OFFSET] * local_values[bit_col + 30]);
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
    for i in 0..24 {
        yield_constr.constraint_transition(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i] - next_values[start_col + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint_transition(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i] - next_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i])
        );
    }
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_0_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_0_Y_1_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_1_Y_0_MULTIPLICATION_OFFSET + Y_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + X_1_Y_1_MULTIPLICATION_OFFSET + X_INPUT_OFFSET + i] -
            local_values[start_col + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(
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

pub fn add_non_residue_multiplication_constraints<F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
    >(
    local_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let modulus = get_u32_vec_from_literal(modulus());
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_X_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_Y_OFFSET + i] - FE::from_canonical_u32(modulus[i]))
        );
    }
    add_addition_fp_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET);
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_X_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_SUM_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_Y_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12])
        );
    }
    add_subtraction_fp_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL);
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_SUB_OFFSET + FP_ADDITION_TOTAL + FP_SUBTRACTION_DIFF_OFFSET + i] -
                local_values[start_col + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_Z0_RANGECHECK_OFFSET);
    
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_X_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_CHECK_OFFSET] *
            (local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_Y_OFFSET + i] - local_values[start_col + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12])
        );
    }
    add_addition_fp_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET);
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_TOTAL + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP2_NON_RESIDUE_MUL_C0_C1_ADD_OFFSET + FP_ADDITION_SUM_OFFSET + i] -
                local_values[start_col + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCE_X_OFFSET + i]
            )
        );
    }
    add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET);
    add_range_check_constraints(local_values, yield_constr, start_col + FP2_NON_RESIDUE_MUL_Z1_RANGECHECK_OFFSET);
}

pub fn add_addition_fp6_constraints<
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
    add_addition_fp2_constraints(local_values, yield_constr, start_col + FP6_ADDITION_0_OFFSET);
    add_addition_fp2_constraints(local_values, yield_constr, start_col + FP6_ADDITION_1_OFFSET);
    add_addition_fp2_constraints(local_values, yield_constr, start_col + FP6_ADDITION_2_OFFSET);
}

pub fn add_addition_with_reduction_constranints_fp6<
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
    add_addition_fp6_constraints(local_values, yield_constr, start_col);
    for j in 0..6 {
        let fp2_offset = if j < 2 {
            FP6_ADDITION_0_OFFSET
        } else if j < 4 {
            FP6_ADDITION_1_OFFSET
        } else {
            FP6_ADDITION_2_OFFSET
        };
        let fp_offset = if j%2 == 0 {
            FP2_ADDITION_0_OFFSET
        } else {
            FP2_ADDITION_1_OFFSET
        };
        for i in 0..12 {
            yield_constr.constraint(
                local_values[start_col + fp2_offset + fp_offset + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[start_col + fp2_offset + fp_offset + FP_ADDITION_SUM_OFFSET + i] -
                    local_values[start_col + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * j + FP_SINGLE_REDUCE_X_OFFSET + i]
                )
            );
        }
        add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * j);
        add_range_check_constraints(local_values, yield_constr, start_col + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL) * j + FP_SINGLE_REDUCE_TOTAL);
    }
}

pub fn add_subtraction_fp6_constraints<
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
    add_subtraction_fp2_constraints(local_values, yield_constr, start_col + FP6_SUBTRACTION_0_OFFSET);
    add_subtraction_fp2_constraints(local_values, yield_constr, start_col + FP6_SUBTRACTION_1_OFFSET);
    add_subtraction_fp2_constraints(local_values, yield_constr, start_col + FP6_SUBTRACTION_2_OFFSET);
}

pub fn add_subtraction_with_reduction_constranints_fp6<
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
    add_addition_fp6_constraints(local_values, yield_constr, start_col);
    add_subtraction_fp6_constraints(local_values, yield_constr, start_col + FP6_ADDITION_TOTAL);

    let modulus = get_u32_vec_from_literal(modulus());
    for j in 0..6 {
        let (fp2_add_offset, fp2_sub_offset) = if j < 2 {
            (FP6_ADDITION_0_OFFSET, FP6_SUBTRACTION_0_OFFSET)
        } else if j < 4 {
            (FP6_ADDITION_1_OFFSET, FP6_SUBTRACTION_1_OFFSET)
        } else {
            (FP6_ADDITION_2_OFFSET, FP6_SUBTRACTION_2_OFFSET)
        };
        let (_fp_add_offset, fp_sub_offset) = if j%2 == 0 {
            (FP2_ADDITION_0_OFFSET, FP2_SUBTRACTION_0_OFFSET)
        } else {
            (FP2_ADDITION_1_OFFSET, FP2_SUBTRACTION_1_OFFSET)
        };
        for i in 0..12 {
            yield_constr.constraint(
                local_values[start_col + fp2_add_offset + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[start_col + fp2_add_offset + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                    FE::from_canonical_u32(modulus[i])
                )
            );
            yield_constr.constraint(
                local_values[start_col + fp2_add_offset + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                    local_values[start_col + fp2_add_offset + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                    FE::from_canonical_u32(modulus[i])
                )
            );
        }
        for i in 0..12 {
            yield_constr.constraint(
                local_values[start_col + FP6_ADDITION_TOTAL + fp2_sub_offset + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[start_col + FP6_ADDITION_TOTAL + fp2_sub_offset + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_X_OFFSET + i] -
                    local_values[start_col + fp2_add_offset + FP2_ADDITION_0_OFFSET + FP_ADDITION_SUM_OFFSET + i]
                )
            );
            yield_constr.constraint(
                local_values[start_col + FP6_ADDITION_TOTAL + fp2_sub_offset + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[start_col + FP6_ADDITION_TOTAL + fp2_sub_offset + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_X_OFFSET + i] -
                    local_values[start_col + fp2_add_offset + FP2_ADDITION_1_OFFSET + FP_ADDITION_SUM_OFFSET + i]
                )
            );
        }
        for i in 0..12 {
            yield_constr.constraint(
                local_values[start_col + FP6_ADDITION_TOTAL + fp2_sub_offset + fp_sub_offset + FP_SUBTRACTION_CHECK_OFFSET] * (
                    local_values[start_col + FP6_ADDITION_TOTAL + fp2_sub_offset + fp_sub_offset + FP_SUBTRACTION_DIFF_OFFSET + i] -
                    local_values[start_col + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCE_X_OFFSET + i]
                )
            );
        }
        add_fp_reduce_single_constraints(local_values, yield_constr, start_col + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j);
        add_range_check_constraints(local_values, yield_constr, start_col + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCE_TOTAL);
    }
}

pub fn add_non_residue_multiplication_fp6_constraints<F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
    >(
    local_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (local_values[start_col + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + 48] - local_values[start_col + FP6_NON_RESIDUE_MUL_C2 + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i])
        );
    }
    add_non_residue_multiplication_constraints(local_values, yield_constr, start_col + FP6_NON_RESIDUE_MUL_C2);
}

pub fn add_fp6_multiplication_constraints<F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
    >(
    local_values: &[P],
    next_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    for i in 0..24*3 {
        yield_constr.constraint_transition(
            local_values[start_col + FP6_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i] - next_values[start_col + FP6_MUL_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint_transition(
            local_values[start_col + FP6_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i] - next_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i])
        );
    }

    // T0
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T0_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i] - local_values[start_col + FP6_MUL_T0_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T0_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i] - local_values[start_col + FP6_MUL_T0_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i])
        );
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + FP6_MUL_T0_CALC_OFFSET);

    // T1
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T1_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 24] - local_values[start_col + FP6_MUL_T1_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T1_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 24] - local_values[start_col + FP6_MUL_T1_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i])
        );
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + FP6_MUL_T1_CALC_OFFSET);

    // T2
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T2_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 48] - local_values[start_col + FP6_MUL_T2_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T2_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 48] - local_values[start_col + FP6_MUL_T2_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i])
        );
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + FP6_MUL_T2_CALC_OFFSET);

    // T3
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 24]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 24 + 12]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 48]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 48 + 12]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T3_CALC_OFFSET);

    // T4
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 24]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 24 + 12]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 48]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 48 + 12]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T4_CALC_OFFSET);

    // T5
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T5_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T5_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T5_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T3_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T5_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T5_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T5_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T5_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T5_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i + 12])
        );
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + FP6_MUL_T5_CALC_OFFSET);

    // T6
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T5_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T5_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T1_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T1_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }

    add_subtraction_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T6_CALC_OFFSET);

    // T7
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T6_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T2_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T2_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }

    add_subtraction_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T7_CALC_OFFSET);

    // T8
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T8_CALC_OFFSET + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (
                local_values[start_col + FP6_MUL_T8_CALC_OFFSET + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i] - local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T8_CALC_OFFSET + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (
                local_values[start_col + FP6_MUL_T8_CALC_OFFSET + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12] - local_values[start_col + FP6_MUL_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
    }
    add_non_residue_multiplication_constraints(local_values, yield_constr, start_col + FP6_MUL_T8_CALC_OFFSET);

    // X calc offset
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T8_CALC_OFFSET + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T8_CALC_OFFSET + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_X_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_X_CALC_OFFSET);

    // T9
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 12]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 24]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 24 + 12]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T9_CALC_OFFSET);

    // T10
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 12]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 24]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 24 + 12]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T10_CALC_OFFSET);

    // T11
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T11_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T11_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T11_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T9_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T11_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T11_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T11_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T11_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T10_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T11_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i + 12])
        );
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + FP6_MUL_T11_CALC_OFFSET);

    // T12
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T11_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T11_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }

    add_subtraction_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T12_CALC_OFFSET);

    // T13
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T12_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T1_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T1_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }

    add_subtraction_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T13_CALC_OFFSET);

    // T14
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T14_CALC_OFFSET + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (
                local_values[start_col + FP6_MUL_T14_CALC_OFFSET + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i] - local_values[start_col + FP6_MUL_T2_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T14_CALC_OFFSET + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (
                local_values[start_col + FP6_MUL_T14_CALC_OFFSET + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12] - local_values[start_col + FP6_MUL_T2_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }
    add_non_residue_multiplication_constraints(local_values, yield_constr, start_col + FP6_MUL_T14_CALC_OFFSET);

    // Y calc offset
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T13_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T14_CALC_OFFSET + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_Y_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T14_CALC_OFFSET + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_Y_CALC_OFFSET);

    // T15
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 12]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 48]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_X_INPUT_OFFSET + i + 48 + 12]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T15_CALC_OFFSET);

    // T16
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 12]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 48]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_Y_INPUT_OFFSET + i + 48 + 12]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T16_CALC_OFFSET);

    // T17
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T17_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T17_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T17_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T15_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T17_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T17_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T17_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T17_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + FP6_MUL_T16_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + FP6_MUL_T17_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i + 12])
        );
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + FP6_MUL_T17_CALC_OFFSET);

    // T18
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T17_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T17_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }

    add_subtraction_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T18_CALC_OFFSET);

    // T19
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T18_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T2_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T2_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }

    add_subtraction_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_T19_CALC_OFFSET);

    // Z calc offset
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + FP6_MUL_T19_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T1_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + FP6_MUL_Z_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + FP6_MUL_T1_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }

    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + FP6_MUL_Z_CALC_OFFSET);
}

pub fn add_multiply_by_1_constraints<F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
    >(
    local_values: &[P],
    next_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    for i in 0..24 {
        for j in 0..3 {
            yield_constr.constraint_transition(
                local_values[start_col + MULTIPLY_BY_1_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_1_INPUT_OFFSET + j*24 + i] - next_values[start_col + MULTIPLY_BY_1_INPUT_OFFSET + j*24 + i])
            );
        }
        yield_constr.constraint_transition(
            local_values[start_col + MULTIPLY_BY_1_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_B1_OFFSET + i] - next_values[start_col + MULTIPLY_BY_1_B1_OFFSET + i])
        );
    }
    
    // T0
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_1_T0_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_T0_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_1_INPUT_OFFSET + i + 48])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_1_T0_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_T0_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_1_B1_OFFSET + i])
        )
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_1_T0_CALC_OFFSET);

    // X
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_1_X_CALC_OFFSET + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_X_CALC_OFFSET + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i] -
            local_values[start_col + MULTIPLY_BY_1_T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_1_X_CALC_OFFSET + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_X_CALC_OFFSET + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12] -
            local_values[start_col + MULTIPLY_BY_1_T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i])
        );
    }
    add_non_residue_multiplication_constraints(local_values, yield_constr, start_col + MULTIPLY_BY_1_X_CALC_OFFSET);

    // Y
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_1_Y_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_Y_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_1_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_1_Y_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_Y_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_1_B1_OFFSET + i])
        )
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_1_Y_CALC_OFFSET);

    // Z
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_1_Z_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_Z_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_1_INPUT_OFFSET + i + 24])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_1_Z_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_1_Z_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_1_B1_OFFSET + i])
        )
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_1_Z_CALC_OFFSET);
}

pub fn add_multiply_by_01_constraints<F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
    >(
    local_values: &[P],
    next_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    for i in 0..24 {
        for j in 0..3 {
            yield_constr.constraint_transition(
                local_values[start_col + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + j*24 + i] - next_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + j*24 + i])
            );
        }
        yield_constr.constraint_transition(
            local_values[start_col + MULTIPLY_BY_01_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_B0_OFFSET + i] - next_values[start_col + MULTIPLY_BY_01_B0_OFFSET + i])
        );
        yield_constr.constraint_transition(
            local_values[start_col + MULTIPLY_BY_01_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_B1_OFFSET + i] - next_values[start_col + MULTIPLY_BY_01_B1_OFFSET + i])
        );
    }
    
    // T0
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T0_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T0_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T0_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T0_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_B0_OFFSET + i])
        )
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_01_T0_CALC_OFFSET);

    // T1
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T1_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T1_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + i + 24])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T1_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T1_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_B1_OFFSET + i])
        )
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_01_T1_CALC_OFFSET);

    // T2
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T2_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T2_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + i + 48])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T2_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T2_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_B1_OFFSET + i])
        )
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_01_T2_CALC_OFFSET);

    // T3
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T3_CALC_OFFSET + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T3_CALC_OFFSET + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i] -
            local_values[start_col + MULTIPLY_BY_01_T2_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T3_CALC_OFFSET + FP2_NON_RESIDUE_MUL_CHECK_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T3_CALC_OFFSET + FP2_NON_RESIDUE_MUL_INPUT_OFFSET + i + 12] -
            local_values[start_col + MULTIPLY_BY_01_T2_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i])
        );
    }
    add_non_residue_multiplication_constraints(local_values, yield_constr, start_col + MULTIPLY_BY_01_T3_CALC_OFFSET);

    // X
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T3_CALC_OFFSET + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T3_CALC_OFFSET + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }
    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + MULTIPLY_BY_01_X_CALC_OFFSET);

    // T4
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_B0_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_B0_OFFSET + i + 12]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_B1_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_B1_OFFSET + i + 12]
            )
        );
    }
    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + MULTIPLY_BY_01_T4_CALC_OFFSET);

    // T5
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + i + 12]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + i + 24]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + i + 36]
            )
        );
    }
    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + MULTIPLY_BY_01_T5_CALC_OFFSET);

    // T6
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i + 12])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T5_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i + 12])
        );
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_01_T6_CALC_OFFSET);

    // T7
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T6_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T0_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T0_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }
    add_subtraction_with_reduction_constranints(local_values, yield_constr, start_col + MULTIPLY_BY_01_T7_CALC_OFFSET);

    // Y
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T7_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL + FP_SINGLE_REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_0_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T1_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_1_OFFSET + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T1_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }
    add_subtraction_with_reduction_constranints(local_values, yield_constr, start_col + MULTIPLY_BY_01_Y_CALC_OFFSET);

    // T8
    for i in 0..24 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T8_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T8_CALC_OFFSET + FP2_FP2_X_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_INPUT_OFFSET + i + 48])
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_T8_CALC_OFFSET + FP2_FP2_SELECTOR_OFFSET] *
            (local_values[start_col + MULTIPLY_BY_01_T8_CALC_OFFSET + FP2_FP2_Y_INPUT_OFFSET + i] - local_values[start_col + MULTIPLY_BY_01_B0_OFFSET + i])
        )
    }
    add_fp2_mul_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_01_T8_CALC_OFFSET);

    // Z
    for i in 0..12 {
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T8_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T8_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_0_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T1_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
        yield_constr.constraint(
            local_values[start_col + MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_CHECK_OFFSET] * (
                local_values[start_col + MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_1_OFFSET + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_01_T1_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET + i]
            )
        );
    }
    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + MULTIPLY_BY_01_Z_CALC_OFFSET);
}

pub fn add_multiply_by_014_constraints<F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
    >(
    local_values: &[P],
    next_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize,
    ) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    for i in 0..12 {
        for j in 0..12 {
            yield_constr.constraint_transition(
                local_values[start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i] -
                next_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i])
            );
        }
        for j in 0..2 {
            yield_constr.constraint_transition(
                local_values[start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i] -
                next_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i])
            );yield_constr.constraint_transition(
                local_values[start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i] -
                next_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i])
            );yield_constr.constraint_transition(
                local_values[start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i] -
                next_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i])
            );
        }
    }

    // T0
    for i in 0..12 {
        for j in 0..6 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_INPUT_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i])
            );
        }
        for j in 0..2 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_B0_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i])
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_B1_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i])
            );
        }
    }
    add_multiply_by_01_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_014_T0_CALC_OFFSET);

    // T1
    for i in 0..12 {
        for j in 0..6 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_INPUT_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i + 24*3])
            );
        }
        for j in 0..2 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_B1_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i])
            );
        }
    }
    add_multiply_by_1_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_014_T1_CALC_OFFSET);

    // T2
    for j in 0..2 {
        let (x_offset, yz_offset) = if j==0 {
            (FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET, Z1_REDUCE_OFFSET)
        } else {
            (FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET, Z2_REDUCE_OFFSET)
        };
        for i in 0..12 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12] -
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_X_CALC_OFFSET + x_offset + FP_SINGLE_REDUCED_OFFSET + i])
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12 + 24] -
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_Y_CALC_OFFSET + yz_offset + REDUCED_OFFSET + i])
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12 + 48] -
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_Z_CALC_OFFSET + yz_offset + REDUCED_OFFSET + i])
            );
        }
    }
    add_non_residue_multiplication_fp6_constraints(local_values, yield_constr, start_col + MULTIPLY_BY_014_T2_CALC_OFFSET);

    // X
    for j in 0..6 {
        let (addition_offset, x_offset, y_offset) = if j==0 {
            (FP6_ADDITION_0_OFFSET + FP2_ADDITION_0_OFFSET, FP6_NON_RESIDUE_MUL_C2 + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET, MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_TOTAL)
        } else if j==1 {
            (FP6_ADDITION_0_OFFSET + FP2_ADDITION_1_OFFSET, FP6_NON_RESIDUE_MUL_C2 + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET, MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)
        } else if j ==2 {
            (FP6_ADDITION_1_OFFSET + FP2_ADDITION_0_OFFSET, FP6_NON_RESIDUE_MUL_INPUT_OFFSET, MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL)
        } else if j==3 {
            (FP6_ADDITION_1_OFFSET + FP2_ADDITION_1_OFFSET, FP6_NON_RESIDUE_MUL_INPUT_OFFSET + 12, MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)
        } else if j==4 {
            (FP6_ADDITION_2_OFFSET + FP2_ADDITION_0_OFFSET, FP6_NON_RESIDUE_MUL_INPUT_OFFSET + 24, MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_TOTAL)
        } else {
            (FP6_ADDITION_2_OFFSET + FP2_ADDITION_1_OFFSET, FP6_NON_RESIDUE_MUL_INPUT_OFFSET + 36, MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_TOTAL + FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)
        };
        for i in 0..12 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + x_offset + i])
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + y_offset + FP_SINGLE_REDUCED_OFFSET + i])
            );
        }
    }
    add_addition_with_reduction_constranints_fp6(local_values, yield_constr, start_col + MULTIPLY_BY_014_X_CALC_OFFSET);

    // T3
    for j in 0..3 {
        let mut addition_offset = if j==0 {
            FP6_ADDITION_0_OFFSET
        } else if j==1 {
            FP6_ADDITION_1_OFFSET
        } else {
            FP6_ADDITION_2_OFFSET
        };
        for k in 0..2 {
            addition_offset += if k==0 {
                FP2_ADDITION_0_OFFSET
            } else {
                FP2_ADDITION_1_OFFSET
            };
            for i in 0..12 {
                yield_constr.constraint(
                    local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                    (local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                    local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*24 + k*12 + i])
                );
                yield_constr.constraint(
                    local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                    (local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] -
                    local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*24 + k*12 + i + 24*3])
                );
            }
        }
    }
    add_addition_with_reduction_constranints_fp6(local_values, yield_constr, start_col + MULTIPLY_BY_014_T3_CALC_OFFSET);

    // T4
    for j in 0..2 {
        let addition_offset = if j==0 {
            FP2_ADDITION_0_OFFSET
        } else {
            FP2_ADDITION_1_OFFSET
        };
        for i in 0..12 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i])
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i])
            );
        }
    }
    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + MULTIPLY_BY_014_T4_CALC_OFFSET);

    // T5
    for i in 0..12 {
        for j in 0..6 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_INPUT_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i])
            );
        }
        for j in 0..2 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_B0_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i])
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_B1_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i])
            );
        }
    }
    add_multiply_by_01_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_014_T5_CALC_OFFSET);

    // T6
    for j in 0..3 {
        let (mut addition_offset, mut subtraction_offset, input_offset) = if j==0 {
            (FP6_ADDITION_0_OFFSET, FP6_SUBTRACTION_0_OFFSET, MULTIPLY_BY_01_X_CALC_OFFSET + FP2_ADDITION_TOTAL)
        } else if j==1 {
            (FP6_ADDITION_1_OFFSET, FP6_SUBTRACTION_1_OFFSET, MULTIPLY_BY_01_Y_CALC_OFFSET + FP2_ADDITION_TOTAL + FP2_SUBTRACTION_TOTAL)
        } else {
            (FP6_ADDITION_2_OFFSET, FP6_SUBTRACTION_2_OFFSET, MULTIPLY_BY_01_Z_CALC_OFFSET + FP2_ADDITION_TOTAL)
        };
        for k in 0..2 {
            addition_offset += if k==0 {
                FP2_ADDITION_0_OFFSET
            } else {
                FP2_ADDITION_1_OFFSET
            };
            subtraction_offset += if k==0 {
                FP2_SUBTRACTION_0_OFFSET
            } else {
                FP2_SUBTRACTION_1_OFFSET
            };
            for i in 0..12 {
                yield_constr.constraint(
                    local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                    (local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                    local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + input_offset + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*k + FP_SINGLE_REDUCED_OFFSET + i])
                );
                yield_constr.constraint(
                    local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_CHECK_OFFSET] *
                    (local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_Y_OFFSET + i] -
                    local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + input_offset + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*k + FP_SINGLE_REDUCED_OFFSET + i])
                );
            }
        }
    }
    add_subtraction_with_reduction_constranints_fp6(local_values, yield_constr, start_col + MULTIPLY_BY_014_T6_CALC_OFFSET);

    // Y
    for j in 0..6 {
        let (addition_offset, subtraction_offset, input_offset) = if j==0 {
            (FP6_ADDITION_0_OFFSET + FP2_ADDITION_0_OFFSET, FP6_SUBTRACTION_0_OFFSET + FP2_SUBTRACTION_0_OFFSET, MULTIPLY_BY_1_X_CALC_OFFSET + FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET)
        } else if j==1 {
            (FP6_ADDITION_0_OFFSET + FP2_ADDITION_1_OFFSET, FP6_SUBTRACTION_0_OFFSET + FP2_SUBTRACTION_1_OFFSET, MULTIPLY_BY_1_X_CALC_OFFSET + FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET + FP_SINGLE_REDUCED_OFFSET)
        } else if j==2 {
            (FP6_ADDITION_1_OFFSET + FP2_ADDITION_0_OFFSET, FP6_SUBTRACTION_1_OFFSET + FP2_SUBTRACTION_0_OFFSET, MULTIPLY_BY_1_Y_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET)
        } else if j==3 {
            (FP6_ADDITION_1_OFFSET + FP2_ADDITION_1_OFFSET, FP6_SUBTRACTION_1_OFFSET + FP2_SUBTRACTION_1_OFFSET, MULTIPLY_BY_1_Y_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET)
        } else if j==4 {
            (FP6_ADDITION_2_OFFSET + FP2_ADDITION_0_OFFSET, FP6_SUBTRACTION_2_OFFSET + FP2_SUBTRACTION_0_OFFSET, MULTIPLY_BY_1_Z_CALC_OFFSET + Z1_REDUCE_OFFSET + REDUCED_OFFSET)
        } else {
            (FP6_ADDITION_2_OFFSET + FP2_ADDITION_1_OFFSET, FP6_SUBTRACTION_2_OFFSET + FP2_SUBTRACTION_1_OFFSET, MULTIPLY_BY_1_Z_CALC_OFFSET + Z2_REDUCE_OFFSET + REDUCED_OFFSET)
        };
        for i in 0..12 {
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i])
            );
            yield_constr.constraint(
                local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + input_offset + i])
            );
        }
    }
    add_subtraction_with_reduction_constranints_fp6(local_values, yield_constr, start_col + MULTIPLY_BY_014_Y_CALC_OFFSET);
}

// Implement constraint generator
impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for MultiplyBy014Stark<F, D> {
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
        for i in 0..24 {
            for j in 0..6 {
                yield_constr.constraint_first_row(local_values[MULTIPLY_BY_014_INPUT_OFFSET + i] - public_inputs[PUBLIC_INPUT_X_OFFSET + i + 24*j]);
            }
            yield_constr.constraint_first_row(local_values[MULTIPLY_BY_014_O0_OFFSET + i] - public_inputs[PUBLIC_INPUT_O0_OFFSET + i]);
            yield_constr.constraint_first_row(local_values[MULTIPLY_BY_014_O1_OFFSET + i] - public_inputs[PUBLIC_INPUT_O1_OFFSET + i]);
            yield_constr.constraint_first_row(local_values[MULTIPLY_BY_014_O4_OFFSET + i] - public_inputs[PUBLIC_INPUT_O4_OFFSET + i]);
        }
        for i in 0..12 {
            for j in 0..6 {
                yield_constr.constraint_first_row(
                    local_values[MULTIPLY_BY_014_X_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i] -
                    public_inputs[PUBLIC_INPUT_RES_OFFSET + j*12 + i]
                );
                yield_constr.constraint_first_row(
                    local_values[MULTIPLY_BY_014_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i] -
                    public_inputs[PUBLIC_INPUT_RES_OFFSET + j*12 + i + 24*3]
                );
            }
        }
        add_multiply_by_014_constraints(local_values, next_values, yield_constr, 0);
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
