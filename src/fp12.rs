use plonky2::{field::{extension::{Extendable, FieldExtension}, packed::PackedField, types::Field}, hash::hash_types::RichField, iop::ext_target::ExtensionTarget, plonk::circuit_builder::CircuitBuilder};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::{native::{mul_by_nonresidue, Fp12, Fp2, Fp6}, utils::*, fp::*, fp2::*, fp6::*};

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

pub fn fill_trace_multiply_by_014<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(trace: &mut Vec<[F; C]>, x: &Fp12, o0: &Fp2, o1: &Fp2, o4: &Fp2, start_row: usize, end_row: usize, start_col: usize) {
    for row in start_row..end_row+1 {
        for i in 0..12 {
            assign_u32_in_series(trace, row, start_col + MULTIPLY_BY_014_INPUT_OFFSET + i*12, &x.0[i].0);
        }
        for i in 0..2 {
            assign_u32_in_series(trace, row, start_col + MULTIPLY_BY_014_O0_OFFSET + i*12, &o0.0[i].0);
            assign_u32_in_series(trace, row, start_col + MULTIPLY_BY_014_O1_OFFSET + i*12, &o1.0[i].0);
            assign_u32_in_series(trace, row, start_col + MULTIPLY_BY_014_O4_OFFSET + i*12, &o4.0[i].0);
        }
        trace[row][start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] = F::ONE;
    }
    trace[end_row][start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] = F::ZERO;
    
    let c0 = Fp6(x.0[..6].try_into().unwrap());
    let c1 = Fp6(x.0[6..].try_into().unwrap());

    let t0 = c0.multiplyBy01(*o0, *o1);
    fill_trace_multiply_by_01(trace, &c0, o0, o1, start_row, end_row, start_col + MULTIPLY_BY_014_T0_CALC_OFFSET);
    let t1 = c1.multiplyBy1(*o4);
    fill_trace_multiply_by_1(trace, &c1, o4, start_row, end_row, start_col + MULTIPLY_BY_014_T1_CALC_OFFSET);
    let t2 = mul_by_nonresidue(t1.0);
    for row in start_row..end_row+1 {
        fill_trace_non_residue_multiplication_fp6(trace, &t1, row, start_col + MULTIPLY_BY_014_T2_CALC_OFFSET);
    }
    let _x = t2+t0;
    for row in start_row..end_row+1 {
        fill_trace_addition_with_reduction_fp6(trace, &t2, &t0, row, start_col + MULTIPLY_BY_014_X_CALC_OFFSET);
    }

    let t3 = c0+c1;
    for row in start_row..end_row+1 {
        fill_trace_addition_with_reduction_fp6(trace, &c0, &c1, row, start_col + MULTIPLY_BY_014_T3_CALC_OFFSET);
    }
    let t4 = (*o1)+(*o4);
    for row in start_row..end_row+1 {
        fill_trace_addition_with_reduction(trace, &o1.get_u32_slice(), &o4.get_u32_slice(), row, start_col + MULTIPLY_BY_014_T4_CALC_OFFSET);
    }
    let t5 = t3.multiplyBy01(*o0, t4);
    fill_trace_multiply_by_01(trace, &t3, o0, &t4, start_row, end_row, start_col + MULTIPLY_BY_014_T5_CALC_OFFSET);
    let t6 = t5-t0;
    for row in start_row..end_row+1 {
        fill_trace_subtraction_with_reduction_fp6(trace, &t5, &t0, row, start_col + MULTIPLY_BY_014_T6_CALC_OFFSET);
    }
    let _y = t6-t1;
    for row in start_row..end_row+1 {
        fill_trace_subtraction_with_reduction_fp6(trace, &t6, &t1, row, start_col + MULTIPLY_BY_014_Y_CALC_OFFSET);
    }
}

pub fn fill_trace_fp12_multiplication<F: RichField + Extendable<D>,
    const D: usize,
    const C: usize,
>(trace: &mut Vec<[F; C]>, x: &Fp12, y: &Fp12, start_row: usize, end_row: usize, start_col: usize) {
    for row in start_row..end_row+1 {
        for i in 0..12 {
            assign_u32_in_series(trace, row, start_col + FP12_MUL_X_INPUT_OFFSET + i*12, &x.0[i].0);
            assign_u32_in_series(trace, row, start_col + FP12_MUL_Y_INPUT_OFFSET + i*12, &y.0[i].0);
        }
        trace[row][start_col + FP12_MUL_SELECTOR_OFFSET] = F::ONE;
    }
    trace[end_row][start_col + FP12_MUL_SELECTOR_OFFSET] = F::ZERO;
    let (c0, c1) = (Fp6(x.0[0..6].try_into().unwrap()), Fp6(x.0[6..12].try_into().unwrap()));
    let (r0, r1) = (Fp6(y.0[0..6].try_into().unwrap()), Fp6(y.0[6..12].try_into().unwrap()));
    let t0 = c0*r0;
    fill_trace_fp6_multiplication(trace, &c0, &r0, start_row, end_row, start_col + FP12_MUL_T0_CALC_OFFSET);
    let t1 = c1*r1;
    fill_trace_fp6_multiplication(trace, &c1, &r1, start_row, end_row, start_col + FP12_MUL_T1_CALC_OFFSET);
    let t2 = mul_by_nonresidue(t1.0);
    for row in start_row..end_row+1 {
        fill_trace_non_residue_multiplication_fp6(trace, &t1, row, start_col + FP12_MUL_T2_CALC_OFFSET);
    }
    let _x = t0+t2;
    for row in start_row..end_row+1 {
        fill_trace_addition_with_reduction_fp6(trace, &t0, &t2, row, start_col + FP12_MUL_X_CALC_OFFSET);
    }

    let t3 = c0+c1;
    for row in start_row..end_row+1 {
        fill_trace_addition_with_reduction_fp6(trace, &c0, &c1, row, start_col + FP12_MUL_T3_CALC_OFFSET);
    }
    let t4 = r0+r1;
    for row in start_row..end_row+1 {
        fill_trace_addition_with_reduction_fp6(trace, &r0, &r1, row, start_col + FP12_MUL_T4_CALC_OFFSET);
    }
    let t5 = t3*t4;
    fill_trace_fp6_multiplication(trace, &t3, &t4, start_row, end_row, start_col + FP12_MUL_T5_CALC_OFFSET);
    let t6 = t5-t0;
    for row in start_row..end_row+1 {
        fill_trace_subtraction_with_reduction_fp6(trace, &t5, &t0, row, start_col + FP12_MUL_T6_CALC_OFFSET);
    }
    let _y = t6-t1;
    for row in start_row..end_row+1 {
        fill_trace_subtraction_with_reduction_fp6(trace, &t6, &t1, row, start_col + FP12_MUL_Y_CALC_OFFSET);
    }
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
    bit_selector: Option<P>,
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    for i in 0..12 {
        for j in 0..12 {
            yield_constr.constraint_transition(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i] -
                next_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i])
            );
        }
        for j in 0..2 {
            yield_constr.constraint_transition(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i] -
                next_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i])
            );
            yield_constr.constraint_transition(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i] -
                next_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i])
            );
            yield_constr.constraint_transition(
            bit_selector_val *
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
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_INPUT_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i])
            );
        }
        for j in 0..2 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_B0_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_B1_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i])
            );
        }
    }
    add_multiply_by_01_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_014_T0_CALC_OFFSET, bit_selector);

    // T1
    for i in 0..12 {
        for j in 0..6 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_INPUT_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i + 24*3])
            );
        }
        for j in 0..2 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_B1_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i])
            );
        }
    }
    add_multiply_by_1_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_014_T1_CALC_OFFSET, bit_selector);

    // T2
    for j in 0..2 {
        let (x_offset, yz_offset) = if j==0 {
            (FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET, Z1_REDUCE_OFFSET)
        } else {
            (FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET, Z2_REDUCE_OFFSET)
        };
        for i in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12] -
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_X_CALC_OFFSET + x_offset + FP_SINGLE_REDUCED_OFFSET + i])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12 + 24] -
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_Y_CALC_OFFSET + yz_offset + REDUCED_OFFSET + i])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12 + 48] -
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_Z_CALC_OFFSET + yz_offset + REDUCED_OFFSET + i])
            );
        }
    }
    add_non_residue_multiplication_fp6_constraints(local_values, yield_constr, start_col + MULTIPLY_BY_014_T2_CALC_OFFSET, bit_selector);

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
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + x_offset + i])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + y_offset + FP_SINGLE_REDUCED_OFFSET + i])
            );
        }
    }
    add_addition_with_reduction_constranints_fp6(local_values, yield_constr, start_col + MULTIPLY_BY_014_X_CALC_OFFSET, bit_selector);

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
            bit_selector_val *
                    local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                    (local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                    local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*24 + k*12 + i])
                );
                yield_constr.constraint(
            bit_selector_val *
                    local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                    (local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] -
                    local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*24 + k*12 + i + 24*3])
                );
            }
        }
    }
    add_addition_with_reduction_constranints_fp6(local_values, yield_constr, start_col + MULTIPLY_BY_014_T3_CALC_OFFSET, bit_selector);

    // T4
    for j in 0..2 {
        let addition_offset = if j==0 {
            FP2_ADDITION_0_OFFSET
        } else {
            FP2_ADDITION_1_OFFSET
        };
        for i in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i])
            );
        }
    }
    add_addition_with_reduction_constranints(local_values, yield_constr, start_col + MULTIPLY_BY_014_T4_CALC_OFFSET, bit_selector);

    // T5
    for i in 0..12 {
        for j in 0..6 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_INPUT_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i])
            );
        }
        for j in 0..2 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_B0_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_B1_OFFSET + j*12 + i] -
                local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i])
            );
        }
    }
    add_multiply_by_01_constraints(local_values, next_values, yield_constr, start_col + MULTIPLY_BY_014_T5_CALC_OFFSET, bit_selector);

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
            bit_selector_val *
                    local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                    (local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                    local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + input_offset + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*k + FP_SINGLE_REDUCED_OFFSET + i])
                );
                yield_constr.constraint(
            bit_selector_val *
                    local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_CHECK_OFFSET] *
                    (local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_Y_OFFSET + i] -
                    local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + input_offset + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*k + FP_SINGLE_REDUCED_OFFSET + i])
                );
            }
        }
    }
    add_subtraction_with_reduction_constranints_fp6(local_values, yield_constr, start_col + MULTIPLY_BY_014_T6_CALC_OFFSET, bit_selector);

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
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_CHECK_OFFSET] *
                (local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_Y_OFFSET + i] -
                local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + input_offset + i])
            );
        }
    }
    add_subtraction_with_reduction_constranints_fp6(local_values, yield_constr, start_col + MULTIPLY_BY_014_Y_CALC_OFFSET, bit_selector);
}

pub fn add_multiply_by_014_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    next_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
){
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));

    for i in 0..12 {
        let mul_tmp = local_values[start_col + MULTIPLY_BY_014_SELECTOR_OFFSET];
        for j in 0..12 {
            let sub_tmp = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i] , next_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i]);
            let c = builder.mul_extension(sub_tmp, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c);
            yield_constr.constraint_transition(builder, c);
        }
        for j in 0..2 {
            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i] , next_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint_transition(builder, c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i] , next_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i]);
            let c2 = builder.mul_extension(sub_tmp2, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint_transition(builder, c);

            let sub_tmp3 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i] , next_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i]);
            let c3 = builder.mul_extension(sub_tmp3, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c3);
            yield_constr.constraint_transition(builder, c);
        }
    }

    // T0
    for i in 0..12 {
        let mul_tmp =  local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET];
        for j in 0..6 {
            let sub_tmp = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_INPUT_OFFSET + j*12 + i] , local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i]);
            let c = builder.mul_extension(sub_tmp, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c);
            yield_constr.constraint(builder,c);
        }
        for j in 0..2{
            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_B0_OFFSET + j*12 + i] , local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + MULTIPLY_BY_01_B1_OFFSET + j*12 + i] , local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i]);
            let c2 = builder.mul_extension(sub_tmp2, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_multiply_by_01_constraints_ext_circuit(builder, yield_constr, local_values, next_values,start_col + MULTIPLY_BY_014_T0_CALC_OFFSET, bit_selector);

    // T1
    for i in 0..12 {
        let mul_tmp = local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_SELECTOR_OFFSET];
        for j in 0..6{
            let sub_tmp = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_INPUT_OFFSET + j*12 + i] , local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*12 + i + 24*3]);
            let c = builder.mul_extension(sub_tmp, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c);
            yield_constr.constraint(builder,c);
        }
        for j in 0..2{
            let sub_tmp = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_B1_OFFSET + j*12 + i] , local_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i]);
            let c = builder.mul_extension(sub_tmp, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c);
            yield_constr.constraint(builder,c);
        }
    }
    add_multiply_by_1_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + MULTIPLY_BY_014_T1_CALC_OFFSET, bit_selector);

    // T2
    for j in 0..2 {
        let (x_offset, yz_offset) = if j==0 {
            (FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET, Z1_REDUCE_OFFSET)
        } else {
            (FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET, Z2_REDUCE_OFFSET)
        };
        for i in 0..12 {
            let mul_tmp = local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET];

            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12] , local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_X_CALC_OFFSET + x_offset + FP_SINGLE_REDUCED_OFFSET + i]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12 + 24] , local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_Y_CALC_OFFSET + yz_offset + REDUCED_OFFSET + i]);
            let c2 = builder.mul_extension(sub_tmp2, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);

            let sub_tmp3 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i + j*12 + 48] , local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + MULTIPLY_BY_1_Z_CALC_OFFSET + yz_offset + REDUCED_OFFSET + i]);
            let c3 = builder.mul_extension(sub_tmp3, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c3);
            yield_constr.constraint(builder,c);
        }
    }
    add_non_residue_multiplication_fp6_constraints_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_BY_014_T2_CALC_OFFSET, bit_selector);

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
            let mul_tmp = local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET];

            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_T2_CALC_OFFSET + x_offset + i]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_X_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + y_offset + FP_SINGLE_REDUCED_OFFSET + i]);
            let c2 = builder.mul_extension(sub_tmp2, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_addition_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_BY_014_X_CALC_OFFSET, bit_selector);

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
                let mul_tmp = local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET];

                let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*24 + k*12 + i]);
                let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
                let c = builder.mul_extension(bit_selector_val, c1);
                yield_constr.constraint(builder,c);

                let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_INPUT_OFFSET + j*24 + k*12 + i + 24*3]);
                let c2 = builder.mul_extension(sub_tmp2, mul_tmp);
                let c = builder.mul_extension(bit_selector_val, c2);
                yield_constr.constraint(builder,c);
            }
        }
    }
    add_addition_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_BY_014_T3_CALC_OFFSET, bit_selector);

    // T4
    for j in 0..2 {
        let addition_offset = if j==0 {
            FP2_ADDITION_0_OFFSET
        } else {
            FP2_ADDITION_1_OFFSET
        };
        for i in 0..12 {
            let mul_tmp = local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET];

            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_O1_OFFSET + j*12 + i]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + addition_offset + FP_ADDITION_Y_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_O4_OFFSET + j*12 + i]);
            let c2 = builder.mul_extension(sub_tmp2, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_addition_with_reduction_constraints_ext_circuit(builder, yield_constr, local_values,start_col + MULTIPLY_BY_014_T4_CALC_OFFSET, bit_selector);

    // T5
    for i in 0..12 {
        let mul_tmp =  local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_SELECTOR_OFFSET];
        for j in 0..6{
            let sub_tmp = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_INPUT_OFFSET + j*12 + i] , local_values[start_col + MULTIPLY_BY_014_T3_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i]);
            let c = builder.mul_extension(sub_tmp, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c);
            yield_constr.constraint(builder,c);
        }
        for j in 0..2{
            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_B0_OFFSET + j*12 + i] , local_values[start_col + MULTIPLY_BY_014_O0_OFFSET + j*12 + i]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + MULTIPLY_BY_01_B1_OFFSET + j*12 + i] , local_values[start_col + MULTIPLY_BY_014_T4_CALC_OFFSET + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i]);
            let c2 = builder.mul_extension(sub_tmp2, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_multiply_by_01_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + MULTIPLY_BY_014_T5_CALC_OFFSET, bit_selector);

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
                let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_T5_CALC_OFFSET + input_offset + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*k + FP_SINGLE_REDUCED_OFFSET + i]);
                let c1 = builder.mul_extension(sub_tmp1, local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET]);
                let c = builder.mul_extension(bit_selector_val, c1);
                yield_constr.constraint(builder,c);
                
                let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_Y_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_T0_CALC_OFFSET + input_offset + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*k + FP_SINGLE_REDUCED_OFFSET + i]);
                let c2 = builder.mul_extension(sub_tmp2, local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_CHECK_OFFSET]);
                let c = builder.mul_extension(bit_selector_val, c2);
                yield_constr.constraint(builder,c);
            }
        }
    }
    add_subtraction_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_BY_014_T6_CALC_OFFSET, bit_selector);

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
            let sub_tmp1 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + addition_offset + FP_ADDITION_X_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i]);
            let c1 = builder.mul_extension(sub_tmp1, local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + addition_offset + FP_ADDITION_CHECK_OFFSET]);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_Y_OFFSET + i] , local_values[start_col + MULTIPLY_BY_014_T1_CALC_OFFSET + input_offset + i]);
            let c2 = builder.mul_extension(sub_tmp2, local_values[start_col + MULTIPLY_BY_014_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + subtraction_offset + FP_SUBTRACTION_CHECK_OFFSET]);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_subtraction_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values, start_col + MULTIPLY_BY_014_Y_CALC_OFFSET, bit_selector);
}

pub fn add_fp12_multiplication_constraints<F: RichField + Extendable<D>,
    const D: usize,
    FE,
    P,
    const D2: usize,
    >(
    local_values: &[P],
    next_values: &[P],
    yield_constr: &mut ConstraintConsumer<P>,
    start_col: usize,
    bit_selector: Option<P>,
) where
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    let bit_selector_val = bit_selector.unwrap_or(P::ONES);

    for i in 0..24*3*2 {
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP12_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i] - next_values[start_col + FP12_MUL_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint_transition(
            bit_selector_val *
            local_values[start_col + FP12_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i] - next_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i])
        );
    }

    // T0
    for i in 0..24*3 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP12_MUL_T0_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP12_MUL_T0_CALC_OFFSET + FP6_MUL_X_INPUT_OFFSET + i] - local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i])
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP12_MUL_T0_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP12_MUL_T0_CALC_OFFSET + FP6_MUL_Y_INPUT_OFFSET + i] - local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i])
        );
    }
    add_fp6_multiplication_constraints(local_values, next_values, yield_constr, start_col + FP12_MUL_T0_CALC_OFFSET, bit_selector);

    // T1
    for i in 0..24*3 {
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP12_MUL_T1_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP12_MUL_T1_CALC_OFFSET + FP6_MUL_X_INPUT_OFFSET + i] - local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i + 24*3])
        );
        yield_constr.constraint(
            bit_selector_val *
            local_values[start_col + FP12_MUL_T1_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET] *
            (local_values[start_col + FP12_MUL_T1_CALC_OFFSET + FP6_MUL_Y_INPUT_OFFSET + i] - local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i + 24*3])
        );
    }
    add_fp6_multiplication_constraints(local_values, next_values, yield_constr, start_col + FP12_MUL_T1_CALC_OFFSET, bit_selector);
    
    // T2
    for i in 0..6 {
        let fp2_offset = if i < 2 {
            FP6_MUL_X_CALC_OFFSET
        } else if i < 4 {
            FP6_MUL_Y_CALC_OFFSET
        } else {
            FP6_MUL_Z_CALC_OFFSET
        };
        let fp_offset = i%2;
        for j in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i*12 + j] - 
                local_values[start_col + FP12_MUL_T1_CALC_OFFSET + fp2_offset + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*fp_offset + FP_SINGLE_REDUCED_OFFSET + j])
            );
        }
    }
    add_non_residue_multiplication_fp6_constraints(local_values, yield_constr, start_col + FP12_MUL_T2_CALC_OFFSET, bit_selector);

    // X
    for i in 0..6 {
        let (fp2_offset_l, fp2_offset_r) = if i < 2 {
            (FP6_ADDITION_0_OFFSET, FP6_MUL_X_CALC_OFFSET)
        } else if i < 4 {
            (FP6_ADDITION_1_OFFSET, FP6_MUL_Y_CALC_OFFSET)
        } else {
            (FP6_ADDITION_2_OFFSET, FP6_MUL_Z_CALC_OFFSET)
        };
        let (fp_offset, num_redn) = if i%2 == 0 {
            (FP2_ADDITION_0_OFFSET, 0)
        } else {
            (FP2_ADDITION_1_OFFSET, 1)
        };
        for j in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_X_OFFSET + j] -
                local_values[start_col + FP12_MUL_T0_CALC_OFFSET + fp2_offset_r + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*num_redn + FP_SINGLE_REDUCED_OFFSET + j])
            );
            if i < 2 {
                let y_offset = if i==0 {
                    FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET
                } else {
                    FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET
                };
                yield_constr.constraint(
            bit_selector_val *
                    local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_CHECK_OFFSET] *
                    (local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_Y_OFFSET + j] -
                    local_values[start_col + FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_C2 + y_offset + FP_SINGLE_REDUCED_OFFSET + j])
                )
            } else {
                yield_constr.constraint(
            bit_selector_val *
                    local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_CHECK_OFFSET] *
                    (local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_Y_OFFSET + j] -
                    local_values[start_col + FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + (i-2)*12 + j])
                );
            }
        }
    }
    add_addition_with_reduction_constranints_fp6(local_values, yield_constr, start_col + FP12_MUL_X_CALC_OFFSET, bit_selector);

    // T3
    for i in 0..6 {
        let fp2_offset = if i < 2 {
            FP6_ADDITION_0_OFFSET
        } else if i < 4 {
            FP6_ADDITION_1_OFFSET
        } else {
            FP6_ADDITION_2_OFFSET
        };
        let fp_offset = if i%2 == 0 {
            FP2_ADDITION_0_OFFSET
        } else {
            FP2_ADDITION_1_OFFSET
        };
        for j in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T3_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_T3_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_X_OFFSET + j] -
                local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i*12 + j])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T3_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_T3_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_Y_OFFSET + j] -
                local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i*12 + j + 24*3])
            );
        }
    }
    add_addition_with_reduction_constranints_fp6(local_values, yield_constr, start_col + FP12_MUL_T3_CALC_OFFSET, bit_selector);

    // T4
    for i in 0..6 {
        let fp2_offset = if i < 2 {
            FP6_ADDITION_0_OFFSET
        } else if i < 4 {
            FP6_ADDITION_1_OFFSET
        } else {
            FP6_ADDITION_2_OFFSET
        };
        let fp_offset = if i%2 == 0 {
            FP2_ADDITION_0_OFFSET
        } else {
            FP2_ADDITION_1_OFFSET
        };
        for j in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T4_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_T4_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_X_OFFSET + j] -
                local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i*12 + j])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T4_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_T4_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_Y_OFFSET + j] -
                local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i*12 + j + 24*3])
            );
        }
    }
    add_addition_with_reduction_constranints_fp6(local_values, yield_constr, start_col + FP12_MUL_T4_CALC_OFFSET, bit_selector);

    // T5
    for i in 0..6 {
        for j in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T5_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET] *
                (local_values[start_col + FP12_MUL_T5_CALC_OFFSET + FP6_MUL_X_INPUT_OFFSET + i*12 + j] -
                local_values[start_col + FP12_MUL_T3_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i + FP_SINGLE_REDUCED_OFFSET + j])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T5_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET] *
                (local_values[start_col + FP12_MUL_T5_CALC_OFFSET + FP6_MUL_Y_INPUT_OFFSET + i*12 + j] -
                local_values[start_col + FP12_MUL_T4_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i + FP_SINGLE_REDUCED_OFFSET + j])
            );
        }
    }
    add_fp6_multiplication_constraints(local_values, next_values, yield_constr, start_col + FP12_MUL_T5_CALC_OFFSET, bit_selector);

    // T6
    for i in 0..6 {
        let (fp2_offset_lx, fp2_offset_ly, fp2_offset_r) = if i < 2 {
            (FP6_ADDITION_0_OFFSET, FP6_SUBTRACTION_0_OFFSET, FP6_MUL_X_CALC_OFFSET)
        } else if i < 4 {
            (FP6_ADDITION_1_OFFSET, FP6_SUBTRACTION_1_OFFSET, FP6_MUL_Y_CALC_OFFSET)
        } else {
            (FP6_ADDITION_2_OFFSET, FP6_SUBTRACTION_2_OFFSET, FP6_MUL_Z_CALC_OFFSET)
        };
        let (fp_offset_x, fp_offset_y, num_redn) = if i%2 == 0 {
            (FP2_ADDITION_0_OFFSET, FP2_SUBTRACTION_0_OFFSET, 0)
        } else {
            (FP2_ADDITION_1_OFFSET, FP2_SUBTRACTION_1_OFFSET, 1)
        };
        for j in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T6_CALC_OFFSET + fp2_offset_lx + fp_offset_x + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_T6_CALC_OFFSET + fp2_offset_lx + fp_offset_x + FP_ADDITION_X_OFFSET + j] -
                local_values[start_col + FP12_MUL_T5_CALC_OFFSET + fp2_offset_r + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*num_redn + FP_SINGLE_REDUCED_OFFSET + j])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + fp2_offset_ly + fp_offset_y + FP_SUBTRACTION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + fp2_offset_ly + fp_offset_y + FP_SUBTRACTION_Y_OFFSET + j] -
                local_values[start_col + FP12_MUL_T0_CALC_OFFSET + fp2_offset_r + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*num_redn + FP_SINGLE_REDUCED_OFFSET + j])
            );
        }
    }
    add_subtraction_with_reduction_constranints_fp6(local_values, yield_constr, start_col + FP12_MUL_T6_CALC_OFFSET, bit_selector);

    // Y
    for i in 0..6 {
        let (fp2_offset_lx, fp2_offset_ly, fp2_offset_r) = if i < 2 {
            (FP6_ADDITION_0_OFFSET, FP6_SUBTRACTION_0_OFFSET, FP6_MUL_X_CALC_OFFSET)
        } else if i < 4 {
            (FP6_ADDITION_1_OFFSET, FP6_SUBTRACTION_1_OFFSET, FP6_MUL_Y_CALC_OFFSET)
        } else {
            (FP6_ADDITION_2_OFFSET, FP6_SUBTRACTION_2_OFFSET, FP6_MUL_Z_CALC_OFFSET)
        };
        let (fp_offset_x, fp_offset_y, num_redn) = if i%2 == 0 {
            (FP2_ADDITION_0_OFFSET, FP2_SUBTRACTION_0_OFFSET, 0)
        } else {
            (FP2_ADDITION_1_OFFSET, FP2_SUBTRACTION_1_OFFSET, 1)
        };
        for j in 0..12 {
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_Y_CALC_OFFSET + fp2_offset_lx + fp_offset_x + FP_ADDITION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_Y_CALC_OFFSET + fp2_offset_lx + fp_offset_x + FP_ADDITION_X_OFFSET + j] -
                local_values[start_col + FP12_MUL_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i + FP_SINGLE_REDUCED_OFFSET + j])
            );
            yield_constr.constraint(
            bit_selector_val *
                local_values[start_col + FP12_MUL_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + fp2_offset_ly + fp_offset_y + FP_SUBTRACTION_CHECK_OFFSET] *
                (local_values[start_col + FP12_MUL_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + fp2_offset_ly + fp_offset_y + FP_SUBTRACTION_Y_OFFSET + j] -
                local_values[start_col + FP12_MUL_T1_CALC_OFFSET + fp2_offset_r + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*num_redn + FP_SINGLE_REDUCED_OFFSET + j])
            );
        }
    }
    add_subtraction_with_reduction_constranints_fp6(local_values, yield_constr, start_col + FP12_MUL_Y_CALC_OFFSET, bit_selector);
}

pub fn add_fp12_multiplication_constraints_ext_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    local_values: &[ExtensionTarget<D>],
    next_values: &[ExtensionTarget<D>],
    start_col: usize,
    bit_selector: Option<ExtensionTarget<D>>,
){
    let bit_selector_val = bit_selector.unwrap_or(builder.constant_extension(F::Extension::ONE));

    for i in 0..24*3*2 {
        let mul_tmp = local_values[start_col + FP12_MUL_SELECTOR_OFFSET];
        
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i] , next_values[start_col + FP12_MUL_X_INPUT_OFFSET + i]);
        let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
        let c = builder.mul_extension(bit_selector_val, c1);
        yield_constr.constraint_transition(builder, c);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i], next_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i]);
        let c2 = builder.mul_extension(sub_tmp2,mul_tmp);
        let c = builder.mul_extension(bit_selector_val, c2);
        yield_constr.constraint_transition(builder, c);
    }

    // T0
    for i in 0..24*3 {
        let mul_tmp = local_values[start_col + FP12_MUL_T0_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET];

        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP12_MUL_T0_CALC_OFFSET + FP6_MUL_X_INPUT_OFFSET + i] , local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i]);
        let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
        let c = builder.mul_extension(bit_selector_val, c1);
        yield_constr.constraint(builder,c);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP12_MUL_T0_CALC_OFFSET + FP6_MUL_Y_INPUT_OFFSET + i] , local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i]);
        let c2 = builder.mul_extension(sub_tmp2,mul_tmp);
        let c = builder.mul_extension(bit_selector_val, c2);
        yield_constr.constraint(builder,c);
    }
    add_fp6_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + FP12_MUL_T0_CALC_OFFSET, bit_selector);


    // T1 
    for i in 0..24*3 {
        let mul_tmp = local_values[start_col + FP12_MUL_T1_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET];
        
        let sub_tmp1 = builder.sub_extension(local_values[start_col + FP12_MUL_T1_CALC_OFFSET + FP6_MUL_X_INPUT_OFFSET + i] , local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i + 24*3]);
        let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
        let c = builder.mul_extension(bit_selector_val, c1);
        yield_constr.constraint(builder,c);

        let sub_tmp2 = builder.sub_extension(local_values[start_col + FP12_MUL_T1_CALC_OFFSET + FP6_MUL_Y_INPUT_OFFSET + i] , local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i + 24*3]);
        let c2 = builder.mul_extension(sub_tmp2,mul_tmp);
        let c = builder.mul_extension(bit_selector_val, c2);
        yield_constr.constraint(builder,c);
    }
    add_fp6_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + FP12_MUL_T1_CALC_OFFSET, bit_selector);

    // T2
    for i in 0..6 {
        let fp2_offset = if i < 2 {
            FP6_MUL_X_CALC_OFFSET
        } else if i < 4 {
            FP6_MUL_Y_CALC_OFFSET
        } else {
            FP6_MUL_Z_CALC_OFFSET
        };
        let fp_offset = i%2;
        for j in 0..12 {
            let sub_tmp = builder.sub_extension(local_values[start_col + FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + i*12 + j] , local_values[start_col + FP12_MUL_T1_CALC_OFFSET + fp2_offset + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*fp_offset + FP_SINGLE_REDUCED_OFFSET + j]);
            let c = builder.mul_extension(sub_tmp, local_values[start_col + FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_CHECK_OFFSET]);
            let c = builder.mul_extension(bit_selector_val,c);
            yield_constr.constraint(builder,c);
        }
    }
    add_non_residue_multiplication_fp6_constraints_ext_circuit(builder, yield_constr, local_values,start_col + FP12_MUL_T2_CALC_OFFSET, bit_selector);

    // X
    for i in 0..6 {
        let (fp2_offset_l, fp2_offset_r) = if i < 2 {
            (FP6_ADDITION_0_OFFSET, FP6_MUL_X_CALC_OFFSET)
        } else if i < 4 {
            (FP6_ADDITION_1_OFFSET, FP6_MUL_Y_CALC_OFFSET)
        } else {
            (FP6_ADDITION_2_OFFSET, FP6_MUL_Z_CALC_OFFSET)
        };
        let (fp_offset, num_redn) = if i%2 == 0 {
            (FP2_ADDITION_0_OFFSET, 0)
        } else {
            (FP2_ADDITION_1_OFFSET, 1)
        };
        for j in 0..12 {
            let mul_tmp = local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_CHECK_OFFSET];

            let sub_tmp = builder.sub_extension(local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_X_OFFSET + j] , local_values[start_col + FP12_MUL_T0_CALC_OFFSET + fp2_offset_r + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*num_redn + FP_SINGLE_REDUCED_OFFSET + j]);
            let c = builder.mul_extension(sub_tmp, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c);
            yield_constr.constraint(builder,c);

            if i < 2 {
                let y_offset = if i==0 {
                    FP2_NON_RESIDUE_MUL_Z0_REDUCE_OFFSET
                } else {
                    FP2_NON_RESIDUE_MUL_Z1_REDUCE_OFFSET
                };

                let sub_tmp = builder.sub_extension(local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_Y_OFFSET + j] , local_values[start_col + FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_C2 + y_offset + FP_SINGLE_REDUCED_OFFSET + j]);
                let c = builder.mul_extension(sub_tmp, mul_tmp);
                let c = builder.mul_extension(bit_selector_val, c);
                yield_constr.constraint(builder,c);
            }
            else{
                let sub_tmp = builder.sub_extension(local_values[start_col + FP12_MUL_X_CALC_OFFSET + fp2_offset_l + fp_offset + FP_ADDITION_Y_OFFSET + j] , local_values[start_col + FP12_MUL_T2_CALC_OFFSET + FP6_NON_RESIDUE_MUL_INPUT_OFFSET + (i-2)*12 + j]);
                let c = builder.mul_extension(sub_tmp, mul_tmp);
                let c = builder.mul_extension(bit_selector_val, c);
                yield_constr.constraint(builder,c);
            }
        }
    }
    add_addition_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values, start_col + FP12_MUL_X_CALC_OFFSET, bit_selector);

    // T3
    for i in 0..6 {
        let fp2_offset = if i < 2 {
            FP6_ADDITION_0_OFFSET
        } else if i < 4 {
            FP6_ADDITION_1_OFFSET
        } else {
            FP6_ADDITION_2_OFFSET
        };
        let fp_offset = if i%2 == 0 {
            FP2_ADDITION_0_OFFSET
        } else {
            FP2_ADDITION_1_OFFSET
        };
        for j in 0..12 {
            let mul_tmp = local_values[start_col + FP12_MUL_T3_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_CHECK_OFFSET];

            let sub_tmp1 = builder.sub_extension(local_values[start_col + FP12_MUL_T3_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_X_OFFSET + j] , local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i*12 + j]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + FP12_MUL_T3_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_Y_OFFSET + j] , local_values[start_col + FP12_MUL_X_INPUT_OFFSET + i*12 + j + 24*3]);
            let c2 = builder.mul_extension(sub_tmp2,mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_addition_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values, start_col + FP12_MUL_T3_CALC_OFFSET, bit_selector);

    // T4
    for i in 0..6 {
        let fp2_offset = if i < 2 {
            FP6_ADDITION_0_OFFSET
        } else if i < 4 {
            FP6_ADDITION_1_OFFSET
        } else {
            FP6_ADDITION_2_OFFSET
        };
        let fp_offset = if i%2 == 0 {
            FP2_ADDITION_0_OFFSET
        } else {
            FP2_ADDITION_1_OFFSET
        };
        for j in 0..12 {
            let mul_tmp = local_values[start_col + FP12_MUL_T4_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_CHECK_OFFSET];
            
            let sub_tmp1 = builder.sub_extension(local_values[start_col + FP12_MUL_T4_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_X_OFFSET + j] , local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i*12 + j]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + FP12_MUL_T4_CALC_OFFSET + fp2_offset + fp_offset + FP_ADDITION_Y_OFFSET + j] , local_values[start_col + FP12_MUL_Y_INPUT_OFFSET + i*12 + j + 24*3]);
            let c2 = builder.mul_extension(sub_tmp2,mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_addition_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values,start_col + FP12_MUL_T4_CALC_OFFSET, bit_selector);

    // T5 
    for i in 0..6 {
        for j in 0..12{
            let mul_tmp = local_values[start_col + FP12_MUL_T5_CALC_OFFSET + FP6_MUL_SELECTOR_OFFSET];
            
            let sub_tmp1 = builder.sub_extension(local_values[start_col + FP12_MUL_T5_CALC_OFFSET + FP6_MUL_X_INPUT_OFFSET + i*12 + j] , local_values[start_col + FP12_MUL_T3_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i + FP_SINGLE_REDUCED_OFFSET + j]);
            let c1 = builder.mul_extension(sub_tmp1, mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + FP12_MUL_T5_CALC_OFFSET + FP6_MUL_Y_INPUT_OFFSET + i*12 + j] , local_values[start_col + FP12_MUL_T4_CALC_OFFSET + FP6_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i + FP_SINGLE_REDUCED_OFFSET + j]);
            let c2 = builder.mul_extension(sub_tmp2,mul_tmp);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_fp6_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, start_col + FP12_MUL_T5_CALC_OFFSET, bit_selector);

    // T6
    for i in 0..6 {
        let (fp2_offset_lx, fp2_offset_ly, fp2_offset_r) = if i < 2 {
            (FP6_ADDITION_0_OFFSET, FP6_SUBTRACTION_0_OFFSET, FP6_MUL_X_CALC_OFFSET)
        } else if i < 4 {
            (FP6_ADDITION_1_OFFSET, FP6_SUBTRACTION_1_OFFSET, FP6_MUL_Y_CALC_OFFSET)
        } else {
            (FP6_ADDITION_2_OFFSET, FP6_SUBTRACTION_2_OFFSET, FP6_MUL_Z_CALC_OFFSET)
        };
        let (fp_offset_x, fp_offset_y, num_redn) = if i%2 == 0 {
            (FP2_ADDITION_0_OFFSET, FP2_SUBTRACTION_0_OFFSET, 0)
        } else {
            (FP2_ADDITION_1_OFFSET, FP2_SUBTRACTION_1_OFFSET, 1)
        };
        for j in 0..12 {
            let sub_tmp1 = builder.sub_extension(local_values[start_col + FP12_MUL_T6_CALC_OFFSET + fp2_offset_lx + fp_offset_x + FP_ADDITION_X_OFFSET + j] , local_values[start_col + FP12_MUL_T5_CALC_OFFSET + fp2_offset_r + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*num_redn + FP_SINGLE_REDUCED_OFFSET + j]);
            let c1 = builder.mul_extension(sub_tmp1, local_values[start_col + FP12_MUL_T6_CALC_OFFSET + fp2_offset_lx + fp_offset_x + FP_ADDITION_CHECK_OFFSET]);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + FP12_MUL_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + fp2_offset_ly + fp_offset_y + FP_SUBTRACTION_Y_OFFSET + j] , local_values[start_col + FP12_MUL_T0_CALC_OFFSET + fp2_offset_r + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*num_redn + FP_SINGLE_REDUCED_OFFSET + j]);
            let c2 = builder.mul_extension(sub_tmp2, local_values[start_col + FP12_MUL_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + fp2_offset_ly + fp_offset_y + FP_SUBTRACTION_CHECK_OFFSET]);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_subtraction_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values, start_col + FP12_MUL_T6_CALC_OFFSET, bit_selector);

    // Y
    for i in 0..6 {
        let (fp2_offset_lx, fp2_offset_ly, fp2_offset_r) = if i < 2 {
            (FP6_ADDITION_0_OFFSET, FP6_SUBTRACTION_0_OFFSET, FP6_MUL_X_CALC_OFFSET)
        } else if i < 4 {
            (FP6_ADDITION_1_OFFSET, FP6_SUBTRACTION_1_OFFSET, FP6_MUL_Y_CALC_OFFSET)
        } else {
            (FP6_ADDITION_2_OFFSET, FP6_SUBTRACTION_2_OFFSET, FP6_MUL_Z_CALC_OFFSET)
        };
        let (fp_offset_x, fp_offset_y, num_redn) = if i%2 == 0 {
            (FP2_ADDITION_0_OFFSET, FP2_SUBTRACTION_0_OFFSET, 0)
        } else {
            (FP2_ADDITION_1_OFFSET, FP2_SUBTRACTION_1_OFFSET, 1)
        };
        for j in 0..12 {
            let sub_tmp1 = builder.sub_extension(local_values[start_col + FP12_MUL_Y_CALC_OFFSET + fp2_offset_lx + fp_offset_x + FP_ADDITION_X_OFFSET + j] , local_values[start_col + FP12_MUL_T6_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*i + FP_SINGLE_REDUCED_OFFSET + j]);
            let c1 = builder.mul_extension(sub_tmp1, local_values[start_col + FP12_MUL_Y_CALC_OFFSET + fp2_offset_lx + fp_offset_x + FP_ADDITION_CHECK_OFFSET]);
            let c = builder.mul_extension(bit_selector_val, c1);
            yield_constr.constraint(builder,c);

            let sub_tmp2 = builder.sub_extension(local_values[start_col + FP12_MUL_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + fp2_offset_ly + fp_offset_y + FP_SUBTRACTION_Y_OFFSET + j] , local_values[start_col + FP12_MUL_T1_CALC_OFFSET + fp2_offset_r + FP2_ADDITION_TOTAL + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*num_redn + FP_SINGLE_REDUCED_OFFSET + j]);
            let c2 = builder.mul_extension(sub_tmp2, local_values[start_col + FP12_MUL_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + fp2_offset_ly + fp_offset_y + FP_SUBTRACTION_CHECK_OFFSET]);
            let c = builder.mul_extension(bit_selector_val, c2);
            yield_constr.constraint(builder,c);
        }
    }
    add_subtraction_with_reduction_constraints_fp6_ext_circuit(builder, yield_constr, local_values, start_col + FP12_MUL_Y_CALC_OFFSET, bit_selector);
}
