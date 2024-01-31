use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
    },
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
};
use starky::{
    constraint_consumer::ConstraintConsumer,
    evaluation_frame::{StarkEvaluationFrame, StarkFrame},
    stark::Stark,
};

use crate::native::Fp12;

use crate::fp::*;
use crate::fp6::*;
use crate::fp12::*;

pub const TOTAL_COLUMNS: usize = FP12_MUL_TOTAL_COLUMNS;
pub const COLUMNS: usize = TOTAL_COLUMNS;

pub const PIS_INPUT_X_OFFSET: usize = 0;
pub const PIS_INPUT_Y_OFFSET: usize = PIS_INPUT_X_OFFSET + 24*3*2;
pub const PIS_OUTPUT_OFFSET: usize = PIS_INPUT_Y_OFFSET + 24*3*2;
pub const PUBLIC_INPUTS: usize = PIS_OUTPUT_OFFSET + 24*3*2;


#[derive(Clone, Copy)]
pub struct FP12MulStark<F: RichField + Extendable<D>, const D: usize> {
    num_rows: usize,
    _f: std::marker::PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> FP12MulStark<F, D> {
    pub fn new(num_rows: usize) -> Self {
        Self {
            num_rows,
            _f: std::marker::PhantomData,
        }
    }

    pub fn generate_trace(&self, x: Fp12, y: Fp12) -> Vec<[F; TOTAL_COLUMNS]> {
        let mut trace = vec![[F::ZERO; TOTAL_COLUMNS]; self.num_rows];
        fill_trace_fp12_multiplication(&mut trace, &x, &y, 0, 11, 0);
        trace
    }
}

// Implement constraint generator
impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for FP12MulStark<F, D> {
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
        for i in 0..24*3*2 {
            yield_constr.constraint(
                local_values[FP12_MUL_SELECTOR_OFFSET] *
                (local_values[FP12_MUL_X_INPUT_OFFSET + i] - public_inputs[PIS_INPUT_X_OFFSET + i])
            );
            yield_constr.constraint(
                local_values[FP12_MUL_SELECTOR_OFFSET] *
                (local_values[FP12_MUL_Y_INPUT_OFFSET + i] - public_inputs[PIS_INPUT_Y_OFFSET + i])
            );
        }

        for i in 0..12 {
            for j in 0..6 {
                for k in 0..2 {
                    let x_y = if k == 0 {
                        FP12_MUL_X_CALC_OFFSET + FP6_ADDITION_TOTAL
                    } else {
                        FP12_MUL_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL
                    };
                    let offset = x_y + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i;
                    yield_constr.constraint(
                        local_values[FP12_MUL_SELECTOR_OFFSET] *
                        (local_values[offset] - public_inputs[PIS_OUTPUT_OFFSET + k*24*3 + j*12 + i])
                    );
                }
            }
        }
        add_fp12_multiplication_constraints(local_values, next_values, yield_constr, 0, None);
    }

    type EvaluationFrameTarget =
        StarkFrame<ExtensionTarget<D>, ExtensionTarget<D>, COLUMNS, PUBLIC_INPUTS>;

    fn eval_ext_circuit(
        &self,
        builder: &mut plonky2::plonk::circuit_builder::CircuitBuilder<F, D>,
        vars: &Self::EvaluationFrameTarget,
        yield_constr: &mut starky::constraint_consumer::RecursiveConstraintConsumer<F, D>,
    ) {
        let local_values = vars.get_local_values();
        let next_values = vars.get_next_values();
        let public_inputs = vars.get_public_inputs();

        // ---
        for i in 0..24*3*2 {
            let c = builder.sub_extension(local_values[FP12_MUL_X_INPUT_OFFSET + i], public_inputs[PIS_INPUT_X_OFFSET + i]);
            let c = builder.mul_extension(local_values[FP12_MUL_SELECTOR_OFFSET], c);
            yield_constr.constraint(builder, c);
    
            let c = builder.sub_extension(local_values[FP12_MUL_Y_INPUT_OFFSET + i], public_inputs[PIS_INPUT_Y_OFFSET + i]);
            let c = builder.mul_extension(local_values[FP12_MUL_SELECTOR_OFFSET], c);
            yield_constr.constraint(builder, c);
        }
        for i in 0..12 {
            for j in 0..6 {
                for k in 0..2 {
                    let x_y = if k == 0 {
                        FP12_MUL_X_CALC_OFFSET + FP6_ADDITION_TOTAL
                    } else {
                        FP12_MUL_Y_CALC_OFFSET + FP6_ADDITION_TOTAL + FP6_SUBTRACTION_TOTAL
                    };
                    let offset = x_y + (FP_SINGLE_REDUCE_TOTAL + RANGE_CHECK_TOTAL)*j + FP_SINGLE_REDUCED_OFFSET + i;
                    let c = builder.sub_extension(local_values[offset], public_inputs[PIS_OUTPUT_OFFSET + k*24*3 + j*12 + i]);
                    let c = builder.mul_extension(local_values[FP12_MUL_SELECTOR_OFFSET], c);
                    yield_constr.constraint(builder, c);
                }
            }
        }
        add_fp12_multiplication_constraints_ext_circuit(builder, yield_constr, local_values, next_values, 0, None);
    }

    fn constraint_degree(&self) -> usize {
        3
    }
}
