use std::str::FromStr;

use num_bigint::BigUint;
use plonky2::{field::{types::Field, extension::Extendable, polynomial::PolynomialValues}, hash::hash_types::RichField, util::transpose};
use itertools::Itertools;
use crate::{layout::{G1_X_IDX, G1_Y_IDX, G2_X_1_IDX, G2_X_2_IDX, G2_Y_1_IDX, G2_Y_2_IDX, G2_Z_1_IDX, G2_Z_2_IDX, TOTAL_COLUMNS, X_INPUT_IDX, Y_INPUT_IDX, EVALUATION_IDX, XY_IDX, XY_CARRIES_IDX, SELECTOR, SHIFTED_XY, SUM, SUM_CARRIES, CONSTRAIN_ROW_IDX, LAST_ROW_IDX}, native::{modulus, get_negate, get_g2_invert, get_u32_carries, modulus_digits, Fp, mul_fp_without_reduction, get_u32_vec_from_literal_24, multiply_by_slice, get_u32_vec_from_literal, get_selector_bits_from_u32, add_u32_slices}};

#[derive(Clone)]
pub struct PairingStark<F: RichField + Extendable<D>, const D: usize> {
    pub trace: Vec<[F; TOTAL_COLUMNS]>,
    num_rows: usize,
}


impl<F: RichField + Extendable<D>, const D: usize> PairingStark<F, D> {

    const PI_INDEX_X0: usize = 0;
    const PI_INDEX_X1: usize = 0;

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

    pub fn generate_trace_1(&mut self, x: [u32; 12], y: [u32; 12]) -> Vec<[F; TOTAL_COLUMNS]>{
        let z = get_u32_vec_from_literal_24(BigUint::new(x.to_vec())*BigUint::new(y.to_vec()));
        let mut selector: u32 = 1;
        for row in 0..self.num_rows {
            for i in 0..12 {
                self.trace[row][X_INPUT_IDX+i] = F::from_canonical_u32(x[i]);
                self.trace[row][Y_INPUT_IDX+i] = F::from_canonical_u32(y[i]);
            }
            for i in 0..24 {
                self.trace[row][EVALUATION_IDX+i] = F::from_canonical_u32(z[i]);
            }
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
            prev_xy_sum = xy_sum.clone();
        }
        for i in 0..11 {
            self.trace[i][CONSTRAIN_ROW_IDX] = F::from_canonical_u32(1u32);
        }
        self.trace[11][LAST_ROW_IDX] = F::ONE;
        // for i in  0..self.num_rows-1 {
        //     // println!("{:?}", xy_sum[0] as u64 +( xy_sum_carry[0] as u64 * (1u64<<32) as u64) - xy_shifted[0] as u64 - prev_xy_sum[0] as u64 );
        //     println!("checks:: {:?}", self.trace[i][CONSTRAIN_ROW_IDX] * ( self.trace[i+1][SUM] +( self.trace[i+1][SUM_CARRIES] * F::from_canonical_u64(1<<32)) - self.trace[i+1][SHIFTED_XY]  - self.trace[i][SUM]));
        // }
        self.trace.clone()
    }

    // fill
    pub fn generate_trace(&mut self, g1: [[u32; 12]; 2], g2: [[u32; 12]; 6]) -> Vec<[F; TOTAL_COLUMNS]>{
        // * --- Assign row 0 --- *
        for i in 0..TOTAL_COLUMNS {
            for j in 0..12 {
                self.trace[0][G1_X_IDX+j] = F::from_canonical_u32(g1[0][j]);
                self.trace[0][G1_Y_IDX+j] = F::from_canonical_u32(g1[1][j]);

                self.trace[0][G2_X_1_IDX+j] = F::from_canonical_u32(g2[0][j]);
                self.trace[0][G2_X_2_IDX+j] = F::from_canonical_u32(g2[1][j]);
                self.trace[0][G2_Y_1_IDX+j] = F::from_canonical_u32(g2[2][j]);
                self.trace[0][G2_Y_2_IDX+j] = F::from_canonical_u32(g2[3][j]);
                self.trace[0][G2_Z_1_IDX+j] = F::from_canonical_u32(g2[4][j]);
                self.trace[0][G2_Z_2_IDX+j] = F::from_canonical_u32(g2[5][j]);
            }
        }

        // Set z_invert in the z_index itself from row 1 -> total_rows
        let z_invert = get_g2_invert(&g2[4], &g2[5]);
        self.assign_u32_12(1, G2_Z_1_IDX, z_invert[0]);
        self.assign_u32_12(1, G2_Z_2_IDX, z_invert[1]);

        // Assign C0T0
        // self.trace[0][G2_Z_1_IDX..G2_Z_1_IDX+12] * self.trace[1][G2_Z_1_IDX..G2_Z_1_IDX+12]
        // self.assign_u32_in_series(0, C0_T0_IDX, &mul_fp_without_reduction(Fp(g2[4]), Fp(z_invert[0])));

        for i in 1..self.num_rows {
            // self.assign_cols_from_prev(i, G1_Y_IDX, 12);
        }
        /*
        cols -> c0_t0, c0_t0_carries, c0_t1, c0_t1_carries, 
                c0(non_reduced), c0_evaluation_carries, c0_reduced_carries
                c1_t0, c1_t0_carries, c1_t1, c1_t1_carries,
                c1(non_reduced), c1_evaluation_carries, c1_reduced_carries

        c0 = c0_t0 - c0_t1 ;

        c0_t0 = (Z[G2_Z_1_IDX..G2_Z_1_IDX+12] * Z_INV[G2_Z_1_IDX..G2_Z_1_IDX+12]);
        c0_t1 = (Z[G2_Z_2_IDX..G2_Z_2_IDX+12] * Z_INV[G2_Z_2_IDX..G2_Z_2_IDX+12]);

        c1_t0 = (Z[G2_Z_1_IDX..G2_Z_1_IDX+12] * Z_INV[G2_Z_2_IDX..G2_Z_2_IDX+12]);
        c1_t1 = (Z[G2_Z_2_IDX..G2_Z_2_IDX+12] * Z_INV[G2_Z_1_IDX..G2_Z_1_IDX+12]);
        c1 = c1_t0+c1_t1

         */

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


// Constraints
/*
    1. Z_INDEX(row: 0) * Z_INVERT_INDEX(row: 0) == 1
    2. G1_Y_INDEX(row: 0) + G1_Y_INDEX(row: 1) == MODULUS [X]
    3. Z_INDEX -> remains same throughout rows(0-num_rows)
    4. Z_INVERT_INDEX -> remains same throughout (0-num_rows)
    5. G1_Y_INDEX -> remain same throughout (1-num_rows)
 */