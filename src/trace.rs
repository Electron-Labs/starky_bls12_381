use num_bigint::BigUint;
use plonky2::{field::{types::Field, extension::Extendable, polynomial::PolynomialValues}, hash::hash_types::RichField, util::transpose};
use itertools::Itertools;
use crate::{layout::{G1_X_IDX, G1_Y_IDX, G2_X_1_IDX, G2_X_2_IDX, G2_Y_1_IDX, G2_Y_2_IDX, G2_Z_1_IDX, G2_Z_2_IDX, G1_Y_NEGATE_SELECTOR_IDX, Z_INVERT_IDX_1, Z_INVERT_IDX_2, G1_Y_CARRY_IDX, TOTAL_COLUMNS}, native::{modulus, get_negate, get_g2_invert, get_u32_carries, modulus_digits, Fp}};

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

    pub fn assign_cols_from_prev(&mut self, row: usize, start_col: usize, num_cols: usize) {
        assert!(row>=1);
        for i in start_col..start_col+num_cols {
            self.trace[row][start_col+i] = self.trace[row-1][start_col+i];
        }
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
        // Set negate selector
        self.trace[0][G1_Y_NEGATE_SELECTOR_IDX] = F::ONE;

        // Set z_invert 
        let z_invert = get_g2_invert(&g2[4], &g2[5]);
        self.assign_u32_12(0, Z_INVERT_IDX_1, z_invert[0]);
        self.assign_u32_12(0, Z_INVERT_IDX_2, z_invert[1]);

        let negate_g1_y = get_negate(&g1[1]);
        // Set negate for row 1
        let carries = get_u32_carries(&g1[1], &negate_g1_y);
        self.assign_u32_12(1, G1_Y_IDX, negate_g1_y);
        self.assign_u32_12(1, G1_Y_CARRY_IDX, carries);

        for i in 1..self.num_rows {
            // self.assign_cols_from_prev(i, G1_Y_IDX, 12);
        }

        let g1_y_bu = BigUint::new(g1[1].to_vec());
        let g1_neg_y_bu = BigUint::new(negate_g1_y.to_vec());
        println!("g1_y::{}, g1_neg_y::{}, modulus::{}", g1_y_bu, g1_neg_y_bu, modulus());
        for i in 1..11 {
            println!("dnkjn{:?}",self.trace[0][G1_Y_IDX+i]  
            + self.trace[1][G1_Y_CARRY_IDX + i-1]+
            self.trace[1][G1_Y_IDX + i]- 
            (self.trace[1][G1_Y_CARRY_IDX + i] * F::from_canonical_u64(1u64<<32)) - 
            F::from_canonical_u32(modulus_digits()[i]));
        }
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