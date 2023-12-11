// PUBLIC KEY
pub const G1_X_IDX: usize = 0;
pub const G1_Y_IDX: usize = G1_X_IDX + 12;
// HASHED MESSAGE
pub const G2_X_1_IDX: usize = G1_Y_IDX + 12;
pub const G2_X_2_IDX: usize = G2_X_1_IDX + 12;
pub const G2_Y_1_IDX: usize = G2_X_2_IDX + 12;
pub const G2_Y_2_IDX: usize = G2_Y_1_IDX + 12;
pub const G2_Z_1_IDX: usize = G2_Y_2_IDX + 12;
pub const G2_Z_2_IDX: usize = G2_Z_1_IDX + 12;

// OUTPUT
pub const E_G_P_IDX: usize = G2_Z_2_IDX + 12;


// FIELD_MULTIPLICATION
pub const X_INPUT_IDX: usize = 0;
pub const Y_INPUT_IDX: usize = X_INPUT_IDX + 12;
pub const XY_IDX: usize = Y_INPUT_IDX + 12;
pub const XY_CARRIES_IDX: usize = XY_IDX + 13;
pub const SHIFTED_XY: usize = XY_CARRIES_IDX + 12;
pub const SELECTOR: usize = SHIFTED_XY + 24;
pub const SUM: usize = SELECTOR + 12;
pub const SUM_CARRIES: usize = SUM + 24;
pub const EVALUATION_IDX: usize = SUM_CARRIES + 24;


pub const TOTAL_COLUMNS: usize =  EVALUATION_IDX + 24 + 1;