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

pub const G1_Y_NEGATE_SELECTOR_IDX: usize = E_G_P_IDX + 144;

pub const Z_INVERT_IDX_1: usize = G1_Y_NEGATE_SELECTOR_IDX + 1;
pub const Z_INVERT_IDX_2: usize  = Z_INVERT_IDX_1 + 12;

pub const G1_Y_CARRY_IDX: usize = Z_INVERT_IDX_2 + 12;




pub const TOTAL_COLUMNS: usize =  G1_Y_CARRY_IDX + 12 + 1;




