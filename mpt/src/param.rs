// Currently using 32 - each hash byte goes into its own cell, this might be
// compressed for optimization purposes in the future.
pub const HASH_WIDTH: usize = 32;
pub const WITNESS_ROW_WIDTH: usize = 68;
pub const LAYOUT_OFFSET: usize = 2;
pub const KECCAK_INPUT_WIDTH: usize = 1;
pub const KECCAK_OUTPUT_WIDTH: usize = 1;
// for s: RLP 2 cells + HASH_WIDTH cells
// for c: RLP 2 cells + HASH_WIDTH cells
pub const RLP_NUM: usize = 2;
pub const S_RLP_START: usize = 0;
pub const S_START: usize = RLP_NUM;
pub const C_RLP_START: usize = RLP_NUM + HASH_WIDTH;
pub const C_START: usize = RLP_NUM + HASH_WIDTH + RLP_NUM;
pub const BRANCH_0_S_START: usize = 4; // row 0 of a branch contains some RLP data
pub const BRANCH_0_C_START: usize = 7;
pub const BRANCH_0_KEY_POS: usize = 10; // row 0 of a branch contains info (deriving from key) about which branch node
                                        // is being modified
pub const BRANCH_ROWS_NUM: i32 = 19;
pub const R_TABLE_LEN: usize = 32;
pub const IS_BRANCH_S_PLACEHOLDER_POS: usize = 11;
pub const IS_BRANCH_C_PLACEHOLDER_POS: usize = 12;
pub const DRIFTED_POS: usize = 13;
pub const IS_BRANCH_C16_POS: usize = 19;
pub const IS_BRANCH_C1_POS: usize = 20;
pub const IS_EXT_SHORT_C16_POS: usize = 21;
pub const IS_EXT_SHORT_C1_POS: usize = 22;
pub const IS_EXT_LONG_EVEN_C16_POS: usize = 23;
pub const IS_EXT_LONG_EVEN_C1_POS: usize = 24;
pub const IS_EXT_LONG_ODD_C16_POS: usize = 25;
pub const IS_EXT_LONG_ODD_C1_POS: usize = 26;

pub const NOT_FIRST_LEVEL_POS: usize = 2;
pub const IS_STORAGE_MOD_POS: usize = 3;
pub const IS_NONCE_MOD_POS: usize = 4;
pub const IS_BALANCE_MOD_POS: usize = 5;
pub const IS_CODEHASH_MOD_POS: usize = 6;
pub const IS_ACCOUNT_DELETE_MOD_POS: usize = 7;
pub const IS_NON_EXISTING_ACCOUNT_POS: usize = 8;
pub const COUNTER_WITNESS_LEN: usize = 4;
pub const COUNTER_POS: usize = IS_NON_EXISTING_ACCOUNT_POS + COUNTER_WITNESS_LEN;

pub const LEAF_KEY_S_IND: i32 = 0;
pub const LEAF_VALUE_S_IND: i32 = 1;
pub const LEAF_KEY_C_IND: i32 = 2;
pub const LEAF_VALUE_C_IND: i32 = 3;
pub const LEAF_DRIFTED_IND: i32 = 4;

pub const ACCOUNT_LEAF_KEY_S_IND: i32 = 0;
pub const ACCOUNT_LEAF_KEY_C_IND: i32 = 1;
pub const ACCOUNT_LEAF_NONCE_BALANCE_S_IND: i32 = 2;
pub const ACCOUNT_LEAF_NONCE_BALANCE_C_IND: i32 = 3;
pub const ACCOUNT_LEAF_STORAGE_CODEHASH_S_IND: i32 = 4;
pub const ACCOUNT_LEAF_STORAGE_CODEHASH_C_IND: i32 = 5;
pub const ACCOUNT_DRIFTED_LEAF_IND: i32 = 6;

pub const EXTENSION_ROWS_NUM: i32 = 2;
