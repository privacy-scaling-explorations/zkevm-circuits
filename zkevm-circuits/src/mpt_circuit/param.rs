pub const ARITY: usize = 16;
// Currently using 32 - each hash byte goes into its own cell, this might be
// compressed for optimization purposes in the future.
pub const HASH_WIDTH: usize = 32; // number of columns used for hash output

// Compact encoding key prefixes
pub const KEY_PREFIX_EVEN: u8 = 0b0000_0000;
pub const KEY_PREFIX_ODD: u8 = 0b0001_0000;
pub const KEY_TERMINAL_PREFIX_EVEN: u8 = 0b0010_0000;
pub const KEY_TERMINAL_PREFIX_ODD: u8 = 0b0011_0000;

// RLP prefixes
pub const RLP_SHORT: u8 = 128; // 0x80
pub const RLP_LONG: u8 = 183; //  0xb7
pub const RLP_LIST_SHORT: u8 = 192; //  0xc0
pub const RLP_LIST_LONG: u8 = 247; //  0xf7
pub const RLP_NIL: u8 = 128; //  0x80
pub const RLP_HASH_VALUE: u8 = 128 + 32; //  0x80

// Key parameters
pub const KEY_LEN: usize = 32;
pub const KEY_LEN_IN_NIBBLES: usize = KEY_LEN * 2;

// Empty trie
pub const EMPTY_TRIE_HASH: [u8; 32] = [
    86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224, 27, 153,
    108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
];

// Number of bytes required to decode an RLP item
pub const RLP_UNIT_NUM_BYTES: usize = 34;
