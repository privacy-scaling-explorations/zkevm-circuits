/*
PI CIRCUIT

pub struct Transform {
    pub typ: ProofType,
    pub key: H256,
    pub value: U256,
    pub address: Address,
    pub nonce: U64,
    pub balance: U256,
    pub code_hash: H256,
}

pub struct MptTable {
    /// Account address
    pub address: Column<Advice>,
    /// Storage address
    pub storage_key: word::Word<Column<Advice>>,
    /// Proof type
    pub proof_type: Column<Advice>,
    /// New MPT root
    pub new_root: word::Word<Column<Advice>>,
    /// Previous MPT root
    pub old_root: word::Word<Column<Advice>>,
    /// New value
    pub new_value: word::Word<Column<Advice>>,
    /// Old value
    pub old_value: word::Word<Column<Advice>>,
}

PICIRCUIT

PI
------------------
last_state_root
next_state_root
| proof_type
| address
| value_hi
| value_lo
| storage_hi
| storage_lo
0

start  proof_type  address value_hi value_lo storage_hi storage_lo  old_root new_root
-----  ---------- -------- -------- -------- ---------- ---------- --------- ----------
1      -                                                                      r1
0      BalChange   a1       0        0        0          0          r1        r2
0      BalChange   a2       0        0        0          0          r2        r3
0       0
0       0
0       0

// check first state root
if start.current == 1 => new_root.current == PI.last_state_root

// check last state root
if proof_type.curr != 0 and proof_type.next == 0 => new_root.current == PI.next_state_root

// check state_root_propagation
if start ==  1 || proof_type != 0 => old_root.next == new_root.current

// proof type = 0 propagation a
if proof_type.current == 0 => proof_type.next == 0

lookup (proof_type  address value_hi value_lo storage_hi storage_lo  old_root new_root) into MPTTable

*/



