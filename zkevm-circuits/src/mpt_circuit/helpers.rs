use crate::{
    assign, circuit,
    circuit_tools::{
        cached_region::{CachedRegion, ChallengeSet},
        cell_manager::{Cell, CellManager, CellType, WordCell},
        constraint_builder::{
            ConstraintBuilder, RLCChainable, RLCChainableRev, RLCChainableValue, RLCable,
        },
        gadgets::{IsEqualGadget, IsEqualWordGadget, LtGadget},
        memory::MemoryBank,
    },
    evm_circuit::{
        param::{N_BYTES_HALF_WORD, N_BYTES_WORD},
        util::from_bytes,
    },
    matchw,
    mpt_circuit::{
        param::{
            ADDRESS_WIDTH, EMPTY_TRIE_HASH, HASH_WIDTH, KEY_LEN_IN_NIBBLES, KEY_PREFIX_EVEN,
            KEY_TERMINAL_PREFIX_EVEN, RLP_UNIT_NUM_BYTES, RLP_UNIT_NUM_VALUE_BYTES,
        },
        rlp_gadgets::{get_ext_odd_nibble, get_terminal_odd_nibble},
    },
    table::LookupTable,
    util::{
        word::{self, Word},
        Challenges, Expr,
    },
};
use eth_types::{Field, Word as U256};
use gadgets::util::{not, or, pow, Scalar};
use halo2_proofs::{
    circuit::Value,
    plonk::{ConstraintSystem, Error, Expression, VirtualCells},
};
use strum_macros::EnumIter;

use super::{
    rlp_gadgets::{
        get_ext_odd_nibble_value, RLPItemGadget, RLPItemWitness, RLPListGadget, RLPListWitness,
    },
    FixedTableTag, MPTCircuitParams, RlpItemType,
};

impl<F: Field> ChallengeSet<F> for crate::util::Challenges<Value<F>> {
    fn indexed(&self) -> Vec<&Value<F>> {
        self.indexed().to_vec()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter)]
pub enum MptTableType {
    Fixed,
    Byte,
    Keccak,
    Mult,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MptCellType {
    StoragePhase1,
    StoragePhase2,
    StoragePhase3,
    StoragePermutation,
    Lookup(MptTableType),
    Dynamic(usize),

    MemParentS,
    MemParentC,
    MemKeyS,
    MemKeyC,
    MemMain,
}

impl Default for MptCellType {
    fn default() -> Self {
        Self::StoragePhase1
    }
}

impl CellType for MptCellType {
    type TableType = MptTableType;

    fn byte_type() -> Option<Self> {
        Some(MptCellType::Lookup(MptTableType::Byte))
    }

    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            0 => MptCellType::StoragePhase1,
            1 => MptCellType::StoragePhase2,
            2 => MptCellType::StoragePhase3,
            _ => unreachable!(),
        }
    }

    fn create_type(id: usize) -> Self {
        MptCellType::Dynamic(id)
    }

    fn lookup_table_type(&self) -> Option<Self::TableType> {
        match self {
            MptCellType::Lookup(table) => Some(*table),
            _ => None,
        }
    }
}

pub const FIXED: MptCellType = MptCellType::Lookup(MptTableType::Fixed);
pub const KECCAK: MptCellType = MptCellType::Lookup(MptTableType::Keccak);
pub const MULT: MptCellType = MptCellType::Lookup(MptTableType::Mult);

/// Indexable object
pub trait Indexable {
    /// Convert to index
    fn idx(&self) -> usize;
}

impl Indexable for bool {
    fn idx(&self) -> usize {
        usize::from(!(*self))
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyGadget<F> {
    has_no_nibbles: IsEqualGadget<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct LeafKeyWitness {
    has_no_nibble: bool,
}

impl<F: Field> LeafKeyGadget<F> {
    pub(crate) fn construct(cb: &mut MPTConstraintBuilder<F>, rlp_key: RLPItemView<F>) -> Self {
        circuit!([meta, cb], {
            let has_no_nibbles = IsEqualGadget::<F>::construct(
                &mut cb.base,
                rlp_key.bytes_be()[0].expr(),
                KEY_TERMINAL_PREFIX_EVEN.expr(),
            );
            LeafKeyGadget { has_no_nibbles }
        })
    }

    pub(crate) fn expr(
        &self,
        cb: &mut MPTConstraintBuilder<F>,
        rlp_key: RLPItemView<F>,
        key_mult_prev: Expression<F>,
        is_key_odd: Expression<F>,
        r: &Expression<F>,
    ) -> Expression<F> {
        circuit!([meta, cb.base], {
            let calc_rlc = |cb: &mut MPTConstraintBuilder<F>,
                            bytes: &[Expression<F>],
                            is_key_odd: Expression<F>| {
                leaf_key_rlc(cb, bytes, key_mult_prev.expr(), is_key_odd.expr(), r)
            };
            matchx! {(
                rlp_key.is_short() => {
                    // When no nibbles: only terminal prefix at `bytes[0]`.
                    // Else: Terminal prefix + single nibble  at `bytes[0]`
                    let is_odd = not!(self.has_no_nibbles);
                    calc_rlc(cb, &rlp_key.bytes_be()[0..1], is_odd)
                },
                rlp_key.is_long() => {
                    // First key byte is at `bytes[1]`.
                    calc_rlc(cb, &rlp_key.bytes_be()[1..34], is_key_odd.expr())
                },
            )}
        })
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<LeafKeyWitness, Error> {
        let has_no_nibble = self.has_no_nibbles.assign(
            region,
            offset,
            F::from(bytes[0] as u64),
            F::from(KEY_TERMINAL_PREFIX_EVEN as u64),
        )?;
        Ok(LeafKeyWitness {
            has_no_nibble: has_no_nibble != 0.scalar(),
        })
    }
}

impl LeafKeyWitness {
    pub(crate) fn key<F: Field>(
        &self,
        rlp_key: RLPItemWitness,
        key_rlc: F,
        key_mult: F,
        r: F,
    ) -> (F, F) {
        if rlp_key.len() <= 1 {
            return (key_rlc, key_mult);
        }

        let start = 0;
        let len = rlp_key.len();
        let even_num_of_nibbles = rlp_key.bytes[start + 1] == 32;

        let mut key_rlc = key_rlc;
        let mut key_mult = key_mult;
        if !even_num_of_nibbles {
            // If odd number of nibbles, we have nibble+48 in s_advices[0].
            key_rlc += F::from((rlp_key.bytes[start + 1] - 48) as u64) * key_mult;
            key_mult *= r;
        }
        (key_rlc, key_mult)
            .rlc_chain_value(rlp_key.bytes[start + 2..start + 2 + len - 1].to_vec(), r)
    }
}

pub(crate) fn ext_key_rlc_expr<F: Field>(
    cb: &mut MPTConstraintBuilder<F>,
    key_value: RLPItemView<F>,
    key_mult_prev: Expression<F>,
    is_key_part_odd: Expression<F>,
    is_key_odd: Expression<F>,
    data: [Vec<Expression<F>>; 2],
    r: &Expression<F>,
) -> Expression<F> {
    circuit!([meta, cb.base], {
        let (is_short, is_long) = (key_value.is_short(), key_value.is_long());
        let mult_first_odd = ifx! {is_key_odd => { 1.expr() } elsex { 16.expr() }};
        let calc_rlc = |cb: &mut MPTConstraintBuilder<F>,
                        bytes: &[Expression<F>],
                        key_mult_first_even: Expression<F>| {
            ext_key_rlc(
                cb,
                bytes,
                key_mult_prev.expr(),
                is_key_part_odd.expr(),
                mult_first_odd.expr(),
                key_mult_first_even,
                r,
            )
        };
        matchx! {(
            and::expr(&[is_long.expr(), not!(is_key_odd)]) => {
                // Here we need to multiply nibbles over bytes with different r's so we need to rlc over separate nibbles.
                // Note that there can be at max 31 key bytes because 32 same bytes would mean
                // the two keys being the same - update operation, not splitting into extension node.
                // So, we do not need to look further than `s_main.bytes` even if `s_main.bytes[0]`
                // is not used (when even number of nibbles).
                let mut key_bytes = vec![data[0][1].expr()];
                key_bytes.append(&mut data[0][1..].iter().skip(1).zip(data[1][2..].iter()).map(|(byte, nibble_hi)| {
                    let nibble_lo = (byte.expr() - nibble_hi.expr()) * invert!(16);
                    // Check that `nibble_hi` is correct.
                    require!(byte => nibble_lo.expr() * 16.expr() + nibble_hi.expr());
                    // Collect bytes
                    (nibble_hi.expr() * 16.expr() * r.expr()) + nibble_lo.expr()
                }).collect::<Vec<_>>());
                calc_rlc(cb, &key_bytes, 1.expr())
            },
            and::expr(&[is_long.expr(), is_key_odd.expr()]) => {
                let additional_mult = ifx! {is_key_part_odd => { r.expr() } elsex { 1.expr() }};
                calc_rlc(cb, &data[0][1..], additional_mult)
            },
            is_short => {
                calc_rlc(cb, &data[0][..1], 1.expr())
            },
        )}
    })
}

pub(crate) fn ext_key_rlc_calc_value<F: Field>(
    key_value: RLPItemWitness,
    key_mult_prev: F,
    is_key_part_odd: bool,
    is_key_odd: bool,
    data: [Vec<u8>; 2],
    r: F,
) -> (F, F) {
    let (is_short, is_long) = (key_value.is_short(), key_value.is_long());
    let mult_first_odd = if is_key_odd { 1.scalar() } else { 16.scalar() };
    let calc_rlc = |bytes: &[F], key_mult_first_even: F| {
        ext_key_rlc_value(
            bytes,
            key_mult_prev,
            is_key_part_odd,
            mult_first_odd,
            key_mult_first_even,
            r,
        )
    };
    matchw! {
        is_long && !is_key_odd => {
            // Here we need to multiply nibbles over bytes with different r's so we need to rlc over separate nibbles.
            // Note that there can be at max 31 key bytes because 32 same bytes would mean
            // the two keys being the same - update operation, not splitting into extension node.
            let mut key_bytes = vec![data[0][1].scalar()];
            key_bytes.append(&mut data[0][1..].iter().skip(1).zip(data[1][2..].iter()).map(|(byte, nibble_hi)| {
                let nibble_lo = (byte - nibble_hi) >> 4;
                // Check that `nibble_hi` is correct.
                assert!(*byte == nibble_lo * 16 + nibble_hi);
                // Collect bytes
                (F::from(*nibble_hi as u64) * F::from(16_u64) * r) + F::from(nibble_lo as u64)
            }).collect::<Vec<_>>());
            calc_rlc(&key_bytes, 1.scalar())
        },
        is_long && is_key_odd => {
            let additional_mult = if is_key_part_odd { r } else { 1.scalar() };
            calc_rlc(&data[0][1..].iter().map(|byte| byte.scalar()).collect::<Vec<_>>(), additional_mult)
        },
        is_short => {
            calc_rlc(&data[0][..1].iter().map(|byte| byte.scalar()).collect::<Vec<_>>(), 1.scalar())
        },
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ListKeyGadget<F> {
    pub(crate) rlp_list_bytes: [Cell<F>; 3],
    pub(crate) rlp_list: RLPListGadget<F>,
    pub(crate) key_value: RLPItemView<F>,
    pub(crate) key: LeafKeyGadget<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ListKeyWitness {
    pub(crate) rlp_list: RLPListWitness,
    pub(crate) key_item: RLPItemWitness,
    pub(crate) key: LeafKeyWitness,
}

impl<F: Field> ListKeyGadget<F> {
    pub(crate) fn construct(cb: &mut MPTConstraintBuilder<F>, key_value: &RLPItemView<F>) -> Self {
        let rlp_list_bytes = cb.query_bytes();
        let rlp_list_bytes_expr = rlp_list_bytes.iter().map(|c| c.expr()).collect::<Vec<_>>();
        let key = LeafKeyGadget::construct(cb, key_value.clone());
        ListKeyGadget {
            rlp_list_bytes,
            rlp_list: RLPListGadget::construct(cb, &rlp_list_bytes_expr),
            key_value: key_value.clone(),
            key,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        list_bytes: &[u8],
        key_item: &RLPItemWitness,
    ) -> Result<ListKeyWitness, Error> {
        for (cell, byte) in self.rlp_list_bytes.iter().zip(list_bytes.iter()) {
            cell.assign(region, offset, byte.scalar())?;
        }
        let rlp_list = self.rlp_list.assign(region, offset, list_bytes)?;
        let key = self.key.assign(region, offset, &key_item.bytes)?;

        Ok(ListKeyWitness {
            rlp_list,
            key_item: key_item.clone(),
            key,
        })
    }

    pub(crate) fn rlc(&self, r: &Expression<F>) -> Expression<F> {
        self.rlp_list
            .rlc_rlp_only(r)
            .rlc_chain(self.key_value.rlc_rlp())
    }

    pub(crate) fn rlc2(&self, r: &Expression<F>) -> Expression<F> {
        self.rlp_list
            .rlc_rlp_only_rev(r)
            .0
            .rlc_chain_rev(self.key_value.rlc_chain_data())
    }
}

impl ListKeyWitness {
    /// Number of bytes of RLP (including list RLP bytes) and key
    pub(crate) fn rlc_leaf<F: Field>(&self, r: F) -> (F, F) {
        self.rlp_list
            .rlc_rlp_only(r)
            .rlc_chain_value(self.key_item.bytes[..self.key_item.num_bytes()].to_vec(), r)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct KeyData<F> {
    pub(crate) rlc: Cell<F>,
    pub(crate) mult: Cell<F>,
    pub(crate) num_nibbles: Cell<F>,
    pub(crate) is_odd: Cell<F>,
    pub(crate) drifted_rlc: Cell<F>,
    pub(crate) drifted_mult: Cell<F>,
    pub(crate) drifted_num_nibbles: Cell<F>,
    pub(crate) drifted_is_odd: Cell<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct KeyDataWitness<F> {
    pub(crate) rlc: F,
    pub(crate) mult: F,
    pub(crate) num_nibbles: usize,
    pub(crate) is_odd: bool,
    pub(crate) drifted_rlc: F,
    pub(crate) drifted_mult: F,
    pub(crate) drifted_num_nibbles: usize,
    pub(crate) drifted_is_odd: bool,
}

impl<F: Field> KeyData<F> {
    pub(crate) fn load<MB: MemoryBank<F, MptCellType>>(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &mut MB,
        offset: Expression<F>,
    ) -> Self {
        let key_data = KeyData {
            rlc: cb.query_cell_with_type(MptCellType::StoragePhase2),
            mult: cb.query_cell_with_type(MptCellType::StoragePhase2),
            num_nibbles: cb.query_cell(),
            is_odd: cb.query_cell(),
            drifted_rlc: cb.query_cell_with_type(MptCellType::StoragePhase2),
            drifted_mult: cb.query_cell_with_type(MptCellType::StoragePhase2),
            drifted_num_nibbles: cb.query_cell(),
            drifted_is_odd: cb.query_cell(),
        };
        circuit!([meta, cb.base], {
            memory.load(
                &mut cb.base,
                offset,
                &[
                    key_data.rlc.expr(),
                    key_data.mult.expr(),
                    key_data.num_nibbles.expr(),
                    key_data.is_odd.expr(),
                    key_data.drifted_rlc.expr(),
                    key_data.drifted_mult.expr(),
                    key_data.drifted_num_nibbles.expr(),
                    key_data.drifted_is_odd.expr(),
                ],
            );
        });
        key_data
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn store<MB: MemoryBank<F, MptCellType>>(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &mut MB,
        rlc: Expression<F>,
        mult: Expression<F>,
        num_nibbles: Expression<F>,
        is_odd: Expression<F>,
        drifted_rlc: Expression<F>,
        drifted_mult: Expression<F>,
        drifted_num_nibbles: Expression<F>,
        drifted_is_odd: Expression<F>,
    ) {
        memory.store(
            &mut cb.base,
            &[
                rlc,
                mult,
                num_nibbles,
                is_odd,
                drifted_rlc,
                drifted_mult,
                drifted_num_nibbles,
                drifted_is_odd,
            ],
        );
    }

    pub(crate) fn store_defaults<MB: MemoryBank<F, MptCellType>>(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &mut MB,
    ) {
        memory.store(&mut cb.base, &KeyData::default_values_expr());
    }

    pub(crate) fn default_values_expr() -> [Expression<F>; 8] {
        [
            0.expr(),
            1.expr(),
            0.expr(),
            false.expr(),
            0.expr(),
            1.expr(),
            0.expr(),
            false.expr(),
        ]
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn witness_store<MB: MemoryBank<F, MptCellType>>(
        _region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        memory: &mut MB,
        rlc: F,
        mult: F,
        num_nibbles: usize,
        drifted_rlc: F,
        drifted_mult: F,
        drifted_num_nibbles: usize,
    ) -> Result<(), Error> {
        let values = [
            rlc,
            mult,
            num_nibbles.scalar(),
            (num_nibbles % 2 == 1).scalar(),
            drifted_rlc,
            drifted_mult,
            drifted_num_nibbles.scalar(),
            (drifted_num_nibbles % 2 == 1).scalar(),
        ];
        memory.witness_store(offset, &values);

        Ok(())
    }

    pub(crate) fn witness_load<MB: MemoryBank<F, MptCellType>>(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        memory: &mut MB,
        load_offset: usize,
    ) -> Result<KeyDataWitness<F>, Error> {
        let values = memory.witness_load(load_offset);

        self.rlc.assign(region, offset, values[0])?;
        self.mult.assign(region, offset, values[1])?;
        self.num_nibbles.assign(region, offset, values[2])?;
        self.is_odd.assign(region, offset, values[3])?;
        self.drifted_rlc.assign(region, offset, values[4])?;
        self.drifted_mult.assign(region, offset, values[5])?;
        self.drifted_num_nibbles.assign(region, offset, values[6])?;
        self.drifted_is_odd.assign(region, offset, values[7])?;

        Ok(KeyDataWitness {
            rlc: values[0],
            mult: values[1],
            num_nibbles: values[2].get_lower_32() as usize,
            is_odd: values[3] != F::ZERO,
            drifted_rlc: values[4],
            drifted_mult: values[5],
            drifted_num_nibbles: values[6].get_lower_32() as usize,
            drifted_is_odd: values[7] != F::ZERO,
        })
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ParentData<F> {
    pub(crate) hash: WordCell<F>,
    pub(crate) rlc: Cell<F>,
    pub(crate) is_root: Cell<F>,
    pub(crate) is_placeholder: Cell<F>,
    pub(crate) drifted_parent_hash: WordCell<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ParentDataWitness<F> {
    pub(crate) hash: word::Word<F>,
    pub(crate) rlc: F,
    pub(crate) is_root: bool,
    pub(crate) is_placeholder: bool,
    pub(crate) drifted_parent_hash: word::Word<F>,
}

impl<F: Field> ParentData<F> {
    pub(crate) fn load<MB: MemoryBank<F, MptCellType>>(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &mut MB,
        offset: Expression<F>,
    ) -> Self {
        let parent_data = ParentData {
            hash: cb.query_word_unchecked(),
            rlc: cb.query_cell_with_type(MptCellType::StoragePhase2),
            is_root: cb.query_cell(),
            is_placeholder: cb.query_cell(),
            drifted_parent_hash: cb.query_word_unchecked(),
        };
        circuit!([meta, cb.base], {
            memory.load(
                &mut cb.base,
                offset,
                &[
                    parent_data.hash.lo().expr(),
                    parent_data.hash.hi().expr(),
                    parent_data.rlc.expr(),
                    parent_data.is_root.expr(),
                    parent_data.is_placeholder.expr(),
                    parent_data.drifted_parent_hash.lo().expr(),
                    parent_data.drifted_parent_hash.hi().expr(),
                ],
            );
        });
        parent_data
    }

    pub(crate) fn store<MB: MemoryBank<F, MptCellType>>(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &mut MB,
        hash: word::Word<Expression<F>>,
        rlc: Expression<F>,
        is_root: Expression<F>,
        is_placeholder: Expression<F>,
        drifted_parent_hash: word::Word<Expression<F>>,
    ) {
        memory.store(
            &mut cb.base,
            &[
                hash.lo(),
                hash.hi(),
                rlc,
                is_root,
                is_placeholder,
                drifted_parent_hash.lo(),
                drifted_parent_hash.hi(),
            ],
        );
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn witness_store<MB: MemoryBank<F, MptCellType>>(
        _region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        memory: &mut MB,
        hash: word::Word<F>,
        rlc: F,
        force_hashed: bool,
        is_placeholder: bool,
        drifted_parent_hash: word::Word<F>,
    ) -> Result<(), Error> {
        memory.witness_store(
            offset,
            &[
                hash.lo(),
                hash.hi(),
                rlc,
                force_hashed.scalar(),
                is_placeholder.scalar(),
                drifted_parent_hash.lo(),
                drifted_parent_hash.hi(),
            ],
        );
        Ok(())
    }

    pub(crate) fn witness_load<MB: MemoryBank<F, MptCellType>>(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        memory: &mut MB,
        load_offset: usize,
    ) -> Result<ParentDataWitness<F>, Error> {
        let values = memory.witness_load(load_offset);

        self.hash.lo().assign(region, offset, values[0])?;
        self.hash.hi().assign(region, offset, values[1])?;
        self.rlc.assign(region, offset, values[2])?;
        self.is_root.assign(region, offset, values[3])?;
        self.is_placeholder.assign(region, offset, values[4])?;
        self.drifted_parent_hash
            .lo()
            .assign(region, offset, values[5])?;
        self.drifted_parent_hash
            .hi()
            .assign(region, offset, values[6])?;

        Ok(ParentDataWitness {
            hash: word::Word::new([values[0], values[1]]),
            rlc: values[2],
            is_root: values[3] == 1.scalar(),
            is_placeholder: values[4] == 1.scalar(),
            drifted_parent_hash: word::Word::new([values[5], values[6]]),
        })
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct MainData<F> {
    pub(crate) proof_type: Cell<F>,
    pub(crate) is_below_account: Cell<F>,
    pub(crate) address: Cell<F>,
    pub(crate) new_root: WordCell<F>,
    pub(crate) old_root: WordCell<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct MainDataWitness<F> {
    pub(crate) proof_type: usize,
    pub(crate) is_below_account: bool,
    pub(crate) address: F,
    pub(crate) new_root: word::Word<F>,
    pub(crate) old_root: word::Word<F>,
}

impl<F: Field> MainData<F> {
    pub(crate) fn load<MB: MemoryBank<F, MptCellType>>(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &mut MB,
        offset: Expression<F>,
    ) -> Self {
        let main_data = MainData {
            proof_type: cb.query_cell(),
            is_below_account: cb.query_cell(),
            address: cb.query_cell(),
            new_root: cb.query_word_unchecked(),
            old_root: cb.query_word_unchecked(),
        };
        circuit!([meta, cb.base], {
            memory.load(
                &mut cb.base,
                offset,
                &[
                    main_data.proof_type.expr(),
                    main_data.is_below_account.expr(),
                    main_data.address.expr(),
                    main_data.new_root.lo().expr(),
                    main_data.new_root.hi().expr(),
                    main_data.old_root.lo().expr(),
                    main_data.old_root.hi().expr(),
                ],
            );
        });
        main_data
    }

    pub(crate) fn store<MB: MemoryBank<F, MptCellType>>(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &mut MB,
        values: [Expression<F>; 7],
    ) {
        memory.store(&mut cb.base, &values);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn witness_store<MB: MemoryBank<F, MptCellType>>(
        _region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        memory: &mut MB,
        proof_type: usize,
        is_below_account: bool,
        address: F,
        new_root: word::Word<F>,
        old_root: word::Word<F>,
    ) -> Result<(), Error> {
        let values = [
            proof_type.scalar(),
            is_below_account.scalar(),
            address,
            new_root.lo(),
            new_root.hi(),
            old_root.lo(),
            old_root.hi(),
        ];
        memory.witness_store(offset, &values);

        Ok(())
    }

    pub(crate) fn witness_load<MB: MemoryBank<F, MptCellType>>(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        memory: &mut MB,
        load_offset: usize,
    ) -> Result<MainDataWitness<F>, Error> {
        let values = memory.witness_load(load_offset);

        self.proof_type.assign(region, offset, values[0])?;
        self.is_below_account.assign(region, offset, values[1])?;
        self.address.assign(region, offset, values[2])?;
        self.new_root.lo().assign(region, offset, values[3])?;
        self.new_root.hi().assign(region, offset, values[4])?;
        self.old_root.lo().assign(region, offset, values[5])?;
        self.old_root.hi().assign(region, offset, values[6])?;

        Ok(MainDataWitness {
            proof_type: values[0].get_lower_32() as usize,
            is_below_account: values[1] == 1.scalar(),
            address: values[2],
            new_root: word::Word::new([values[3], values[4]]),
            old_root: word::Word::new([values[5], values[6]]),
        })
    }
}

/// Add the nibble from the drifted branch
pub(crate) fn nibble_rlc<F: Field>(
    cb: &mut MPTConstraintBuilder<F>,
    key_rlc: Expression<F>,
    key_mult_prev: Expression<F>,
    is_key_odd: Expression<F>,
    nibble: Expression<F>,
    r: &Expression<F>,
) -> (Expression<F>, Expression<F>) {
    circuit!([meta, cb.base], {
        let (nibble_mult, mult) = ifx! {is_key_odd => {
            // The nibble will be added as the least significant nibble, the multiplier needs to advance
            (1.expr(), r.expr())
        } elsex {
            // The nibble will be added as the most significant nibble, the multiplier needs to stay the same
            (16.expr(), 1.expr())
        }};
        (
            key_rlc + nibble * nibble_mult * key_mult_prev.expr(),
            key_mult_prev * mult,
        )
    })
}

pub(crate) fn leaf_key_rlc<F: Field>(
    cb: &mut MPTConstraintBuilder<F>,
    bytes: &[Expression<F>],
    key_mult_prev: Expression<F>,
    is_key_odd: Expression<F>,
    r: &Expression<F>,
) -> Expression<F> {
    circuit!([meta, cb.base], {
        // Add the odd nibble first if we have one.
        let (rlc, mult) = ifx! {is_key_odd => {
            (get_terminal_odd_nibble(bytes[0].expr()) * key_mult_prev.expr(), r.expr())
        } elsex {
            require!(bytes[0] => KEY_TERMINAL_PREFIX_EVEN);
            (0.expr(), 1.expr())
        }};
        (rlc, key_mult_prev * mult).rlc_chain(bytes[1..].rlc(r))
    })
}

pub(crate) fn ext_key_rlc<F: Field>(
    cb: &mut MPTConstraintBuilder<F>,
    bytes: &[Expression<F>],
    key_mult_prev: Expression<F>,
    is_odd: Expression<F>,
    rlc_mult_first_odd: Expression<F>,
    key_mult_first_odd: Expression<F>,
    r: &Expression<F>,
) -> Expression<F> {
    circuit!([meta, cb.base], {
        // Add the odd nibble first if we have one.
        let (rlc, mult) = ifx! {is_odd => {
            (get_ext_odd_nibble(bytes[0].expr()) * key_mult_prev.expr() * rlc_mult_first_odd, key_mult_first_odd.expr())
        } elsex {
            require!(bytes[0] => KEY_PREFIX_EVEN);
            (0.expr(), 1.expr())
        }};
        (rlc, key_mult_prev * mult).rlc_chain(bytes[1..].rlc(r))
    })
}

pub(crate) fn ext_key_rlc_value<F: Field>(
    bytes: &[F],
    key_mult_prev: F,
    is_odd: bool,
    rlc_mult_first_odd: F,
    key_mult_first_odd: F,
    r: F,
) -> (F, F) {
    // Add the odd nibble first if we have one.
    let (rlc, mult) = if is_odd {
        (
            get_ext_odd_nibble_value(bytes[0]) * key_mult_prev * rlc_mult_first_odd,
            key_mult_first_odd,
        )
    } else {
        assert!(bytes[0] == KEY_PREFIX_EVEN.scalar());
        (0.scalar(), 1.scalar())
    };
    (rlc, key_mult_prev * mult).rlc_chain_value(bytes[1..].iter().collect::<Vec<&F>>(), r)
}

// Returns the number of nibbles stored in a key value
pub(crate) mod num_nibbles {
    use crate::{_cb, circuit, circuit_tools::constraint_builder::ConstraintBuilder};
    use eth_types::Field;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(
        key_len: Expression<F>,
        is_key_odd: Expression<F>,
    ) -> Expression<F> {
        circuit!([meta, _cb!()], {
            ifx! {is_key_odd => {
                key_len.expr() * 2.expr() - 1.expr()
            } elsex {
                (key_len.expr() - 1.expr()) * 2.expr()
            }}
        })
    }
    pub(crate) fn value(key_len: usize, is_key_odd: bool) -> usize {
        if is_key_odd {
            key_len * 2 - 1
        } else {
            (key_len - 1) * 2
        }
    }
}

pub(crate) fn parent_memory(is_s: bool) -> MptCellType {
    if is_s {
        MptCellType::MemParentS
    } else {
        MptCellType::MemParentC
    }
}

pub(crate) fn key_memory(is_s: bool) -> MptCellType {
    if is_s {
        MptCellType::MemKeyS
    } else {
        MptCellType::MemKeyC
    }
}

pub(crate) fn main_memory() -> MptCellType {
    MptCellType::MemMain
}

/// MPTConstraintBuilder
#[derive(Clone)]
pub struct MPTConstraintBuilder<F> {
    pub base: ConstraintBuilder<F, MptCellType>,
    pub challenges: Option<Challenges<Expression<F>>>,
    pub key_r: Expression<F>,
    pub keccak_r: Expression<F>,
}

impl<F: Field> MPTConstraintBuilder<F> {
    pub(crate) fn new(
        max_degree: usize,
        challenges: Option<Challenges<Expression<F>>>,
        cell_manager: Option<CellManager<F, MptCellType>>,
    ) -> Self {
        MPTConstraintBuilder {
            base: ConstraintBuilder::new(
                max_degree,
                cell_manager,
                Some(challenges.clone().unwrap().lookup_input().expr()),
            ),
            key_r: challenges.clone().unwrap().keccak_input().expr(),
            keccak_r: challenges.clone().unwrap().keccak_input().expr(),
            challenges,
        }
    }

    pub(crate) fn push_condition(&mut self, condition: Expression<F>) {
        self.base.push_condition(condition)
    }

    pub(crate) fn pop_condition(&mut self) {
        self.base.pop_condition()
    }

    pub(crate) fn query_bool(&mut self) -> Cell<F> {
        self.base.query_bool()
    }

    pub(crate) fn query_byte(&mut self) -> Cell<F> {
        self.base.query_bytes::<1>()[0].clone()
    }

    pub(crate) fn query_bytes<const N: usize>(&mut self) -> [Cell<F>; N] {
        self.base.query_bytes()
    }

    pub(crate) fn query_bytes_dyn(&mut self, count: usize) -> Vec<Cell<F>> {
        self.base.query_cells_dyn(MptCellType::StoragePhase1, count)
    }

    pub(crate) fn query_cell(&mut self) -> Cell<F> {
        self.base.query_default()
    }

    pub(crate) fn query_cells<const N: usize>(&mut self) -> [Cell<F>; N] {
        self.base
            .query_cells_dyn(MptCellType::default(), N)
            .try_into()
            .unwrap()
    }

    pub(crate) fn query_cell_with_type(&mut self, cell_type: MptCellType) -> Cell<F> {
        self.base.query_cell_with_type(cell_type)
    }

    // default query_word is 2 limbs. Each limb is not guaranteed to be 128 bits.
    pub(crate) fn query_word_unchecked(&mut self) -> WordCell<F> {
        self.base.query_word_unchecked()
    }

    pub(crate) fn require_equal(
        &mut self,
        name: &'static str,
        lhs: Expression<F>,
        rhs: Expression<F>,
    ) {
        self.base.require_equal(name, lhs, rhs)
    }

    pub(crate) fn require_in_set(
        &mut self,
        name: &'static str,
        value: Expression<F>,
        set: Vec<Expression<F>>,
    ) {
        self.base.require_in_set(name, value, set)
    }

    pub(crate) fn require_boolean(&mut self, name: &'static str, value: Expression<F>) {
        self.base.require_boolean(name, value)
    }

    pub(crate) fn add_lookup(
        &mut self,
        description: String,
        values: Vec<Expression<F>>,
        table: Vec<Expression<F>>,
    ) {
        self.base.add_lookup(description, values, table);
    }

    pub(crate) fn load_table(
        &mut self,
        meta: &mut ConstraintSystem<F>,
        tag: MptTableType,
        table: &dyn LookupTable<F>,
    ) {
        self.base.load_table(meta, tag, table)
    }

    pub(crate) fn store_table(
        &mut self,
        description: &'static str,
        tag: MptTableType,
        values: Vec<Expression<F>>,
    ) {
        self.base.store_table(description, tag, values)
    }

    pub(crate) fn store_tuple(
        &mut self,
        description: &'static str,
        table_type: MptCellType,
        values: Vec<Expression<F>>,
    ) -> Expression<F> {
        self.base.store_tuple(description, table_type, values)
    }

    pub(crate) fn table(&self, table_type: MptTableType) -> Vec<Expression<F>> {
        self.base.table(table_type)
    }
}

/// Checks if we are in an empty tree
#[derive(Clone, Debug, Default)]
pub struct IsPlaceholderLeafGadget<F> {
    is_empty_trie: IsEqualWordGadget<F>,
    is_nil_in_branch_at_mod_index: IsEqualWordGadget<F>,
}

impl<F: Field> IsPlaceholderLeafGadget<F> {
    pub(crate) fn construct(
        cb: &mut MPTConstraintBuilder<F>,
        parent_word: Word<Expression<F>>,
    ) -> Self {
        circuit!([meta, cb.base], {
            let empty_hash = Word::<F>::from(U256::from_big_endian(&EMPTY_TRIE_HASH));
            let is_empty_trie = IsEqualWordGadget::construct(
                &mut cb.base,
                &parent_word,
                &Word::<Expression<F>>::new([
                    Expression::Constant(empty_hash.lo()),
                    Expression::Constant(empty_hash.hi()),
                ]),
            );
            let is_nil_in_branch_at_mod_index = IsEqualWordGadget::construct(
                &mut cb.base,
                &parent_word,
                &Word::<Expression<F>>::new([0.expr(), 0.expr()]),
            );

            Self {
                is_empty_trie,
                is_nil_in_branch_at_mod_index,
            }
        })
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        or::expr(&[
            self.is_empty_trie.expr(),
            self.is_nil_in_branch_at_mod_index.expr(),
        ])
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        hash: Word<F>,
    ) -> Result<(), Error> {
        let empty_hash = Word::<F>::from(U256::from_big_endian(&EMPTY_TRIE_HASH));
        self.is_empty_trie
            .assign(region, offset, hash, empty_hash)?;
        self.is_nil_in_branch_at_mod_index.assign(
            region,
            offset,
            hash,
            Word::<F>::from(U256::zero()),
        )?;
        Ok(())
    }
}

/// Handles drifted leaves
#[derive(Clone, Debug, Default)]
pub struct DriftedGadget<F> {
    drifted_rlp_key: ListKeyGadget<F>,
}

impl<F: Field> DriftedGadget<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn construct(
        cb: &mut MPTConstraintBuilder<F>,
        value_list_num_bytes: &[Expression<F>],
        parent_data: &[ParentData<F>],
        key_data: &[KeyData<F>],
        expected_key_rlc: &[Expression<F>],
        leaf_no_key_rlc: &[Expression<F>],
        leaf_no_key_rlc_mult: &[Expression<F>],
        drifted_item: &RLPItemView<F>,
        is_mod_extension: &[Cell<F>; 2],
        r: &Expression<F>,
    ) -> Self {
        let mut config = DriftedGadget::default();
        circuit!([meta, cb], {
            ifx! {parent_data[true.idx()].is_placeholder.expr() + parent_data[false.idx()].is_placeholder.expr() => {
                config.drifted_rlp_key = ListKeyGadget::construct(cb, drifted_item);
                for is_s in [true, false] {
                    ifx! {and::expr(&[parent_data[is_s.idx()].is_placeholder.expr(), not!(is_mod_extension[is_s.idx()].expr())]) => {
                        ifx! {parent_data[is_s.idx()].is_placeholder.expr() => {
                            // Check that the drifted leaf is unchanged and is stored at `drifted_index`.

                            // Make sure the RLP is still consistent with the new key part
                            require!(
                                config.drifted_rlp_key.rlp_list.len()
                                    => config.drifted_rlp_key.key_value.num_bytes() + value_list_num_bytes[is_s.idx()].clone()
                                );

                            // Calculate the drifted key RLC
                            // Get the key RLC for the drifted branch
                            let (key_rlc, key_mult, key_num_nibbles, is_key_odd) = (
                                key_data[is_s.idx()].drifted_rlc.expr(),
                                key_data[is_s.idx()].drifted_mult.expr(),
                                key_data[is_s.idx()].drifted_num_nibbles.expr(),
                                key_data[is_s.idx()].drifted_is_odd.expr(),
                            );
                            let key_rlc = key_rlc.expr() + config.drifted_rlp_key.key.expr(
                                cb,
                                config.drifted_rlp_key.key_value.clone(),
                                key_mult.expr(),
                                is_key_odd.expr(),
                                r
                            );
                            // The key of the drifted leaf needs to match the key of the leaf
                            require!(key_rlc => expected_key_rlc[is_s.idx()]);

                            // Total number of nibbles needs to be KEY_LEN_IN_NIBBLES
                            // (RLC encoding could be the same for addresses with zero's at the end)
                            let num_nibbles = num_nibbles::expr(config.drifted_rlp_key.key_value.len(), is_key_odd.expr());
                            require!(key_num_nibbles.expr() + num_nibbles => KEY_LEN_IN_NIBBLES);

                            // Complete the drifted leaf rlc by adding the bytes on the value row
                            //let leaf_rlc = (config.drifted_rlp_key.rlc(be_r), mult.expr()).rlc_chain(leaf_no_key_rlc[is_s.idx()].expr());
                            let leaf_rlc = config.drifted_rlp_key.rlc2(&cb.keccak_r).rlc_chain_rev((leaf_no_key_rlc[is_s.idx()].expr(), leaf_no_key_rlc_mult[is_s.idx()].expr()));
                            // The drifted leaf needs to be stored in the branch at `drifted_index`.
                            let hash = parent_data[is_s.idx()].drifted_parent_hash.expr();
                            require!((1.expr(), leaf_rlc.expr(), config.drifted_rlp_key.rlp_list.num_bytes(), hash.lo(), hash.hi()) =>> @KECCAK);
                        }
                    }}
                }}
            }}
            config
        })
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        parent_data: &[ParentDataWitness<F>],
        drifted_list_bytes: &[u8],
        drifted_item: &RLPItemWitness,
        _r: F,
    ) -> Result<(), Error> {
        if parent_data[true.idx()].is_placeholder || parent_data[false.idx()].is_placeholder {
            self.drifted_rlp_key
                .assign(region, offset, drifted_list_bytes, drifted_item)?;
        }
        Ok(())
    }
}

/// Handles wrong leaves
#[derive(Clone, Debug, Default)]
pub struct WrongGadget<F> {
    wrong_rlp_key: ListKeyGadget<F>,
    is_key_equal: IsEqualGadget<F>,
}

impl<F: Field> WrongGadget<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn construct(
        cb: &mut MPTConstraintBuilder<F>,
        expected_key: Expression<F>,
        is_non_existing: Expression<F>,
        key_value: &RLPItemView<F>,
        key_rlc: &Expression<F>,
        expected_item: &RLPItemView<F>,
        is_in_empty_tree: Expression<F>,
        key_data: KeyData<F>,
        r: &Expression<F>,
    ) -> Self {
        let mut config = WrongGadget::default();
        circuit!([meta, cb.base], {
            // Get the previous key data
            ifx! {(is_non_existing, not!(is_in_empty_tree)) => {
                // Calculate the key
                config.wrong_rlp_key = ListKeyGadget::construct(cb, expected_item);
                let key_rlc_wrong = key_data.rlc.expr() + config.wrong_rlp_key.key.expr(
                    cb,
                    config.wrong_rlp_key.key_value.clone(),
                    key_data.mult.expr(),
                    key_data.is_odd.expr(),
                    r,
                );
                // Check that it's the key as expected
                require!(key_rlc_wrong => expected_key);

                // Now make sure this address is different than the one of the leaf
                config.is_key_equal = IsEqualGadget::construct(
                    &mut cb.base,
                    key_rlc.expr(),
                    expected_key,
                );
                require!(config.is_key_equal.expr() => false);
                // Make sure the lengths of the keys are the same
                require!(config.wrong_rlp_key.key_value.len() => key_value.len());
            }}
            config
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        is_non_existing: bool,
        key_rlc: &[F],
        list_bytes: &[u8],
        expected_item: &RLPItemWitness,
        for_placeholder_s: bool,
        key_data: KeyDataWitness<F>,
        r: F,
    ) -> Result<(F, F), Error> {
        if is_non_existing {
            let wrong_witness =
                self.wrong_rlp_key
                    .assign(region, offset, list_bytes, expected_item)?;
            let (key_rlc_wrong, _) = wrong_witness.key.key(
                wrong_witness.key_item.clone(),
                key_data.rlc,
                key_data.mult,
                r,
            );

            let is_key_equal_witness = self.is_key_equal.assign(
                region,
                offset,
                key_rlc[for_placeholder_s.idx()],
                key_rlc_wrong,
            )?;

            // When key is not equal, we have a non existing account
            Ok((key_rlc_wrong, is_key_equal_witness.neg()))
        } else {
            // existing account
            Ok((key_rlc[for_placeholder_s.idx()], false.scalar()))
        }
    }
}

/// Main RLP item
#[derive(Clone, Debug, Default)]
pub struct MainRLPGadget<F> {
    rlp_byte: Cell<F>,
    bytes: Vec<Cell<F>>,
    rlp: RLPItemGadget<F>,
    below_limit: LtGadget<F, 1>,
    num_bytes: Cell<F>,
    len: Cell<F>,
    mult_inv: Cell<F>,
    mult_diff: Cell<F>,
    hash_rlc: Cell<F>,
    rlc_rlp: Cell<F>,
    word: WordCell<F>,
    tag: Cell<F>,
    max_len: Cell<F>,
    is_rlp: Cell<F>,
    is_big_endian: Cell<F>,
    is_hash: Cell<F>,
    ensure_minimal_rlp: Cell<F>,
    keccak_r: Option<Expression<F>>,
}

impl<F: Field> MainRLPGadget<F> {
    pub(crate) fn construct(cb: &mut MPTConstraintBuilder<F>, params: MPTCircuitParams) -> Self {
        circuit!([meta, cb], {
            let mut config = MainRLPGadget {
                rlp_byte: cb.query_cell(),
                rlp: RLPItemGadget::default(),
                bytes: cb.query_cells::<RLP_UNIT_NUM_VALUE_BYTES>().to_vec(),
                below_limit: LtGadget::default(),
                num_bytes: cb.query_cell(),
                len: cb.query_cell(),
                mult_inv: cb.query_cell_with_type(MptCellType::StoragePhase2),
                mult_diff: cb.query_cell_with_type(MptCellType::StoragePhase2),
                hash_rlc: cb.query_cell_with_type(MptCellType::StoragePhase2),
                rlc_rlp: cb.query_cell_with_type(MptCellType::StoragePhase2),
                word: cb.query_word_unchecked(),
                tag: cb.query_cell(),
                max_len: cb.query_cell(),
                is_rlp: cb.query_cell(),
                is_big_endian: cb.query_cell(),
                is_hash: cb.query_cell(),
                ensure_minimal_rlp: cb.query_cell(),
                keccak_r: Some(cb.keccak_r.expr()),
            };
            let all_bytes = vec![vec![config.rlp_byte.clone()], config.bytes.clone()].concat();

            // Decode the RLP item
            config.rlp =
                RLPItemGadget::construct(cb, &[config.rlp_byte.expr(), 0.expr(), 0.expr()]);

            // Make sure the RLP item length is within a valid range
            config.below_limit = LtGadget::construct(
                &mut cb.base,
                config.rlp.len(),
                config.max_len.expr() + 1.expr(),
            );
            require!(config.below_limit.expr() => true);

            // Store RLP properties for easy access
            require!(config.num_bytes => config.rlp.num_bytes());
            require!(config.len => config.rlp.len());

            // Cache the rlc of the hash
            ifx! {config.is_hash.expr() => {
                require!(config.hash_rlc => config.bytes[..HASH_WIDTH].rlc_rev(&cb.key_r));
            }}

            // Cache some RLP related values
            ifx! {config.is_rlp.expr() => {
                // The key bytes are stored differently than all other value types (BE vs LE)
                ifx!{config.is_big_endian => {
                    require!(config.rlc_rlp => all_bytes.rlc_rev(&cb.keccak_r.expr()) * config.mult_inv.expr());
                } elsex {
                    // Special case for single byte string values as those values are stored in the RLP byte itself
                    ifx!{and::expr(&[not!(config.rlp.is_list()), config.rlp.is_short()]) => {
                        require!(config.word => [config.rlp_byte.expr(), 0.expr()]);
                        require!(config.rlc_rlp => config.rlp_byte);
                    } elsex {
                        let lo = from_bytes::expr(&config.bytes[0..N_BYTES_HALF_WORD]);
                        let hi = from_bytes::expr(&config.bytes[N_BYTES_HALF_WORD..N_BYTES_WORD]);
                        require!(config.word => [lo, hi]);
                        require!(config.rlc_rlp => config.rlp_byte.expr().rlc_chain_rev((
                            config.bytes.rlc(&cb.keccak_r.expr()),
                            config.mult_diff.expr(),
                        )));
                    }}
                }}
            }}

            // Check the multiplier values
            // `num_bytes - 1` because the RLP byte is handled separately
            require!((config.rlp.num_bytes() - 1.expr(), config.mult_diff.expr()) =>> @MULT);
            require!(config.mult_inv.expr() * pow::expr(cb.keccak_r.expr(), RLP_UNIT_NUM_BYTES - 1) => config.mult_diff.expr());

            // Lists always need to be short
            ifx! {config.rlp.is_list() => {
                require!(config.rlp.is_short() => true);
            }}

            // Range/zero checks
            // These range checks ensure that
            // - the bytes are all valid byte values < 256
            // - the byte value is zero when the byte index >= num_bytes
            // - the RLP encoding is minimal (when ensure_minimal_rlp is true) by checking that the
            //   MSB is non-zero (the byte at index 1 (the MSB) is non-zero)
            // We enable dynamic lookups because otherwise these lookups would require a lot of
            // extra cells.
            if params.is_two_byte_lookup_enabled() {
                assert!(all_bytes.len() % 2 == 0);
                for idx in (0..all_bytes.len()).step_by(2) {
                    require!((
                        config.tag.expr(),
                        config.num_bytes.expr() - idx.expr(),
                        all_bytes[idx],
                        all_bytes[idx + 1]
                    ) => @cb.table(MptTableType::Fixed));
                }
            } else {
                for (idx, byte) in all_bytes.iter().enumerate() {
                    // Never do any zero check on the RLP byte (which is always allowed to be 0)
                    let nonzero_check = if idx == 0 {
                        0.expr()
                    } else {
                        config.ensure_minimal_rlp.expr()
                    };
                    require!((config.tag.expr(), config.num_bytes.expr() - idx.expr(), byte.expr(), nonzero_check) => @cb.table(MptTableType::Fixed));
                }
            }

            config
        })
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: &[u8],
        item_type: RlpItemType,
    ) -> Result<RLPItemWitness, Error> {
        // Always pad the bytes to the full length with zeros
        let mut bytes = bytes.to_vec();
        while bytes.len() < RLP_UNIT_NUM_BYTES {
            bytes.push(0);
        }

        // Decode the RLP item
        let rlp = self.rlp.assign(region, offset, &bytes)?;

        // Depending on the RLP item type, we store the data in little endian or big endian.
        // Little endian makes it much easer to decode the lo/hi split representation.
        let mut value_bytes = bytes[1..].to_vec();
        let mut len: usize = rlp.len();
        while len < 33 {
            if self.is_big_endian(item_type) {
                // Just pad
                value_bytes.push(0);
            } else {
                // Push the bytes to the right
                value_bytes.insert(0, 0);
            }
            len += 1;
        }
        let mut value_bytes = value_bytes[0..33].to_vec();
        if !self.is_big_endian(item_type) {
            value_bytes.reverse();
        }
        // Assign the bytes
        assign!(region, self.rlp_byte, offset => bytes[0].scalar())?;
        for (byte, column) in value_bytes.iter().zip(self.bytes.iter()) {
            assign!(region, (column.column(), offset) => byte.scalar())?;
        }
        
        // Make sure the RLP item is within a valid range
        let max_len = if item_type == RlpItemType::Node {
            if rlp.is_string() {
                self.max_length(item_type)
            } else {
                HASH_WIDTH - 1
            }
        } else {
            self.max_length(item_type)
        }; 
        self.max_len.assign(region, offset, max_len.scalar())?;
        self.below_limit
            .assign(region, offset, rlp.len().scalar(), (max_len + 1).scalar())?;

        // Compute the denominator needed for BE
        let mult_inv = pow::value(region.keccak_r, RLP_UNIT_NUM_BYTES - rlp.num_bytes())
            .invert()
            .unwrap_or(F::ZERO);

        // Store RLP properties for easy access
        self.num_bytes
            .assign(region, offset, rlp.num_bytes().scalar())?;
        self.len.assign(region, offset, rlp.len().scalar())?;
        self.hash_rlc
            .assign(region, offset, rlp.rlc_content(region.key_r))?;
        self.rlc_rlp
            .assign(region, offset, rlp.rlc_rlp_rev(region.keccak_r))?;

        // Assign the word
        self.word.lo().assign(region, offset, rlp.word().lo())?;
        self.word.hi().assign(region, offset, rlp.word().hi())?;

        // Assign the RLC helper variables
        self.mult_inv.assign(region, offset, mult_inv)?;
        self.mult_diff.assign(
            region,
            offset,
            pow::value(region.keccak_r, rlp.num_bytes() - 1),
        )?;

        // Assign free inputs
        assign!(region, self.tag, offset => self.tag(item_type).scalar())?;
        assign!(region, self.is_rlp, offset => (item_type != RlpItemType::Nibbles).scalar())?;
        assign!(region, self.is_big_endian, offset => self.is_big_endian(item_type).scalar())?;
        assign!(region, self.is_hash, offset => (item_type == RlpItemType::Hash).scalar())?;
        assign!(region, self.ensure_minimal_rlp, offset => ((item_type == RlpItemType::Value) || rlp.is_list()).scalar())?;

        Ok(rlp)
    }

    pub(crate) fn create_view(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut MPTConstraintBuilder<F>,
        rot: usize,
        item_type: RlpItemType,
    ) -> RLPItemView<F> {
        circuit!([meta, cb.base], {
            let is_string = self.rlp.is_string_at(meta, rot);
            let is_list = self.rlp.is_list_at(meta, rot);
            let tag = self.tag.rot(meta, rot);
            let max_len = self.max_len.rot(meta, rot);
            let len = self.len.rot(meta, rot);
            let is_rlp = self.is_rlp.rot(meta, rot);
            let is_big_endian = self.is_big_endian.rot(meta, rot);
            let is_hash = self.is_hash.rot(meta, rot);
            let ensure_minimal_rlp = self.ensure_minimal_rlp.rot(meta, rot);

            // Check the tag value
            require!(tag => self.tag(item_type).expr());
            // Check that values and keys are always strings
            if item_type == RlpItemType::Value || item_type == RlpItemType::Key {
                require!(is_string => true);
            }
            // Hashes always are strings and have length HASH_WIDTH
            if item_type == RlpItemType::Hash {
                require!(is_string => true);
                require!(len => HASH_WIDTH);
            }
            // Addresses always are strings and have length ADDRESS_WIDTH
            if item_type == RlpItemType::Address {
                require!(is_string => true);
                require!(len => ADDRESS_WIDTH);
            }
            if item_type == RlpItemType::Node {
                // Nodes always have length 0 or 32 when a string, or are < 32 when a list
                ifx! {is_string => {
                    require!(max_len => self.max_length(item_type).expr());
                    require!(len => [0, HASH_WIDTH]);
                } elsex {
                    require!(max_len => HASH_WIDTH - 1);
                }}
            } else {
                require!(max_len => self.max_length(item_type).expr());
            }
            // Set the "free" inputs
            require!(is_rlp => self.is_rlp(item_type));
            require!(is_big_endian => self.is_big_endian(item_type));
            require!(is_hash => (item_type == RlpItemType::Hash));
            require!(ensure_minimal_rlp => or::expr([(item_type == RlpItemType::Value).expr(), is_list]));
        });
        RLPItemView {
            is_big_endian: self.is_big_endian(item_type),
            can_use_word: self.is_rlp(item_type) && !self.is_big_endian(item_type),
            num_bytes: Some(self.num_bytes.rot(meta, rot)),
            len: Some(self.len.rot(meta, rot)),
            mult: Some(self.mult_diff.rot(meta, rot) * cb.keccak_r.expr()),
            hash_rlc: Some(self.hash_rlc.rot(meta, rot)),
            rlc_rlp: Some(self.rlc_rlp.rot(meta, rot)),
            bytes: [vec![self.rlp_byte.clone()], self.bytes.clone()]
                .concat()
                .iter()
                .map(|byte| byte.rot(meta, rot))
                .collect(),
            is_short: Some(self.rlp.value.is_short.rot(meta, rot)),
            is_long: Some(self.rlp.value.is_long.rot(meta, rot)),
            word: Some(Word::new([
                self.word.lo().rot(meta, rot),
                self.word.hi().rot(meta, rot),
            ])),
        }
    }

    fn tag(&self, item_type: RlpItemType) -> FixedTableTag {
        if item_type == RlpItemType::Nibbles {
            FixedTableTag::RangeKeyLen16
        } else {
            FixedTableTag::RangeKeyLen256
        }
    }

    fn max_length(&self, item_type: RlpItemType) -> usize {
        match item_type {
            RlpItemType::Node => 32,
            RlpItemType::Value => 32,
            RlpItemType::Hash => 32,
            RlpItemType::Address => 20,
            RlpItemType::Key => 33,
            RlpItemType::Nibbles => 32,
        }
    }

    fn is_big_endian(&self, item_type: RlpItemType) -> bool {
        item_type == RlpItemType::Key || item_type == RlpItemType::Nibbles
    }

    fn is_rlp(&self, item_type: RlpItemType) -> bool {
        item_type != RlpItemType::Nibbles
    }
}

/// Main RLP item
#[derive(Clone, Debug, Default)]
pub struct RLPItemView<F> {
    is_big_endian: bool,
    can_use_word: bool,
    bytes: Vec<Expression<F>>,
    num_bytes: Option<Expression<F>>,
    len: Option<Expression<F>>,
    mult: Option<Expression<F>>,
    hash_rlc: Option<Expression<F>>,
    rlc_rlp: Option<Expression<F>>,
    is_short: Option<Expression<F>>,
    is_long: Option<Expression<F>>,
    word: Option<Word<Expression<F>>>,
}

impl<F: Field> RLPItemView<F> {
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        self.num_bytes.clone().unwrap()
    }

    pub(crate) fn len(&self) -> Expression<F> {
        self.len.clone().unwrap()
    }

    pub(crate) fn mult(&self) -> Expression<F> {
        self.mult.clone().unwrap()
    }

    pub(crate) fn hash_rlc(&self) -> Expression<F> {
        self.hash_rlc.clone().unwrap()
    }

    pub(crate) fn rlc_rlp(&self) -> Expression<F> {
        self.rlc_rlp.clone().unwrap()
    }

    pub(crate) fn rlc_chain_data(&self) -> (Expression<F>, Expression<F>) {
        (self.rlc_rlp(), self.mult())
    }

    pub(crate) fn bytes_be(&self) -> Vec<Expression<F>> {
        assert!(self.is_big_endian);
        self.bytes.clone()
    }

    pub(crate) fn bytes_le(&self) -> Vec<Expression<F>> {
        assert!(!self.is_big_endian);
        self.bytes.clone()
    }

    pub(crate) fn is_short(&self) -> Expression<F> {
        self.is_short.clone().unwrap()
    }

    pub(crate) fn is_long(&self) -> Expression<F> {
        self.is_long.clone().unwrap()
    }

    pub(crate) fn is_very_long(&self) -> Expression<F> {
        not::expr(self.is_short() + self.is_long())
    }

    pub(crate) fn word(&self) -> Word<Expression<F>> {
        assert!(self.can_use_word);
        self.word.clone().unwrap()
    }
}
