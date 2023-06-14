use crate::{
    assign, circuit,
    circuit_tools::{
        cached_region::{CachedRegion, ChallengeSet},
        cell_manager::{Cell, CellManager, CellType},
        constraint_builder::{
            ConstraintBuilder, RLCChainable, RLCChainableValue, RLCable, RLCableValue,
        },
        gadgets::{IsEqualGadget, LtGadget},
        memory::MemoryBank,
    },
    evm_circuit::table::Table,
    matchw,
    mpt_circuit::{
        param::{EMPTY_TRIE_HASH, KEY_LEN_IN_NIBBLES, KEY_PREFIX_EVEN, KEY_TERMINAL_PREFIX_EVEN, MAIN_RLP_STRING_MAX, MAIN_RLP_LIST_MAX},
        rlp_gadgets::{get_ext_odd_nibble, get_terminal_odd_nibble},
    },
    util::{Challenges, Expr},
};
use eth_types::Field;
use gadgets::util::{not, or, pow, Scalar};
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression, VirtualCells},
};

use super::{
    rlp_gadgets::{
        get_ext_odd_nibble_value, RLPItemGadget, RLPItemWitness, RLPListGadget, RLPListWitness,
    },
    FixedTableTag,
};

impl<F: Field> ChallengeSet<F> for crate::util::Challenges<Value<F>> {
    fn indexed(&self) -> Vec<&Value<F>> {
        self.indexed().to_vec()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MptCellType {
    StoragePhase1,
    StoragePhase2,
    StoragePermutation,
    LookupByte,
    Lookup(Table),
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
    fn byte_type() -> Option<Self> {
        Some(MptCellType::LookupByte)
    }

    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            0 => MptCellType::StoragePhase1,
            1 => MptCellType::StoragePhase2,
            _ => unreachable!(),
        }
    }
}

pub const FIXED: MptCellType = MptCellType::Lookup(Table::Fixed);
pub const KECCAK: MptCellType = MptCellType::Lookup(Table::Keccak);

/// Indexable object
pub trait Indexable {
    /// Convert to index
    fn idx(&self) -> usize;
}

impl Indexable for bool {
    fn idx(&self) -> usize {
        if *self {
            0
        } else {
            1
        }
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
                rlp_key.bytes()[0].expr(),
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
            matchx! {
                rlp_key.is_short() => {
                    // When no nibbles: only terminal prefix at `bytes[1]`.
                    // Else: Terminal prefix + single nibble  at `bytes[1]`
                    let is_odd = not!(self.has_no_nibbles);
                    calc_rlc(cb, &rlp_key.bytes()[0..1], is_odd)
                },
                rlp_key.is_long() => {
                    // First key byte is at `bytes[2]`.
                    calc_rlc(cb, &rlp_key.bytes()[1..34], is_key_odd.expr())
                },
            }
        })
    }

    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
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
        matchx! {
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
        }
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

    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
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
    pub(crate) fn load(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &MemoryBank<F, MptCellType>,
        offset: Expression<F>,
    ) -> Self {
        let key_data = KeyData {
            rlc: cb.query_cell(),
            mult: cb.query_cell(),
            num_nibbles: cb.query_cell(),
            is_odd: cb.query_cell(),
            drifted_rlc: cb.query_cell(),
            drifted_mult: cb.query_cell(),
            drifted_num_nibbles: cb.query_cell(),
            drifted_is_odd: cb.query_cell(),
        };
        circuit!([meta, cb.base], {
            memory.load(
                "key load",
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
    pub(crate) fn store(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &MemoryBank<F, MptCellType>,
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

    pub(crate) fn store_defaults(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &MemoryBank<F, MptCellType>,
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
    pub(crate) fn witness_store<S: ChallengeSet<F>>(
        _region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        memory: &mut MemoryBank<F, MptCellType>,
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

    pub(crate) fn witness_load<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        memory: &MemoryBank<F, MptCellType>,
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
    pub(crate) rlc: Cell<F>,
    pub(crate) is_root: Cell<F>,
    pub(crate) is_placeholder: Cell<F>,
    pub(crate) drifted_parent_rlc: Cell<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct ParentDataWitness<F> {
    pub(crate) rlc: F,
    pub(crate) is_root: bool,
    pub(crate) is_placeholder: bool,
    pub(crate) drifted_parent_rlc: F,
}

impl<F: Field> ParentData<F> {
    pub(crate) fn load(
        description: &'static str,
        cb: &mut MPTConstraintBuilder<F>,
        memory: &MemoryBank<F, MptCellType>,
        offset: Expression<F>,
    ) -> Self {
        let parent_data = ParentData {
            rlc: cb.query_cell(),
            is_root: cb.query_cell(),
            is_placeholder: cb.query_cell(),
            drifted_parent_rlc: cb.query_cell(),
        };
        circuit!([meta, cb.base], {
            memory.load(
                description,
                &mut cb.base,
                offset,
                &[
                    parent_data.rlc.expr(),
                    parent_data.is_root.expr(),
                    parent_data.is_placeholder.expr(),
                    parent_data.drifted_parent_rlc.expr(),
                ],
            );
        });
        parent_data
    }

    pub(crate) fn store(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &MemoryBank<F, MptCellType>,
        rlc: Expression<F>,
        is_root: Expression<F>,
        is_placeholder: Expression<F>,
        drifted_parent_rlc: Expression<F>,
    ) {
        memory.store(
            &mut cb.base,
            &[rlc, is_root, is_placeholder, drifted_parent_rlc],
        );
    }

    pub(crate) fn witness_store<S: ChallengeSet<F>>(
        _region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        memory: &mut MemoryBank<F, MptCellType>,
        rlc: F,
        force_hashed: bool,
        is_placeholder: bool,
        placeholder_rlc: F,
    ) -> Result<(), Error> {
        memory.witness_store(
            offset,
            &[
                rlc,
                force_hashed.scalar(),
                is_placeholder.scalar(),
                placeholder_rlc,
            ],
        );
        Ok(())
    }

    pub(crate) fn witness_load<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        memory: &MemoryBank<F, MptCellType>,
        load_offset: usize,
    ) -> Result<ParentDataWitness<F>, Error> {
        let values = memory.witness_load(load_offset);

        self.rlc.assign(region, offset, values[0])?;
        self.is_root.assign(region, offset, values[1])?;
        self.is_placeholder.assign(region, offset, values[2])?;
        self.drifted_parent_rlc.assign(region, offset, values[3])?;

        Ok(ParentDataWitness {
            rlc: values[0],
            is_root: values[1] == 1.scalar(),
            is_placeholder: values[2] == 1.scalar(),
            drifted_parent_rlc: values[3],
        })
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct MainData<F> {
    pub(crate) proof_type: Cell<F>,
    pub(crate) is_below_account: Cell<F>,
    pub(crate) address_rlc: Cell<F>,
    pub(crate) root_prev: Cell<F>,
    pub(crate) root: Cell<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct MainDataWitness<F> {
    pub(crate) proof_type: usize,
    pub(crate) is_below_account: bool,
    pub(crate) address_rlc: F,
    pub(crate) root_prev: F,
    pub(crate) root: F,
}

impl<F: Field> MainData<F> {
    pub(crate) fn load(
        description: &'static str,
        cb: &mut MPTConstraintBuilder<F>,
        memory: &MemoryBank<F, MptCellType>,
        offset: Expression<F>,
    ) -> Self {
        let main_data = MainData {
            proof_type: cb.query_cell(),
            is_below_account: cb.query_cell(),
            address_rlc: cb.query_cell(),
            root_prev: cb.query_cell(),
            root: cb.query_cell(),
        };
        circuit!([meta, cb.base], {
            memory.load(
                description,
                &mut cb.base,
                offset,
                &[
                    main_data.proof_type.expr(),
                    main_data.is_below_account.expr(),
                    main_data.address_rlc.expr(),
                    main_data.root_prev.expr(),
                    main_data.root.expr(),
                ],
            );
        });
        main_data
    }

    pub(crate) fn store(
        cb: &mut MPTConstraintBuilder<F>,
        memory: &MemoryBank<F, MptCellType>,
        values: [Expression<F>; 5],
    ) {
        memory.store(&mut cb.base, &values);
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn witness_store<S: ChallengeSet<F>>(
        _region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        memory: &mut MemoryBank<F, MptCellType>,
        proof_type: usize,
        is_below_account: bool,
        address_rlc: F,
        root_prev: F,
        root: F,
    ) -> Result<(), Error> {
        let values = [
            proof_type.scalar(),
            is_below_account.scalar(),
            address_rlc,
            root_prev,
            root,
        ];
        memory.witness_store(offset, &values);

        Ok(())
    }

    pub(crate) fn witness_load<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        memory: &MemoryBank<F, MptCellType>,
        load_offset: usize,
    ) -> Result<MainDataWitness<F>, Error> {
        let values = memory.witness_load(load_offset);

        self.proof_type.assign(region, offset, values[0])?;
        self.is_below_account.assign(region, offset, values[1])?;
        self.address_rlc.assign(region, offset, values[2])?;
        self.root_prev.assign(region, offset, values[3])?;
        self.root.assign(region, offset, values[4])?;

        Ok(MainDataWitness {
            proof_type: values[0].get_lower_32() as usize,
            is_below_account: values[1] == 1.scalar(),
            address_rlc: values[2],
            root_prev: values[3],
            root: values[4],
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
            challenges,
        }
    }

    pub(crate) fn set_use_dynamic_lookup(&mut self, use_dynamic_lookup: bool) {
        self.base.set_use_dynamic_lookup(use_dynamic_lookup);
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
        self.base.query_one(MptCellType::LookupByte)
    }

    pub(crate) fn query_bytes<const N: usize>(&mut self) -> [Cell<F>; N] {
        self.base
            .query_cells_dyn(MptCellType::LookupByte, N)
            .try_into()
            .unwrap()
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

    pub(crate) fn add_dynamic_lookup(
        &mut self,
        description: &'static str,
        tag: MptCellType,
        values: Vec<Expression<F>>,
    ) {
        self.base.add_dynamic_lookup(description, tag, values)
    }

    pub(crate) fn add_lookup(
        &mut self,
        description: &'static str,
        cell_type: MptCellType,
        values: Vec<Expression<F>>,
    ) {
        self.base.add_lookup(description, cell_type, values)
    }

    pub(crate) fn store_dynamic_table(
        &mut self,
        description: &'static str,
        tag: MptCellType,
        values: Vec<Expression<F>>,
    ) {
        self.base.store_dynamic_table(description, tag, values)
    }
}

/// Returns `1` when `value == 0`, and returns `0` otherwise.
#[derive(Clone, Debug, Default)]
pub struct IsEmptyTreeGadget<F> {
    is_in_empty_trie: IsEqualGadget<F>,
    is_in_empty_branch: IsEqualGadget<F>,
}

impl<F: Field> IsEmptyTreeGadget<F> {
    pub(crate) fn construct(
        cb: &mut MPTConstraintBuilder<F>,
        parent_rlc: Expression<F>,
        r: &Expression<F>,
    ) -> Self {
        circuit!([meta, cb.base], {
            let empty_root_rlc = EMPTY_TRIE_HASH
                .iter()
                .map(|v| v.expr())
                .collect::<Vec<_>>()
                .rlc(r);
            let is_in_empty_trie =
                IsEqualGadget::construct(&mut cb.base, parent_rlc.expr(), empty_root_rlc.expr());
            let is_in_empty_branch =
                IsEqualGadget::construct(&mut cb.base, parent_rlc.expr(), 0.expr());

            Self {
                is_in_empty_trie,
                is_in_empty_branch,
            }
        })
    }

    pub(crate) fn expr(&self) -> Expression<F> {
        or::expr(&[self.is_in_empty_trie.expr(), self.is_in_empty_branch.expr()])
    }

    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        parent_rlc: F,
        r: F,
    ) -> Result<(), Error> {
        self.is_in_empty_trie
            .assign(region, offset, parent_rlc, EMPTY_TRIE_HASH.rlc_value(r))?;
        self.is_in_empty_branch
            .assign(region, offset, parent_rlc, 0.scalar())?;
        Ok(())
    }
}

/// Handles drifted leaves
#[derive(Clone, Debug, Default)]
pub struct DriftedGadget<F> {
    drifted_rlp_key: ListKeyGadget<F>,
}

impl<F: Field> DriftedGadget<F> {
    pub(crate) fn construct(
        cb: &mut MPTConstraintBuilder<F>,
        parent_data: &[ParentData<F>],
        key_data: &[KeyData<F>],
        expected_key_rlc: &[Expression<F>],
        leaf_no_key_rlc: &[Expression<F>],
        drifted_item: &RLPItemView<F>,
        r: &Expression<F>,
    ) -> Self {
        let mut config = DriftedGadget::default();
        circuit!([meta, cb], {
            ifx! {parent_data[true.idx()].is_placeholder.expr() + parent_data[false.idx()].is_placeholder.expr() => {
                config.drifted_rlp_key = ListKeyGadget::construct(cb, drifted_item);
                for is_s in [true, false] {
                    ifx! {parent_data[is_s.idx()].is_placeholder.expr() => {
                        // Check that the drifted leaf is unchanged and is stored at `drifted_index`.
                        // TODO(Brecht): Length can change so need to add RLP consistency checks?

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

                        // Multiplier after list and key
                        let mult = config.drifted_rlp_key.rlp_list.rlp_mult(r) * drifted_item.mult();

                        // Complete the drifted leaf rlc by adding the bytes on the value row
                        let leaf_rlc = (config.drifted_rlp_key.rlc(r), mult.expr()).rlc_chain(leaf_no_key_rlc[is_s.idx()].expr());
                        // The drifted leaf needs to be stored in the branch at `drifted_index`.
                        require!((1, leaf_rlc, config.drifted_rlp_key.rlp_list.num_bytes(), parent_data[is_s.idx()].drifted_parent_rlc.expr()) => @KECCAK);
                    }
                }}
            }}
            config
        })
    }

    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
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
    wrong_mult: Cell<F>,
    is_key_equal: IsEqualGadget<F>,
    wrong_key: Option<Expression<F>>,
}

impl<F: Field> WrongGadget<F> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn construct(
        cb: &mut MPTConstraintBuilder<F>,
        expected_address: Expression<F>,
        is_non_existing: Expression<F>,
        key_value: &RLPItemView<F>,
        key_rlc: &Expression<F>,
        wrong_item: &RLPItemView<F>,
        is_in_empty_tree: Expression<F>,
        key_data: KeyData<F>,
        r: &Expression<F>,
    ) -> Self {
        let mut config = WrongGadget::default();
        circuit!([meta, cb.base], {
            // Get the previous key data
            ifx! {is_non_existing, not!(is_in_empty_tree) => {
                // Calculate the key
                config.wrong_rlp_key = ListKeyGadget::construct(cb, wrong_item);
                let key_rlc_wrong = key_data.rlc.expr() + config.wrong_rlp_key.key.expr(
                    cb,
                    config.wrong_rlp_key.key_value.clone(),
                    key_data.mult.expr(),
                    key_data.is_odd.expr(),
                    r,
                );
                // Check that it's the key as expected
                require!(key_rlc_wrong => expected_address);

                // Now make sure this address is different than the one of the leaf
                config.is_key_equal = IsEqualGadget::construct(
                    &mut cb.base,
                    key_rlc.expr(),
                    expected_address,
                );
                require!(config.is_key_equal => false);
                // Make sure the lengths of the keys are the same
                require!(config.wrong_rlp_key.key_value.len() => key_value.len());
            }}
            config
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        is_non_existing: bool,
        key_rlc: &[F],
        list_bytes: &[u8],
        wrong_item: &RLPItemWitness,
        for_placeholder_s: bool,
        key_data: KeyDataWitness<F>,
        r: F,
    ) -> Result<F, Error> {
        if is_non_existing {
            let wrong_witness = self
                .wrong_rlp_key
                .assign(region, offset, list_bytes, wrong_item)?;
            let (key_rlc_wrong, _) = wrong_witness.key.key(
                wrong_witness.key_item.clone(),
                key_data.rlc,
                key_data.mult,
                r,
            );

            self.is_key_equal.assign(
                region,
                offset,
                key_rlc[for_placeholder_s.idx()],
                key_rlc_wrong,
            )?;
            Ok(key_rlc_wrong)
        } else {
            Ok(key_rlc[for_placeholder_s.idx()])
        }
    }
}

/// Main RLP item
#[derive(Clone, Debug, Default)]
pub struct MainRLPGadget<F> {
    bytes: Vec<Cell<F>>,
    rlp: RLPItemGadget<F>,
    below_limit: LtGadget<F, 2>,
    num_bytes: Cell<F>,
    len: Cell<F>,
    mult_diff: Cell<F>,
    rlc_content: Cell<F>,
    rlc_rlp: Cell<F>,
    tag: Cell<F>,
}

impl<F: Field> MainRLPGadget<F> {
    pub(crate) fn construct(cb: &mut MPTConstraintBuilder<F>, r: &Expression<F>) -> Self {
        circuit!([meta, cb], {
            let mut config = MainRLPGadget {
                bytes: cb.query_cells::<34>().to_vec(),
                rlp: RLPItemGadget::default(),
                below_limit: LtGadget::default(),
                num_bytes: cb.query_cell(),
                len: cb.query_cell(),
                mult_diff: cb.query_cell(),
                rlc_content: cb.query_cell(),
                rlc_rlp: cb.query_cell(),
                tag: cb.query_cell(),
                // force_string: cb.query_cell(),
            };
            config.rlp = RLPItemGadget::construct(
                cb,
                &config
                    .bytes
                    .iter()
                    .map(|byte| byte.expr())
                    .collect::<Vec<_>>(),
            );
            

            let max_len = matchx!(
                config.rlp.is_string() => MAIN_RLP_STRING_MAX.expr(),
                config.rlp.is_list() => MAIN_RLP_LIST_MAX.expr(),
            );
            config.below_limit = LtGadget::construct(&mut cb.base, config.rlp.len(), max_len);
            require!(config.below_limit.expr() => true);

            require!(config.num_bytes => config.rlp.num_bytes());
            require!(config.len => config.rlp.len());
            require!(config.rlc_content => config.rlp.rlc_content(r));
            require!(config.rlc_rlp => config.rlp.rlc_rlp(cb, r));
            let mult_diff = config.mult_diff.expr();
            require!((FixedTableTag::RMult, config.rlp.num_bytes(), mult_diff) => @FIXED);
            // `tag` is a "free" input that needs to be constrained externally!

            // Range/zero checks
            // These range checks ensure that the value in the RLP columns are all byte
            // value. These lookups also enforce the byte value to be zero when
            // the byte index >= num_bytes.
            // TODO(x Brecht): do 2 bytes/lookup when circuit height >= 2**21
            // We enable dynamic lookups because otherwise these lookup would require a lot of extra
            // cells.
            cb.set_use_dynamic_lookup(true);
            for (idx, byte) in config.bytes.iter().enumerate() {
                // endien problem
                // after 3 bytes, the rest should be 0
                require!((config.tag.expr(), byte.expr(), config.num_bytes.expr() - idx.expr()) => @FIXED);
            }
            cb.set_use_dynamic_lookup(false);

            config
        })
    }

    pub(crate) fn assign<S: ChallengeSet<F>>(
        &self,
        region: &mut CachedRegion<'_, '_, F, S>,
        offset: usize,
        bytes: &[u8],
        r: F,
        is_nibbles: bool,
    ) -> Result<RLPItemWitness, Error> {
        // Assign the bytes
        for (byte, column) in bytes.iter().zip(self.bytes.iter()) {
            assign!(region, (column.column(), offset) => byte.scalar())?;
        }

        // Decode the RLP item
        let rlp_witness = self.rlp.assign(region, offset, bytes)?;
        let max_len = match rlp_witness.is_string() {
            true => MAIN_RLP_STRING_MAX,
            false => MAIN_RLP_LIST_MAX,
        };
        self.below_limit.assign(region, offset, rlp_witness.len().scalar(), max_len.scalar())?;

        // Store RLP properties for easy access
        self.num_bytes
            .assign(region, offset, rlp_witness.num_bytes().scalar())?;
        self.len
            .assign(region, offset, rlp_witness.len().scalar())?;

        self.mult_diff
            .assign(region, offset, pow::value(r, rlp_witness.num_bytes()))?;

        self.rlc_content
            .assign(region, offset, rlp_witness.rlc_content(r))?;
        self.rlc_rlp
            .assign(region, offset, rlp_witness.rlc_rlp(r))?;

        assign!(region, self.tag, offset => self.tag(is_nibbles).scalar())?;

        Ok(rlp_witness)
    }

    pub(crate) fn create_view(
        &self,
        meta: &mut VirtualCells<F>,
        cb: &mut MPTConstraintBuilder<F>,
        rot: usize,
        is_nibbles: bool,
    ) -> RLPItemView<F> {
        circuit!([meta, cb.base], {
            require!(self.tag.rot(meta, rot) => self.tag(is_nibbles).expr());
        });
        RLPItemView {
            num_bytes: Some(self.num_bytes.rot(meta, rot)),
            len: Some(self.len.rot(meta, rot)),
            mult_diff: Some(self.mult_diff.rot(meta, rot)),
            rlc_content: Some(self.rlc_content.rot(meta, rot)),
            rlc_rlp: Some(self.rlc_rlp.rot(meta, rot)),
            bytes: self.bytes.iter().map(|byte| byte.rot(meta, rot)).collect(),
            is_short: Some(self.rlp.value.is_short.rot(meta, rot)),
            is_long: Some(self.rlp.value.is_long.rot(meta, rot)),
        }
    }

    fn tag(&self, is_nibbles: bool) -> FixedTableTag {
        if is_nibbles {
            FixedTableTag::RangeKeyLen16
        } else {
            FixedTableTag::RangeKeyLen256
        }
    }
}

/// Main RLP item
#[derive(Clone, Debug, Default)]
pub struct RLPItemView<F> {
    pub(crate) bytes: Vec<Expression<F>>,
    pub(crate) num_bytes: Option<Expression<F>>,
    pub(crate) len: Option<Expression<F>>,
    pub(crate) mult_diff: Option<Expression<F>>,
    pub(crate) rlc_content: Option<Expression<F>>,
    pub(crate) rlc_rlp: Option<Expression<F>>,
    pub(crate) is_short: Option<Expression<F>>,
    pub(crate) is_long: Option<Expression<F>>,
}

impl<F: Field> RLPItemView<F> {
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        self.num_bytes.clone().unwrap()
    }

    pub(crate) fn len(&self) -> Expression<F> {
        self.len.clone().unwrap()
    }

    pub(crate) fn mult(&self) -> Expression<F> {
        self.mult_diff.clone().unwrap()
    }

    pub(crate) fn rlc_content(&self) -> Expression<F> {
        self.rlc_content.clone().unwrap()
    }

    pub(crate) fn rlc_rlp(&self) -> Expression<F> {
        self.rlc_rlp.clone().unwrap()
    }

    pub(crate) fn rlc(&self) -> (Expression<F>, Expression<F>) {
        (self.rlc_content(), self.rlc_rlp())
    }

    pub(crate) fn bytes(&self) -> Vec<Expression<F>> {
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
}
