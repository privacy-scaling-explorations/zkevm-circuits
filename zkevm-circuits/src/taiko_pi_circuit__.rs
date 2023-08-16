//! Use the hash value as public input.

use crate::{
    assign,
    evm_circuit::table::Table::*,
    evm_circuit::{util::{constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon}, rlc}, table::Table},
    table::{byte_table::ByteTable, BlockContextFieldTag, BlockTable, KeccakTable, LookupTable},
    util::{Challenges, SubCircuitConfig},
    circuit_tools::{
        constraint_builder::{ConstraintBuilder, RLCable, RLCChainable, TO_FIX, COMPRESS, REDUCE, RLCableValue},
        cell_manager::{CellManager, CellType, Cell}, gadgets::IsEqualGadget, cached_region::{CachedRegion, self},
    },
    
    witness::{self, BlockContext}, circuit,
};
use gadgets::util::Scalar;
use eth_types::{Address, Field, ToBigEndian, ToWord, Word, H256};
use ethers_core::utils::keccak256;
use gadgets::{util::{or, select, Expr, and}, impl_expr};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, SecondPhase,
        Selector, VirtualCells,
    },
    poly::{Rotation},
};
use std::{marker::PhantomData, ops::Range, usize, default};

const BYTE_POW_BASE: u64 = 1 << 8;
const N: usize = 32;
const RPI_BYTES_LEN: usize = 32 * 10;


/// PublicData contains all the values that the PiCircuit receives as input
#[derive(Debug, Clone, Default)]
pub struct PublicData {
    /// l1 signal service address
    pub l1_signal_service: Word,
    /// l2 signal service address
    pub l2_signal_service: Word,
    /// l2 contract address
    pub l2_contract: Word,
    /// meta hash
    pub meta_hash: Word,
    /// block hash value
    pub block_hash: Word,
    /// the parent block hash
    pub parent_hash: Word,
    /// signal root
    pub signal_root: Word,
    /// extra message
    pub graffiti: Word,
    /// union field
    pub field9: Word, // prover[96:256]+parentGasUsed[64:96]+gasUsed[32:64]
    /// union field
    pub field10: Word, /* blockMaxGasLimit[192:256]+maxTransactionsPerBlock[128:
                        * 192]+maxBytesPerTxList[64:128] */

    // privates
    // Prover address
    prover: Address,
    // parent block gas used
    parent_gas_used: u32,
    // block gas used
    gas_used: u32,
    // blockMaxGasLimit
    block_max_gas_limit: u64,
    // maxTransactionsPerBlock: u64,
    max_transactions_per_block: u64,
    // maxBytesPerTxList: u64,
    max_bytes_per_tx_list: u64,

    block_context: BlockContext,
    chain_id: Word,
}

impl PublicData {
    fn assignments(&self) -> [(&'static str, Option<Word>, [u8; 32]); 10] {
        let res = [
            (
                "l1_signal_service",
                None,
                self.l1_signal_service.to_be_bytes(),
            ),
            (
                "l2_signal_service",
                None,
                self.l2_signal_service.to_be_bytes(),
            ),
            ("l2_contract", None, self.l2_contract.to_be_bytes()),
            ("meta_hash", None, self.meta_hash.to_be_bytes()),
            (
                "parent_hash",
                Some(self.block_context.number - 1),
                self.parent_hash.to_be_bytes(),
            ),
            (
                "block_hash",
                Some(self.block_context.number),
                self.block_hash.to_be_bytes(),
            ),
            ("signal_root", None, self.signal_root.to_be_bytes()),
            ("graffiti", None, self.graffiti.to_be_bytes()),
            (
                "prover+parentGasUsed+gasUsed",
                None,
                self.field9.to_be_bytes(),
            ),
            (
                "blockMaxGasLimit+maxTransactionsPerBlock+maxBytesPerTxList",
                None,
                self.field10.to_be_bytes(),
            ),
        ];
        res.iter().for_each(|field|{
            println!("{:?}, len {:?}", field.0, field.2.len());
        });
        res
    }

    /// get rpi bytes
    pub fn rpi_bytes(&self) -> Vec<u8> {
        self.assignments().iter().flat_map(|v| v.2).collect()
    }

    fn default<F: Default>() -> Self {
        Self::new::<F>(&witness::Block::default())
    }

    /// create PublicData from block and taiko
    pub fn new<F>(block: &witness::Block<F>) -> Self {
        use witness::left_shift;
        let field9 = left_shift(block.protocol_instance.prover, 96)
            + left_shift(block.protocol_instance.parent_gas_used as u64, 64)
            + left_shift(block.protocol_instance.gas_used as u64, 32);

        let field10 = left_shift(block.protocol_instance.block_max_gas_limit, 192)
            + left_shift(block.protocol_instance.max_transactions_per_block, 128)
            + left_shift(block.protocol_instance.max_bytes_per_tx_list, 64);
        PublicData {
            l1_signal_service: block.protocol_instance.l1_signal_service.to_word(),
            l2_signal_service: block.protocol_instance.l2_signal_service.to_word(),
            l2_contract: block.protocol_instance.l2_contract.to_word(),
            meta_hash: block.protocol_instance.meta_hash.hash().to_word(),
            block_hash: block.protocol_instance.block_hash.to_word(),
            parent_hash: block.protocol_instance.parent_hash.to_word(),
            signal_root: block.protocol_instance.signal_root.to_word(),
            graffiti: block.protocol_instance.graffiti.to_word(),
            prover: block.protocol_instance.prover,
            parent_gas_used: block.protocol_instance.parent_gas_used,
            gas_used: block.protocol_instance.gas_used,
            block_max_gas_limit: block.protocol_instance.block_max_gas_limit,
            max_transactions_per_block: block.protocol_instance.max_transactions_per_block,
            max_bytes_per_tx_list: block.protocol_instance.max_bytes_per_tx_list,
            field9,
            field10,
            block_context: block.context.clone(),
            chain_id: block.context.chain_id,
        }
    }

    fn get_pi(&self) -> H256 {
        let rpi_bytes = self.rpi_bytes();
        let rpi_keccak = keccak256(rpi_bytes);
        H256(rpi_keccak)
    }
}



/// Config for PiCircuit
#[derive(Clone, Debug)]
pub struct TaikoPiCircuitConfig<F: Field> {
    field_idx: Column<Advice>,
    block_acc: Column<Advice>,
    field_gadget: FieldBytesGadget<F>,
}

/// Circuit configuration arguments
pub struct TaikoPiCircuitConfigArgs<F: Field> {
    /// BlockTable
    pub block_table: BlockTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// ByteTable
    pub byte_table: ByteTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

/// 
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PiCellType {
    ///
    Storage1,
    ///
    Storage2,
    ///
    Byte,
    ///
    Lookup(Table)
}
impl CellType for PiCellType {
    fn byte_type() -> Option<Self> {
        Some(Self::Byte)
    }
    fn storage_for_phase(phase: u8) -> Self {
        match phase {
            1 => PiCellType::Storage1,
            2 => PiCellType::Storage2,
            _ => unimplemented!()
        }
    }
}
impl Default for PiCellType {
    fn default() -> Self {
        Self::Storage1
    }
}

#[derive(Clone, Copy)]
enum PiState {
    L1Signal,
    L2Signal,
    L2Contract,
    MetaHash,
    ParentHash,
    BlockHash,
    SignalRoot,
    Graffiti,
    Field9,
    Field10,
    
    KeccakHi,
    KeccakLow,
}
impl_expr!(PiState);
impl Into<usize> for PiState {
    fn into(self) -> usize {
        self as usize
    }
}

impl<F: Field> SubCircuitConfig<F> for TaikoPiCircuitConfig<F> {
    type ConfigArgs = TaikoPiCircuitConfigArgs<F>;

        /// Return a new TaikoPiCircuitConfig
        fn new(
            meta: &mut ConstraintSystem<F>,
            Self::ConfigArgs {
                block_table,
                keccak_table,
                byte_table,
                challenges,
            }: Self::ConfigArgs,
        ) -> Self {
            let field_cm = CellManager::new(
                meta,
                vec![(PiCellType::Byte, 32, 1, false)],
                0,
                1,
            );
            let state_cm = CellManager::new(
                meta,
                vec![
                    (PiCellType::Storage1, 2, 1, false),
                    (PiCellType::Storage2, 2, 2, false),
                    ],
                    0,
                    5,
            );
            let mut cb: ConstraintBuilder<F, PiCellType> =  ConstraintBuilder::new(4,  Some(field_cm), Some(challenges.evm_word()));
            cb.preload_tables(meta,
                &[
                   (PiCellType::Lookup(Keccak), &keccak_table), 
                   (PiCellType::Lookup(Bytecode), &byte_table), 
                   (PiCellType::Lookup(Block), &block_table)
                   ]
               );

            
            let field_idx = meta.advice_column();
            let block_acc = meta.advice_column();
            let mut field_gadget = FieldBytesGadget::default();
            field_gadget.challenges = Some(challenges.clone());
            meta.create_gate(
                "PI acc constraints", 
                |meta| {
                    circuit!([meta, cb], {
                        cb.set_cell_manager(state_cm.clone());
                        let is_block_fields = Self::is_block_field(&mut cb, a!(field_idx));
                        let q_block = Self::idx_range(&mut cb, a!(field_idx), &[PiState::ParentHash, PiState::BlockHash]);
                        let q_keccak = Self::idx_range(&mut cb, a!(field_idx), &[PiState::KeccakLow]);
                        let q_last_field = Self::idx_range(&mut cb, a!(field_idx), &[PiState::Field10]);

                        field_gadget.config(&mut cb);
                        ifx! (is_block_fields => {
                            // do this directly in column
                            // field_gadget.bytes_lookup(&mut cb);
                            require!(
                                a!(block_acc, 1) => field_gadget.block_input_acc(a!(block_acc))
                            );
                            ifx!(q_block.expr() => {
                                let block_number = field_gadget.set_block_number(&mut cb);
                                require!(
                                    (
                                        BlockContextFieldTag::BlockHash.expr(),
                                        block_number.expr(),
                                        field_gadget.evm_word_field()
                                    ) => @PiCellType::Lookup(Table::Block), (COMPRESS, REDUCE)
                                );
                            }); 
                            // On the last bytes of the last field
                            // the we copy block_acc to a tmp cell in field_gadget
                            ifx!(q_last_field.expr() => {
                                field_gadget.set_keccak_input(&mut cb, a!(block_acc));
                            });
                        } elsex {
                            // block_acc should be reset to 0
                            require!(
                                a!(block_acc, 1) => field_gadget.keccak_output_acc(a!(block_acc))
                            );
                            ifx!(q_keccak.expr() => {
                                require!(
                                    (
                                        1.expr(),
                                        field_gadget.keccak_input.clone().unwrap().expr(),
                                        RPI_BYTES_LEN.expr(),
                                        a!(block_acc)
                                    )
                                    => @PiCellType::Lookup(Table::Keccak), (COMPRESS, REDUCE));
                            });
                        });
                    });
                    cb.build_constraints()
                }
            );
            cb.build_equalities(meta);
            cb.build_lookups(
                meta, 
                &[state_cm], 
                &[
                    (PiCellType::Byte, PiCellType::Lookup(Bytecode)),
                    (PiCellType::Lookup(Table::Keccak), PiCellType::Lookup(Table::Keccak)),
                    (PiCellType::Lookup(Table::Block), PiCellType::Lookup(Table::Block)),
                ]
            );
            Self {
                field_idx,
                block_acc,
                field_gadget: field_gadget
            }
        }

}

impl<F: Field> TaikoPiCircuitConfig<F> {

    fn idx_range(
        cb: &mut ConstraintBuilder<F, PiCellType>,
        field_idx: Expression<F>,
        range: &[PiState]
    ) -> Expression<F> {
        let mut expr = 0.expr();
        circuit!([meta, cb], {
            let is_block_field = range.iter()
                .fold(1.expr(), |acc, item| acc * (field_idx.clone() - item.expr()));
            expr = cb.local_processing(
                "field idx range check", 
                &[is_block_field], 
                PiCellType::Storage1,
                None, 
                true, 
                true
            )[0].clone();
        });
        expr
    }

    fn is_block_field(
        cb: &mut ConstraintBuilder<F, PiCellType>,
        field_idx: Expression<F>
    ) -> Expression<F> {
        Self::idx_range(
            cb, 
            field_idx, 
        &[
                PiState::L1Signal, 
                PiState::L2Signal, 
                PiState::L2Contract, 
                PiState::MetaHash, 
                PiState::ParentHash,
                PiState::BlockHash,
                PiState::SignalRoot, 
                PiState::Graffiti, 
                PiState::Field9, 
                PiState::Field10
            ]
        )
    }

    pub(crate) fn assign(
        &self,
        layouter: &mut impl Layouter<F>,
        public_data: &PublicData,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Pi",
            |mut region| {
                let mut cached_region = CachedRegion::new(&mut region);
                let mut r = F::ZERO;
                let mut block_acc = F::ZERO;
                let mut offset = 0;
                println!("\n===================");
                for (i, (annotation, block_number, bytes)) in public_data
                    .assignments()
                    .iter()
                    .enumerate() {
                        println!("{:?}, len {:?}， offset {:?}", annotation, bytes.len(), offset);
                        match i {
                            i if i <= PiState::Field10.into() => {
                                challenges.keccak_input().map(|v| r = v);
                                block_acc += self.field_gadget.assign_bytes(&mut cached_region, r, offset, bytes.as_ref())?;
                                let block_acc_cell = assign!(cached_region, (self.block_acc, offset) => block_acc)?;
                                if let Some(block_number) = block_number {
                                    self.field_gadget.assign_block_number(
                                        &mut cached_region, 
                                        offset, 
                                        block_number.as_u64().scalar()
                                    );                                    
                                }
                                
                                if i == PiState::Field10 as usize {
                                    self.field_gadget.assign_keccak_acc(
                                        &mut cached_region, 
                                        offset,
                                        block_acc_cell
                                    );
                                    block_acc = F::ZERO;
                                }
                            },
                            i if i >= PiState::KeccakHi.into() => {
                                challenges.evm_word().map(|v| r = v);
                                block_acc += self.field_gadget.assign_bytes(&mut cached_region, r, offset, bytes.as_ref())?;
                                assign!(cached_region, (self.block_acc, offset) => block_acc)?;

                            },
                            _ => unreachable!(),
                        }
                    }
                Ok(())
            },
        )
    }
}

/// Field Bytes
#[derive(Clone, Debug, Default)]
pub struct FieldBytesGadget<F> {
    challenges: Option<Challenges<Expression<F>>>,
    bytes: [Cell<F>; N],
    block_number: Option<Cell<F>>,
    keccak_input: Option<Cell<F>>,
}

impl<F: Field> FieldBytesGadget<F> {

    fn config(&mut self, cb: &mut ConstraintBuilder<F, PiCellType>) {
        self.bytes = cb.query_bytes();
    } 

    fn bytes_expr(&self) -> Vec<Expression<F>> {
        self.bytes.iter().map(|b| b.expr()).collect()
    }

    /// RLC of bytes of a field with evm_word 1<<8
    fn hi_low_fields_(&self) -> Expression<F> {
        self.bytes_expr().rlc(&BYTE_POW_BASE.expr())
    }

    /// RLC of bytes of a field with evm_word
    fn evm_word_field(&self) -> Expression<F> {
        let r = self.challenges.clone().unwrap().evm_word().expr();
        self.bytes_expr().rlc(&r)
    }

    /// RLC of bytes of a field with keccak_input
    fn keccak_field(&self) -> Expression<F> {
        let r = self.challenges.clone().unwrap().keccak_input().expr();
        self.bytes_expr().rlc(&r)
    }
    
    // ------------------ Acc ------------------

    /// Next value of block field bytes RLC accumulator for keccak input
    fn block_input_acc(&self, prev_field: Expression<F>) -> Expression<F> {
        let r = self.challenges.clone().unwrap().keccak_input().expr();
        let raise_exp = (0..self.bytes.len())
            .fold(1.expr(), |acc: Expression<F>, _|acc * r.clone());
        prev_field * raise_exp + self.keccak_field()
    }

    /// Next value of keccak output hi low bytes accumulator
    fn keccak_output_acc(&self, hi: Expression<F>) -> Expression<F> {
        let r = self.challenges.clone().unwrap().evm_word().expr();
        let raise_exp = (0..self.bytes.len())
            .fold(1.expr(), |acc: Expression<F>, _|acc * r.clone());
        let low = self.hi_low_fields_();
        hi * raise_exp + low
    }

    // ------------------ Set Cell ------------------


    /// Init a cell for keccak input at the last row of all block fields
    fn set_keccak_input(
        &mut self, 
        cb: &mut ConstraintBuilder<F, PiCellType>,
        keccak_input_acc: Expression<F>,
    ) -> Expression<F> {
        let keccak_input = cb.query_cell_with_type(PiCellType::Storage2);
        cb.enable_equality(keccak_input.column());
        // cb.require_equal(
        //     "Copy keccak input from acc column to temporary cell", 
        //     keccak_input_acc, 
        //     keccak_input.expr()
        // );
        keccak_input.expr()
    }

    /// Init a cell for block idx when we need to lookup block table
    fn set_block_number(&mut self, cb: &mut ConstraintBuilder<F, PiCellType>) -> Expression<F> {
        let block_number = cb.query_default();
        self.block_number = Some(block_number.clone());
        block_number.expr()
    }

    // ------------------ Assign ------------------

    /// Returns the rlc of given bytes
    pub(crate) fn assign_bytes(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        r: F,
        offset: usize,
        bytes: &[u8],
    ) -> Result<F, Error> {
        // Assign the bytes
        for (byte, column) in bytes.iter().zip(self.bytes.iter()) {
            assign!(region, (column.column(), offset) => byte.scalar())?;
        }
        let mut rlc = bytes.rlc_value(r);
        Ok(rlc)
    }

    pub(crate) fn assign_block_number(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block_number: F,
    ) -> Result<(), Error> {
        if let Some(cell) = &self.block_number {
            cell.assign(region, offset, block_number)?;
            Ok(())
        } else {
            Err(Error::Synthesis)
        }
    }

    pub(crate) fn assign_keccak_acc(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block_acc_cell: AssignedCell<F, F>,
    ) -> Result<(), Error> {
        if let Some(cell) = &self.keccak_input {
            block_acc_cell.copy_advice(
                || "Copy block acc into cell for keccak input", 
                region.inner(), 
                cell.column(), 
                offset
            )?;
            Ok(())
        } else {
            Err(Error::Synthesis)
        }
    }
}