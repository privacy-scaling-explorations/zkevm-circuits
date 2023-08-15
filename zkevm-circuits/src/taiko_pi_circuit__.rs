//! Use the hash value as public input.

use crate::{
    evm_circuit::table::Table::*,
    evm_circuit::{util::{constraint_builder::{BaseConstraintBuilder, ConstrainBuilderCommon}, rlc}, table::Table},
    table::{byte_table::ByteTable, BlockContextFieldTag, BlockTable, KeccakTable, LookupTable},
    util::{random_linear_combine_word as rlc, Challenges, SubCircuit, SubCircuitConfig},
    circuit_tools::{
        constraint_builder::{ConstraintBuilder, TO_FIX, COMPRESS, REDUCE},
        cell_manager::{CellManager, CellType, Cell}, gadgets::IsEqualGadget,
    },
    
    witness::{self, BlockContext}, circuit,
};
use eth_types::{Address, Field, ToBigEndian, ToWord, Word, H256};
use ethers_core::utils::keccak256;
use gadgets::{util::{or, select, Expr, and}, impl_expr};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, SecondPhase,
        Selector, VirtualCells,
    },
    poly::Rotation,
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

/// Field Bytes
#[derive(Clone, Debug, Default)]
pub struct FieldBytesGadget<F> {
    bytes: [Cell<F>; N],
    block_idx: Option<Cell<F>>,
    keccak_input: Option<Cell<F>>,
    // len: Cell<F>,
    // acc: Cell<F>,
    // is_keccak: IsEqualGadget<F>,
    // is_block: IsEqualGadget<F>,
}

impl<F: Field> FieldBytesGadget<F> {

    fn config(&mut self, cb: &mut ConstraintBuilder<F, PiCellType>) {
        self.bytes = cb.query_bytes();
    } 

    fn bytes_expr(&self, range: Range<usize>) -> Vec<Expression<F>> {
        assert!(range.end < N);
        range.map(|i| self.bytes[i].expr()).collect()
    }

    fn hi_low_fields(&self) -> (Expression<F>, Expression<F>){
        (
            rlc::expr(&self.bytes_expr(0..N/2), BYTE_POW_BASE.expr()),
            rlc::expr(&self.bytes_expr(N/2..N), BYTE_POW_BASE.expr()),
        )
    }

    fn evm_word_field(&self, challenges: Challenges<Expression<F>>) -> Expression<F> {
        rlc::expr(&self.bytes_expr(0..N), challenges.evm_word().expr())
    }

    fn keccak_field(&self, challenges: Challenges<Expression<F>>) -> Expression<F> {
        rlc::expr(&self.bytes_expr(0..N), challenges.keccak_input().expr())
    }

    fn keccak_input_acc(&self, challenges: Challenges<Expression<F>>, prev_field: Expression<F>) -> Expression<F> {
        let raise_exp = (0..self.bytes.len())
            .fold(1.expr(), |acc: Expression<F>, _|acc * challenges.keccak_input().expr());
        prev_field * raise_exp + self.keccak_field(challenges.clone())
    }

    fn keccak_output_acc(&self, challenges: Challenges<Expression<F>>) -> Expression<F> {
        let raise_exp = (0..self.bytes.len())
            .fold(1.expr(), |acc: Expression<F>, _|acc * challenges.evm_word().expr());
        let (hi, low) = self.hi_low_fields();
        hi * raise_exp + low
    }

    fn set_keccak_input(
        &mut self, 
        cb: &mut ConstraintBuilder<F, PiCellType>,
        keccak_input_acc: Expression<F>,
        challenges: Challenges<Expression<F>>,
    ) {
        let keccak_input = cb.query_cell_with_type(PiCellType::Storage2);
        cb.require_equal(
            "Copy keccak input from acc column to temporary cell", 
            keccak_input_acc, 
            keccak_input.expr()
        );
    }

    fn keccak_lookup(
        &mut self, 
        cb: &mut ConstraintBuilder<F, PiCellType>,
        challenges: Challenges<Expression<F>>,
    ) -> (Expression<F>, Expression<F>, Expression<F>, Expression<F>) {
        if let Some(input) = self.keccak_input.clone() {
            return (
                1.expr(),
                input.expr(),
                RPI_BYTES_LEN.expr(),
                self.keccak_output_acc(challenges)
            )
        } else {
            panic!("Cannot configure keccak lookup without input");
        }
    }

    fn block_hash_lookup(
        &mut self, 
        cb: &mut ConstraintBuilder<F, PiCellType>,
        challenges: Challenges<Expression<F>>,
    ) -> (Expression<F>, Expression<F>, Expression<F>) {
        let block_idx = cb.query_default();
        self.block_idx = Some(block_idx.clone());
        (
            BlockContextFieldTag::BlockHash.expr(),
            block_idx.expr(),
            self.evm_word_field(challenges)
        )
    }

    // fn bytes_lookup(
    //     &mut self, 
    //     cb: &mut ConstraintBuilder<F, PiCellType>,
    // ) {
    //     circuit!([meta, cb], {
    //         for byte in self.bytes {
    //             require!((byte.expr()) => @PiCellType::Lookup(Table::Bytecode), (TO_FIX));
    //         }
    //     });
    // }
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

///
#[derive(Clone, Copy)]
pub enum PiState {
    ///
    Start,
    ///
    Block,
    ///
    Last,
}
impl_expr!(PiState);


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
            let cm = CellManager::new(
                meta,
                vec![
                    (PiCellType::Byte, 32, 1, false),
                    (PiCellType::Storage1, 3, 2, false),
                ],
                0,
                1,
            );
            let mut cb: ConstraintBuilder<F, PiCellType> =  ConstraintBuilder::new(4,  Some(cm), Some(challenges.evm_word()));
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
            meta.create_gate(
                "PI acc constraints", 
                |meta| {
                    circuit!([meta, cb], {
                        let q_block = IsEqualGadget::construct(&mut cb, a!(field_idx), PiState::Block.expr());
                        let q_last_field = IsEqualGadget::construct(&mut cb, a!(field_idx), PiState::Last.expr());
                        field_gadget.config(&mut cb);
                        ifx! (Self::is_block_field(&mut cb, a!(field_idx)) => {
                            // do this directly in column
                            // field_gadget.bytes_lookup(&mut cb);
                            require!(
                                a!(block_acc, 1) => field_gadget.keccak_input_acc(challenges.clone(), a!(block_acc))
                            );
                            ifx!(q_block.expr() => {
                                let data = field_gadget.block_hash_lookup(&mut cb, challenges.clone());
                                require!((data.0, data.1, data.2) => @PiCellType::Lookup(Table::Block), (COMPRESS, REDUCE));
                            }); 
                            ifx!(q_last_field.expr() => {
                                field_gadget.set_keccak_input(&mut cb, a!(block_acc), challenges.clone());
                            });
                        } elsex {
                            let data = field_gadget.keccak_lookup(&mut cb, challenges.clone());
                            require!((data.0, data.1, data.2, data.3) => @PiCellType::Lookup(Table::Keccak), (COMPRESS, REDUCE));
                        });
                    });
                    cb.build_constraints()
                }
            );
            Self {
                field_idx,
                block_acc,
                field_gadget
            }
        }

}

impl<F: Field> TaikoPiCircuitConfig<F> {

    fn is_block_field(
        cb: &mut ConstraintBuilder<F, PiCellType>,
        field_idx: Expression<F>
    ) -> Expression<F> {
        let mut expr = 0.expr();
        circuit!([meta, cb], {
            let is_block_field = (0..9)
                .fold(1.expr(), |acc, item| acc * (field_idx.clone() - item.expr()));
            expr = cb.local_processing(
                "is_block_field range check", 
                &[is_block_field], 
                PiCellType::Storage1,
                None, 
                true, 
                true
            )[0].clone();
        });
        expr
    }
}