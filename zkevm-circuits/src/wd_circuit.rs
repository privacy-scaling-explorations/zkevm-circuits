//! The withdrawal circuit implementation.

use crate::{
    table::{BlockTable, KeccakTable, LookupTable, MptTable, WdTable, MPTProofType},
    util::{word::Word, Challenges, SubCircuit, SubCircuitConfig},
    witness::{self, MptUpdateRow}, evm_circuit::util::from_bytes, mpt_circuit::MainRLPGadget, circuit_tools::{cached_region::CachedRegion, cell_manager::CellColumn, gadgets::IsZeroGadget},
};
use bus_mapping::circuit_input_builder::Withdrawal;
use eth_types::{keccak256, Field, U256};
use gadgets::util::not;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression}, poly::Rotation,
}; 

/// Config for WdCircuit 
#[derive(Clone, Debug)]
pub struct WdCircuitConfig<F: Field> {
    // withdrawal fields
    id: Column<Advice>,
    validator_id: Column<Advice>,
    address: Word<Column<Advice>>,
    amount: Column<Advice>,

    // intermediate mpt root
    root: Word<Column<Advice>>,
    
    // 
    // keccak of above fields encoded in rlp
    hash: Word<Column<Advice>>,
    //  
    rlp_item: MainRLPGadget<F>,  
    // cell_columns: Vec<CellColumn<F, MptCellType>>,

    amount_is_zero: IsZeroGadget<F>,

    // external table
    pub mpt_table: MptTable, 

    // _marker: PhantomData<F>,
}

/// Circuit configuration arguments
pub struct WdCircuitConfigArgs<F: Field> {
    /// WdTable
    pub wd_table: WdTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// BlockTable
    pub block_table: BlockTable,
    /// MptTable
    pub mpt_table: MptTable, 
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for WdCircuitConfig<F> {
    type ConfigArgs = WdCircuitConfigArgs<F>;

    /// Return a new WdCircuitConfig
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            wd_table,
            keccak_table,
            block_table,
            mpt_table,
            challenges,
        }: Self::ConfigArgs,
    ) -> Self {
        wd_table.annotate_columns(meta);
        keccak_table.annotate_columns(meta);
        block_table.annotate_columns(meta);
        mpt_table.annotate_columns(meta);

        let id = wd_table.id;
        let validator_id = wd_table.validator_id;
        let address = wd_table.address;
        let amount = wd_table.amount;
        meta.enable_equality(wd_table.id);
        meta.enable_equality(wd_table.validator_id);
        meta.enable_equality(wd_table.address.lo());
        meta.enable_equality(wd_table.address.hi());
        meta.enable_equality(wd_table.amount);

        meta.enable_equality(block_table.value.lo());
        meta.enable_equality(block_table.value.hi());

        let hash = Word::new([meta.advice_column(), meta.advice_column()]);
        let root = Word::new([meta.advice_column(), meta.advice_column()]);

      
        
        // keccak lookup?
        meta.lookup_any( 
            "keccak256_table_lookup(rlp_item.rlc_rlp, rlp_item.num_bytes, cur.hash)",
            |meta| {
                let is_zero_amount = IsZeroGadget::construct(meta, wd_table.amount.cur());
                let enable = not::expr(is_zero_amount);

                let mut constraints = vec![(
                    enable,
                    meta.query_advice(keccak_table.is_enabled, Rotation::cur()),
                )];


                for (circuit_column, table_column) in
                    keccak_table.match_columns(rlp_item.rlc_rlp, rlp_item.num_bytes, hash)
                {
                    constraints.push((
                        enable.clone() * meta.query_advice(circuit_column, Rotation::cur()),
                        meta.query_advice(table_column, Rotation::cur()),
                    ))
                }

                constraints
            },
        );

        // mpt lookup
        let mpt_table = MptTable {
            address: address,
            storage_key: id,
            proof_type: meta.advice_column(),
            new_root: root,
            old_root: meta.query_advice(root, Rotation::prev()),
            new_value: hash,
            old_value: meta.query_advice(hash, Rotation::prev()),
        };

        for col in [
            mpt_table.address,
            mpt_table.storage_key.lo(),
            mpt_table.storage_key.hi(),
            mpt_table.proof_type,
            mpt_table.new_root.lo(),
            mpt_table.new_root.hi(),
            mpt_table.old_root.lo(),
            mpt_table.old_root.hi(),
            mpt_table.new_value.lo(),
            mpt_table.new_value.hi(),
            mpt_table.old_value.lo(),
            mpt_table.old_value.hi(),
        ]
        .iter()
        {
            meta.enable_equality(*col);
        }


        
        



         // meta.lookup_any(
        //     "mpt_table_lookup(value, old_root, new_root)",
        //     |meta| {
        // });



        Self {
            id,
            validator_id,
            address,
            amount,
            hash,
            root,
            rlp_item,
            mpt_table,
            // _marker: PhantomData,
        }
    }
}

impl<F: Field> WdCircuitConfig<F> {
    /// Assigns a wd circuit row
    fn assign_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        withdrawal: Withdrawal,
        hash: Word<Value<F>>,
        root: Word<Value<F>>,
    ) -> Result<(), Error> {
        region.assign_advice(
            || "wd_id",
            self.id,
            offset,
            || Value::known(F::from(withdrawal.id)),
        )?;
        region.assign_advice(
            || "validator_id",
            self.validator_id,
            offset,
            || Value::known(F::from(withdrawal.validator_id)),
        )?;
        withdrawal
            .address
            .assign_advice(region, || "address", self.address, offset);
        region.assign_advice(
            || "amount",
            self.amount,
            offset,
            || Value::known(F::from(withdrawal.amount)),
        )?;
        hash.assign_advice(region, "rlp hash", self.hash, offset);
        root.assign_advice(region, "mpt root", self.root, offset);
        // FIXME: do we need to do copy constrain and how?
        Ok(())
    }

    /// Get number of rows required.
    pub fn get_num_rows_required(num_wd: usize) -> usize {
        2
    }
}

/// Wd Circuit for verifying transaction signatures
#[derive(Clone, Default, Debug)]
pub struct WdCircuit<F: Field> {
    /// Max number of supported withdrawals
    pub max_wds: usize,
    /// List of Withdrawal
    pub wds: Vec<Withdrawal>,
    /// List of intermediate mpt roots
    pub roots: Vec<Vec<u8>>,
}

impl<F: Field> WdCircuit<F> {
    /// Return a new WdCircuit
    pub fn new(max_wds: usize, wds: Vec<Withdrawal>, roots: Vec<Vec<u8>>) -> Self {
        WdCircuit::<F> {
            max_wds,
            wds,
            roots,
        }
    }

    /// Return the minimum number of rows required to prove an input of a
    /// particular size.
    pub fn min_num_rows() -> usize {
        1
    }

    fn assign_wd_rows(
        &self,
        config: &WdCircuitConfig<F>,
        layouter: &mut impl Layouter<F>,
        hashes: Vec<Word<Value<F>>>,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "wd circuit",
            |mut region| {
                // Assign all Wd fields, hashes and intermediate mpt roots
                let wd_default = Withdrawal::default();
                for (i, wd) in self
                    .wds
                    .iter()
                    .chain((0..(self.max_wds - self.wds.len())).map(|_| &wd_default))
                    .enumerate()
                {
                    // assign a row of withdrawal circuit
                    config.assign_row(&mut region, i, wd, hashes[i], self.roots[i])?;


                    // RLP assignment
                    let mut keccak_r = F::ZERO;
                    challenges.keccak_input().map(|v| keccak_r = v);
                    let mut cached_region = CachedRegion::new(
                        &mut region,
                        keccak_r,
                    );
                    cached_region.annotate_columns(&self.cell_columns);

                    let mut rlp_values = Vec::new();
                    // Decompose RLP
                    for (idx, bytes) in wd.iter().enumerate() {
                        cached_region.push_region(offset + idx, MPTRegion::RLP as usize);
                        let rlp_value = self.rlp_item.assign(
                            &mut cached_region,
                            offset + idx,
                            bytes,
                            *item_type,
                        )?;
                        rlp_values.push(rlp_value);
                        cached_region.pop_region();
                    }

                    let prev_root = if i ==0 {[0;32]} else{self.roots[i-1]};
                    config.mpt_table.assign_cached(
                        region,
                        i,
                        &MptUpdateRow {
                            address: Value::known(from_bytes::value(
                                &wd.address.iter().cloned().rev().collect::<Vec<_>>(),
                            )),
                            storage_key: Word::<F>::new([0.scalar(), 0.scalar()]).into_value(),
                            proof_type: Value::known(MPTProofType::StorageChanged.scalar()),
                            new_root: self.roots[i].into_value(),
                            old_root: prev_root.into_value(),
                            new_value: hashes[i].into_value(),
                            old_value: 0.into_value(),
                        },
                    )?;
                }

                Ok(())
            },
        )
    }
}

impl<F: Field> SubCircuit<F> for WdCircuit<F> {
    type Config = WdCircuitConfig<F>;

    fn unusable_rows() -> usize {
        // FIXME: what is unusable rows??
        // No column queried at more than 3 distinct rotations, so returns 6 as
        // minimum unusable rows.
        6
    }

    fn new_from_block(block: &witness::Block<F>) -> Self {
        Self::new(block.circuits_params.max_withdrawals, block.withdrawals())
    }

    /// Return the minimum number of rows required to prove the block
    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        (
            // FIXME: figure out what this is
            Self::min_num_rows(),
            Self::min_num_rows(),
        )
    }

    /// Make the assignments to the WdCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        assert!(self.wds.len() <= self.max_wds);

        let hashes = self
            .wds
            .iter()
            .map(|wd| {
                let mut stream = ethers_core::utils::rlp::RlpStream::new();
                stream.begin_list(4);
                stream.append(&wd.id);
                stream.append(&wd.validator_id);
                stream.append(&wd.address);
                stream.append(&wd.amount);
                let rlp_encoding = stream.out().to_vec();
                U256::from_big_endian(&keccak256(&rlp_encoding)).into()
            })
            .collect::<Vec<Word<Value<F>>>>();

        self.assign_wd_rows(config, layouter, hashes)?;
        Ok(())
    }

    fn instance(&self) -> Vec<Vec<F>> {
        // The maingate expects an instance column, but we don't use it, so we return an
        // "empty" instance column
        vec![vec![]]
    }
}
