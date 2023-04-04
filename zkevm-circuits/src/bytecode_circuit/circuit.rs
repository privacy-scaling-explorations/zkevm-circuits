use super::{
    bytecode_unroller::{unroll, UnrolledBytecode},
    wit_gen::BytecodeWitnessGen,
};
use crate::{
    table::{BytecodeTable, KeccakTable},
    util::{get_push_size, Challenges, SubCircuit, SubCircuitConfig},
    witness,
};
use bus_mapping::state_db::EMPTY_CODE_HASH_LE;
use chiquito::{
    ast::{query::Queriable, Expr, ToExpr, ToField},
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Circuit,
        Compiler, FixedGenContext, WitnessGenContext,
    },
    dsl::{circuit, StepTypeContext},
};
use eth_types::Field;
use halo2_proofs::{
    circuit::{Layouter, Value},
    halo2curves::FieldExt,
    plonk::{Column, ConstraintSystem, Error, Expression, Fixed},
};
use std::cell::RefCell;

struct IsZero<F> {
    value_inv: Queriable<F>,
    is_zero_expression: Expr<F>,
}

impl<F: FieldExt> IsZero<F> {
    pub fn setup<V: Into<Expr<F>>, StepArgs>(
        ctx: &mut StepTypeContext<F, StepArgs>,
        value: V,
        value_inv: Queriable<F>,
    ) -> IsZero<F> {
        let value: Expr<F> = value.into();
        let is_zero_expression = 1.expr() - (value.clone() * value_inv);

        ctx.constr("isZero", value * is_zero_expression.clone());

        IsZero {
            value_inv,
            is_zero_expression,
        }
    }

    pub fn is_zero(&self) -> Expr<F> {
        self.is_zero_expression.clone()
    }
}

impl<F: Field> IsZero<F> {
    pub fn wg(&self, ctx: &mut dyn WitnessGenContext<F>, value: F) {
        ctx.assign(self.value_inv, value.invert().unwrap_or(F::zero()));
    }
}

type WitnessInput<F> = (Vec<UnrolledBytecode<F>>, Challenges<Value<F>>, usize);

/// BytecodeCircuitConfig
#[derive(Clone, Debug)]
pub struct BytecodeCircuitConfig<F: Field> {
    compiled: ChiquitoHalo2<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>>,
    push_data_table: ChiquitoHalo2<F, (), ()>,
    pub(crate) keccak_table: KeccakTable,

    minimum_rows: usize,
}

/// Circuit configuration arguments
pub struct BytecodeCircuitConfigArgs<F: Field> {
    /// BytecodeTable
    pub bytecode_table: BytecodeTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// Challenges
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for BytecodeCircuitConfig<F> {
    type ConfigArgs = BytecodeCircuitConfigArgs<F>;

    /// Return a new BytecodeCircuitConfig
    fn new(meta: &mut ConstraintSystem<F>, config: Self::ConfigArgs) -> Self {
        let push_data_value = meta.fixed_column();
        let push_data_size = meta.fixed_column();

        let mut push_data_table = chiquito2Halo2(Self::circuit_push_data_table(
            push_data_value,
            push_data_size,
        ));

        push_data_table.configure(meta);

        let mut circuit = chiquito2Halo2(Self::circuit(
            meta,
            &config,
            push_data_value,
            push_data_size,
        ));

        circuit.configure(meta);

        Self {
            compiled: circuit,
            push_data_table,
            keccak_table: config.keccak_table,
            minimum_rows: meta.minimum_rows(),
        }
    }
}

impl<F: Field> BytecodeCircuitConfig<F> {
    fn circuit(
        meta: &mut ConstraintSystem<F>,
        BytecodeCircuitConfigArgs {
            bytecode_table,
            keccak_table,
            challenges,
        }: &BytecodeCircuitConfigArgs<F>,
        push_data_table_value: Column<Fixed>,
        push_data_table_size: Column<Fixed>,
    ) -> Circuit<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>> {
        let mut bytecode_circuit = circuit::<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>, _>(
            "bytecode circuit",
            |ctx| {
                use chiquito::dsl::cb::*;

                let length = ctx.forward("length");
                let push_data_left = ctx.forward("push_data_left");
                let value_rlc = ctx.forward_with_phase("value_rlc", 1); // 1 -> SecondPhase

                let index = ctx.import_halo2_advice("index", bytecode_table.index);
                let hash = ctx.import_halo2_advice("hash", bytecode_table.code_hash);
                let is_code = ctx.import_halo2_advice("is_code", bytecode_table.is_code);
                let value = ctx.import_halo2_advice("value", bytecode_table.value);
                let tag = ctx.import_halo2_advice("tag", bytecode_table.tag);

                let push_data_table_value =
                    ctx.import_halo2_fixed("push_data_value", push_data_table_value);
                let push_data_table_size =
                    ctx.import_halo2_fixed("push_data_size", push_data_table_size);

                let keccak_is_enabled =
                    ctx.import_halo2_advice("keccak_is_enabled", keccak_table.is_enabled);
                let keccak_value_rlc =
                    ctx.import_halo2_advice("keccak_value_rlc", keccak_table.input_rlc);
                let keccak_length =
                    ctx.import_halo2_advice("keccak_length", keccak_table.input_len);
                let keccak_hash = ctx.import_halo2_advice("keccak_hash", keccak_table.output_rlc);

                let header = ctx.step_type("header");
                let byte_step = ctx.step_type("byte");

                ctx.pragma_first_step(header);
                ctx.pragma_last_step(header);

                ctx.step_type_def(header, move |ctx| {
                    ctx.constr("index == 0", eq(index, 0));
                    ctx.constr("value == length", eq(value, length));

                    ctx.transition_to("cur.length == 0", header, eq(length, 0));

                    let empty_hash = rlc(
                        &EMPTY_CODE_HASH_LE.map(|v| (v as u64).expr()),
                        challenges.evm_word(),
                    );

                    ctx.transition_to("cur.hash == EMPTY_HASH", header, eq(hash, empty_hash));

                    ctx.transition_to(
                        "next.length == cur.length",
                        byte_step,
                        eq(length, length.next()),
                    );
                    ctx.transition_to("next.index == 0", byte_step, eq(index.next(), 0));
                    ctx.transition_to("next.is_code == 1", byte_step, eq(is_code.next(), 1));
                    ctx.transition_to("next.hash == cur.hash", byte_step, eq(hash, hash.next()));
                    ctx.transition_to(
                        "next.value_rlc == next.value",
                        byte_step,
                        eq(value_rlc.next(), value.next()),
                    );

                    ctx.wg(move |ctx, wit| {
                        let wit = wit.borrow();

                        ctx.assign(tag, 0.field());
                        ctx.assign(index, 0.field());
                        ctx.assign(length, wit.length.field());
                        ctx.assign(value, wit.length.field());
                        ctx.assign(is_code, 0.field());
                        ctx.assign(value_rlc, 0.field());

                        wit.code_hash.map(|v| ctx.assign(hash, v));
                    })
                });

                ctx.step_type_def(byte_step, move |ctx| {
                    let push_data_size = ctx.signal("push_data_size");
                    let push_data_left_inv = ctx.signal("push_data_left_inv");

                    let push_data_left_is_zero =
                        IsZero::setup(ctx, push_data_left, push_data_left_inv);

                    ctx.constr(
                        "is_code == push_data_left_is_zero.is_zero",
                        eq(is_code, push_data_left_is_zero.is_zero()),
                    );

                    ctx.lookup(
                        "lookup((value, push_data_size_table.value)(push_data_size, push_data_size_table.push_data_size))",
                        vec![(value.expr(), push_data_table_value.expr()), (push_data_size.expr(), push_data_table_size.expr())]);

                    ctx.transition_to(
                        "next.length == cur.length",
                        byte_step,
                        eq(length, length.next()),
                    );
                    ctx.transition_to(
                        "next.index == cur.index + 1",
                        byte_step,
                        eq(index + 1, index.next()),
                    );
                    ctx.transition_to("next.hash == cur.hash", byte_step, eq(hash, hash.next()));
                    ctx.transition_to(
                        "next.value_rlc == cur.value_rlc * randomness + next.value",
                        byte_step,
                        eq(value_rlc.next(), (value_rlc * challenges.keccak_input()) + value.next()),
                    );

                    ctx.transition_to(
                        "next.push_data_left == cur.is_code ? cur.push_data_size : cur.push_data_left - 1",
                        byte_step,
                        eq(
                            push_data_left.next(),
                            select(is_code, push_data_size, push_data_left - 1),
                        ),
                    );

                    ctx.transition_to("cur.index + 1 == cur.length", header, eq(index + 1, length));

                    ctx.lookup(
                        "if header.next() then keccak256_table_lookup(cur.value_rlc, cur.length, cur.hash)",
                        vec![
                            (header.next().expr(), keccak_is_enabled.expr()),
                            (header.next() * value_rlc, keccak_value_rlc.expr()),
                            (header.next() * length, keccak_length.expr()),
                            (header.next() * hash, keccak_hash.expr()),
                        ],
                    );

                    ctx.wg(move |ctx, wit| {
                        let wit = wit.borrow();

                        ctx.assign(tag, 1.field());
                        ctx.assign(index, wit.index());
                        ctx.assign(length, wit.length.field());
                        ctx.assign(value, wit.value());
                        ctx.assign(is_code, wit.is_code());

                        wit.value_rlc.map(|v| ctx.assign(value_rlc, v));
                        wit.code_hash.map(|v| ctx.assign(hash, v));

                        ctx.assign(push_data_size, wit.push_data_size.field());
                        ctx.assign(push_data_left, wit.push_data_left.field());
                        push_data_left_is_zero.wg(ctx, wit.push_data_left.field());
                    });
                });

                ctx.trace(move |ctx, (bytecodes, challenges, last_row_offset)| {
                    ctx.set_height(last_row_offset + 1);

                    let mut offset = 0;
                    for bytecode in bytecodes.iter() {
                        let wit = RefCell::new(BytecodeWitnessGen::new(bytecode, &challenges));

                        println!("start wit gen");

                        if offset < last_row_offset - 1 {
                            ctx.add(&header, wit.clone());
                            offset += 1;
                        }

                        while wit.borrow_mut().has_more() && offset < last_row_offset - 1 {
                            wit.borrow_mut().next_row();
                            ctx.add(&byte_step, wit.clone());
                            offset += 1;
                        }
                    }

                    // padding
                    let wit = RefCell::new(BytecodeWitnessGen::new(&unroll(vec![]), &challenges));

                    while offset <= last_row_offset {
                        ctx.add(&header, wit.clone());
                        offset += 1;
                    }
                })
            },
        );

        let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

        compiler.compile(&mut bytecode_circuit)
    }

    fn circuit_push_data_table(
        push_data_value: Column<Fixed>,
        push_data_size: Column<Fixed>,
    ) -> Circuit<F, (), ()> {
        let mut push_data_table_circuit = circuit::<F, (), (), _>("push_table", |ctx| {
            let push_data_value = ctx.import_halo2_fixed("push_data_value", push_data_value);
            let push_data_size = ctx.import_halo2_fixed("push_data_size", push_data_size);

            ctx.fixed_gen(move |ctx: &mut dyn FixedGenContext<F>| {
                for byte in 0usize..256 {
                    let push_size = get_push_size(byte as u8);
                    ctx.assign(byte, push_data_value, byte.field());
                    ctx.assign(byte, push_data_size, push_size.field());
                }
            });
        });

        let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

        compiler.compile(&mut push_data_table_circuit)
    }
}

#[derive(Default, Debug, Clone)]
/// BytecodeCircuit
pub struct BytecodeCircuit<F: Field> {
    /// Unrolled bytecodes
    pub bytecodes: Vec<UnrolledBytecode<F>>,
    /// Circuit size
    pub size: usize,
    /// Overwrite
    pub overwrite: UnrolledBytecode<F>,
}

impl<F: Field> BytecodeCircuit<F> {
    /// new BytecodeCircuitTester
    pub fn new(bytecodes: Vec<UnrolledBytecode<F>>, size: usize) -> Self {
        BytecodeCircuit {
            bytecodes,
            size,
            overwrite: Default::default(),
        }
    }

    /// Creates bytecode circuit from block and bytecode_size.
    pub fn new_from_block_sized(block: &witness::Block<F>, bytecode_size: usize) -> Self {
        let bytecodes: Vec<UnrolledBytecode<F>> = block
            .bytecodes
            .iter()
            .map(|(_, b)| unroll(b.bytes.clone()))
            .collect();
        Self::new(bytecodes, bytecode_size)
    }
}

impl<F: Field> SubCircuit<F> for BytecodeCircuit<F> {
    type Config = BytecodeCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        // TODO: Find a nicer way to add the extra `128`.  Is this to account for
        // unusable rows? Then it could be calculated like this:
        // fn unusable_rows<F: Field, C: Circuit<F>>() -> usize {
        //     let mut cs = ConstraintSystem::default();
        //     C::configure(&mut cs);
        //     cs.blinding_factors()
        // }
        let bytecode_size = block.circuits_params.max_bytecode + 128;
        Self::new_from_block_sized(block, bytecode_size)
    }

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.push_data_table.synthesize(layouter, ());
        config.compiled.synthesize(
            layouter,
            (
                self.bytecodes.clone(),
                *challenges,
                self.size - (config.minimum_rows + 1),
            ),
        );

        Ok(())
    }

    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        (
            block
                .bytecodes
                .values()
                .map(|bytecode| bytecode.bytes.len() + 1)
                .sum(),
            block.circuits_params.max_bytecode,
        )
    }
}
