use eth_types::Field;
use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use std::iter;

pub const BYTES_LEN_17_WORDS: usize = 136;

// TODO: byteRLC
// TODO: connect_word_builder
#[derive(Debug, Clone)]
pub struct PaddingConfig<F> {
    q_all: Selector,
    q_without_first: Selector,
    q_without_last: Selector,
    q_last: Selector,
    flag_enable: Column<Advice>,
    byte: Column<Advice>,
    input_len: Column<Advice>,
    acc_len: Column<Advice>,
    diff_is_zero: IsZeroConfig<F>,
    is_pad_zone: Column<Advice>,
    padded_byte: Column<Advice>,
}

impl<F: Field> PaddingConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_all = meta.selector();
        let q_without_first = meta.selector();
        let q_without_last = meta.selector();
        let q_last = meta.selector();
        let flag_enable = meta.advice_column();
        let byte = meta.advice_column();
        let input_len = meta.advice_column();
        let acc_len = meta.advice_column();
        let diff_inv = meta.advice_column();
        let is_pad_zone = meta.advice_column();
        let padded_byte = meta.advice_column();
        meta.enable_equality(flag_enable);
        meta.enable_equality(input_len);
        meta.enable_equality(acc_len);
        let one = Expression::Constant(F::one());
        let diff_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_all),
            |meta| {
                meta.query_advice(input_len, Rotation::cur())
                    - meta.query_advice(acc_len, Rotation::cur())
            },
            diff_inv,
        );
        meta.create_gate("all", |meta| {
            let q_all = meta.query_selector(q_all);
            let flag_enable = meta.query_advice(flag_enable, Rotation::cur());
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::cur());

            vec![q_all * flag_enable * (is_pad_zone_cur * byte_cur)]
        });

        meta.create_gate("without last", |meta| {
            let q_without_last = meta.query_selector(q_without_last);
            let flag_enable_cur = meta.query_advice(flag_enable, Rotation::cur());
            let acc_len_cur = meta.query_advice(acc_len, Rotation::cur());
            let acc_len_next = meta.query_advice(acc_len, Rotation::next());
            let padded_byte_cur = meta.query_advice(padded_byte, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::cur());
            iter::empty()
                .chain(Some(("increase acc_len", acc_len_next - acc_len_cur - one)))
                .chain(Some((
                    "check padded byte",
                    padded_byte_cur
                        - byte_cur
                        - diff_is_zero.clone().is_zero_expression
                            * Expression::Constant(F::from(0x80)),
                )))
                .map(move |(name, poly)| {
                    (
                        name,
                        q_without_last.clone() * flag_enable_cur.clone() * poly,
                    )
                })
        });
        meta.create_gate("without first", |meta| {
            let q_without_first = meta.query_selector(q_without_first);
            let flag_enable_cur = meta.query_advice(flag_enable, Rotation::cur());
            let is_pad_zone_prev = meta.query_advice(is_pad_zone, Rotation::prev());
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            vec![(
                "check pad_zone",
                q_without_first
                    * flag_enable_cur
                    * (is_pad_zone_cur
                        - is_pad_zone_prev
                        - diff_is_zero.clone().is_zero_expression),
            )]
        });

        meta.create_gate("last", |meta| {
            let q_last = meta.query_selector(q_last);
            let padded_byte_cur = meta.query_advice(padded_byte, Rotation::cur());
            let flag_enable_cur = meta.query_advice(flag_enable, Rotation::cur());
            let one = Expression::Constant(F::one());
            vec![
                q_last
                    * flag_enable_cur
                    * (padded_byte_cur
                        - diff_is_zero.clone().is_zero_expression
                            * Expression::Constant(F::from(0x80))
                        - one),
            ]
        });
        Self {
            q_all,
            q_without_first,
            q_without_last,
            q_last,
            flag_enable,
            byte,
            input_len,
            acc_len,
            diff_is_zero,
            is_pad_zone,
            padded_byte,
        }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        flag_enable: AssignedCell<F, F>,
        input_len_cell: AssignedCell<F, F>,
        acc_len_cell: AssignedCell<F, F>,
        bytes: [u8; BYTES_LEN_17_WORDS],
    ) -> Result<(), Error> {
        let diff_is_zero_chip = IsZeroChip::construct(self.diff_is_zero.clone());
        layouter.assign_region(
            || "padding validation",
            |mut region| {
                let last = BYTES_LEN_17_WORDS - 1;
                self.q_last.enable(&mut region, last)?;
                let mut acc_len = acc_len_cell.value().cloned().unwrap_or_default();
                let mut is_pad_zone = F::zero();
                let mut padded_byte = [0u8; BYTES_LEN_17_WORDS];
                for (offset, &byte) in bytes.iter().enumerate().take(BYTES_LEN_17_WORDS) {
                    self.q_all.enable(&mut region, offset)?;
                    if offset != 0 {
                        self.q_without_first.enable(&mut region, offset)?;
                    }
                    if offset != last {
                        self.q_without_last.enable(&mut region, offset)?;
                    }
                    flag_enable.clone().copy_advice(
                        || "flag enable",
                        &mut region,
                        self.flag_enable,
                        offset,
                    )?;
                    input_len_cell.copy_advice(
                        || "input len",
                        &mut region,
                        self.input_len,
                        offset,
                    )?;

                    region.assign_advice(
                        || "acc_len_rest",
                        self.acc_len,
                        offset,
                        || Ok(acc_len),
                    )?;
                    let diff_value =
                        Some(input_len_cell.value().cloned().unwrap_or_default() - acc_len);
                    let is_zero = diff_value
                        .map(|diff_value| F::from(diff_value == F::zero()))
                        .unwrap_or_default();
                    diff_is_zero_chip.assign(&mut region, offset, diff_value)?;

                    let byte_f = F::from(byte as u64);
                    region.assign_advice(|| "byte", self.byte, offset, || Ok(byte_f))?;
                    is_pad_zone += is_zero;
                    region.assign_advice(
                        || "is pad zone",
                        self.is_pad_zone,
                        offset,
                        || Ok(is_pad_zone),
                    )?;
                    padded_byte[offset] = byte
                        + diff_value
                            .map(|diff_value| (diff_value == F::zero()) as u8)
                            .unwrap_or_default()
                            * 0x80u8
                        + ((offset == last) as u8);
                    region.assign_advice(
                        || "padded byte",
                        self.padded_byte,
                        offset,
                        || {
                            Ok(byte_f
                                // pad head
                                + is_zero * F::from(0x80)
                                // pad tail
                                + F::from(offset == last))
                        },
                    )?;
                    acc_len += F::one();
                }
                println!("bytes {:?}", bytes);
                println!("padded bytes {:?}", padded_byte);

                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        plonk::{Advice, Circuit},
    };
    use pairing::bn256::Fr;
    use pretty_assertions::assert_eq;
    use rand::{thread_rng, Fill};
    use std::marker::PhantomData;

    struct MyCircuit<F> {
        bytes: [u8; BYTES_LEN_17_WORDS],
        parent_flag: bool,
        input_len: u64,
        acc_len: u64,
        _marker: PhantomData<F>,
    }
    impl<F: Field> Default for MyCircuit<F> {
        fn default() -> Self {
            Self {
                bytes: [0; BYTES_LEN_17_WORDS],
                parent_flag: true,
                input_len: 0,
                acc_len: 0,
                _marker: PhantomData,
            }
        }
    }

    #[derive(Clone)]
    struct MyConfig<F> {
        padding_conf: PaddingConfig<F>,
        parent_flag: Column<Advice>,
        input_len: Column<Advice>,
        acc_len: Column<Advice>,
    }

    impl<F: Field> Circuit<F> for MyCircuit<F> {
        type Config = MyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }
        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let padding_conf = PaddingConfig::configure(meta);
            let parent_flag = meta.advice_column();
            let input_len = meta.advice_column();
            let acc_len = meta.advice_column();
            meta.enable_equality(parent_flag);
            meta.enable_equality(input_len);
            meta.enable_equality(acc_len);

            Self::Config {
                padding_conf,
                parent_flag,
                acc_len,
                input_len,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let (parent_flag, input_len, acc_len) = layouter.assign_region(
                || "external values",
                |mut region| {
                    let offset = 0;
                    let parent_flag = region.assign_advice(
                        || "parent flag",
                        config.parent_flag,
                        offset,
                        || Ok(F::from(self.parent_flag)),
                    )?;
                    let input_len = region.assign_advice(
                        || "input len",
                        config.input_len,
                        offset,
                        || Ok(F::from(self.input_len)),
                    )?;
                    let acc_len = region.assign_advice(
                        || "acc len",
                        config.acc_len,
                        offset,
                        || Ok(F::from(self.acc_len)),
                    )?;
                    Ok((parent_flag, input_len, acc_len))
                },
            )?;

            config.padding_conf.assign_region(
                &mut layouter,
                parent_flag,
                input_len,
                acc_len,
                self.bytes,
            )?;

            Ok(())
        }
    }
    #[test]
    fn test_normal_pad() {
        let mut bytes = [0; BYTES_LEN_17_WORDS];
        bytes[0] = 1;
        let circuit = MyCircuit::<Fr> {
            bytes,
            parent_flag: true,
            input_len: 1,
            acc_len: 0,
            _marker: PhantomData,
        };
        let prover = MockProver::<Fr>::run(9, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_full_pad() {
        let circuit = MyCircuit::<Fr> {
            bytes: [0; BYTES_LEN_17_WORDS],
            parent_flag: true,
            input_len: 0,
            acc_len: 0,
            _marker: PhantomData,
        };
        let prover = MockProver::<Fr>::run(9, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_0x81_case() {
        let mut bytes = [0u8; BYTES_LEN_17_WORDS];
        let mut rng = thread_rng();
        bytes.try_fill(&mut rng).unwrap();
        bytes[135] = 0;
        let circuit = MyCircuit::<Fr> {
            bytes,
            parent_flag: true,
            input_len: 135,
            acc_len: 0,
            _marker: PhantomData,
        };
        let prover = MockProver::<Fr>::run(9, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
