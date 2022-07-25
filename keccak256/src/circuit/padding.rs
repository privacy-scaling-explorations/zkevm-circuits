use eth_types::Field;
use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use itertools::Itertools;
use std::convert::TryInto;
use std::iter;
use std::marker::PhantomData;

pub const BYTES_LEN_17_WORDS: usize = 136;

/// Build word from big endian bytes
#[derive(Debug, Clone)]
pub struct WordConfig<F> {
    q_enable: Selector,
    word: Column<Advice>,
    _marker: PhantomData<F>,
}
impl<F: Field> WordConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        byte: Column<Advice>,
        word: Column<Advice>,
    ) -> Self {
        meta.enable_equality(byte);
        meta.enable_equality(word);
        let q_enable = meta.selector();
        meta.create_gate("build word", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let byte = meta.query_advice(byte, Rotation::cur());
            let word_cur = meta.query_advice(word, Rotation::cur());
            let word_prev = meta.query_advice(word, Rotation::prev());
            vec![q_enable * (word_cur - Expression::Constant(F::from(256u64)) * word_prev - byte)]
        });
        Self {
            q_enable,
            word,
            _marker: PhantomData,
        }
    }

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        bytes: [AssignedCell<F, F>; 8],
    ) -> Result<AssignedCell<F, F>, Error> {
        let mut word_cell = bytes[0].copy_advice(|| "first byte", region, self.word, offset)?;
        let mut word = bytes[0].value().cloned().unwrap_or_default();
        for (i, byte) in bytes.iter().enumerate().skip(1) {
            let real_offset = offset + i;
            self.q_enable.enable(region, real_offset)?;
            word = word * F::from(256u64) + byte.value().cloned().unwrap_or_default();
            word_cell = region.assign_advice(|| "word", self.word, real_offset, || Ok(word))?;
        }
        Ok(word_cell)
    }
}

// TODO: byteRLC
#[derive(Debug, Clone)]
pub struct PaddingConfig<F> {
    q_all: Selector,
    q_without_first: Selector,
    q_without_last: Selector,
    q_last: Selector,
    is_finalize: Column<Advice>,
    byte: Column<Advice>,
    input_len: Column<Advice>,
    acc_len: Column<Advice>,
    diff_is_zero: IsZeroConfig<F>,
    is_pad_zone: Column<Advice>,
    padded_byte: Column<Advice>,
    word_config: WordConfig<F>,
}

impl<F: Field> PaddingConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_all = meta.selector();
        let q_without_first = meta.selector();
        let q_without_last = meta.selector();
        let q_last = meta.selector();
        let is_finalize = meta.advice_column();
        let byte = meta.advice_column();
        let input_len = meta.advice_column();
        let acc_len = meta.advice_column();
        let diff_inv = meta.advice_column();
        let is_pad_zone = meta.advice_column();
        let padded_byte = meta.advice_column();
        let word = meta.advice_column();
        meta.enable_equality(is_finalize);
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
        let word_config = WordConfig::configure(meta, padded_byte, word);
        // Check bytes in the pad zone must be 0
        meta.create_gate("all", |meta| {
            let q_all = meta.query_selector(q_all);
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::cur());

            vec![q_all * (is_pad_zone_cur * byte_cur)]
        });
        // check that
        // 1. acc_len is increasing by one in each row
        // 2. padded_byte is correctly padded 0x80 from byte
        meta.create_gate("without last", |meta| {
            let q_without_last = meta.query_selector(q_without_last);
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
                .map(move |(name, poly)| (name, q_without_last.clone() * poly))
        });
        // Check that cells in the pad_zone column are 0 before the pad, and are 1 after
        // the pad.
        meta.create_gate("without first", |meta| {
            let q_without_first = meta.query_selector(q_without_first);
            let is_pad_zone_prev = meta.query_advice(is_pad_zone, Rotation::prev());
            let is_pad_zone_cur = meta.query_advice(is_pad_zone, Rotation::cur());
            vec![(
                "check pad_zone",
                q_without_first
                    * (is_pad_zone_cur
                        - is_pad_zone_prev
                        - diff_is_zero.clone().is_zero_expression),
            )]
        });
        // padded_byte is padded 0x80 if pad happens here. padded_byte is also padded
        // 0x01 if the state_tag is Finalize
        meta.create_gate("last", |meta| {
            let q_last = meta.query_selector(q_last);
            let is_finalize = meta.query_advice(is_finalize, Rotation::cur());
            let padded_byte_cur = meta.query_advice(padded_byte, Rotation::cur());
            let byte_cur = meta.query_advice(byte, Rotation::cur());
            vec![
                q_last
                    * (padded_byte_cur
                        - byte_cur
                        - diff_is_zero.clone().is_zero_expression
                            * Expression::Constant(F::from(0x80))
                        - is_finalize),
            ]
        });
        Self {
            q_all,
            q_without_first,
            q_without_last,
            q_last,
            is_finalize,
            byte,
            input_len,
            acc_len,
            diff_is_zero,
            is_pad_zone,
            padded_byte,
            word_config,
        }
    }
    pub fn assign_region(
        &self,
        layouter: &mut impl Layouter<F>,
        is_finalize: AssignedCell<F, F>,
        input_len_cell: AssignedCell<F, F>,
        acc_len_cell: AssignedCell<F, F>,
        bytes: [u8; BYTES_LEN_17_WORDS],
    ) -> Result<[AssignedCell<F, F>; 17], Error> {
        let diff_is_zero_chip = IsZeroChip::construct(self.diff_is_zero.clone());
        layouter.assign_region(
            || "padding validation",
            |mut region| {
                const LAST: usize = BYTES_LEN_17_WORDS - 1;
                self.q_last.enable(&mut region, LAST)?;
                let mut is_pad_zone = F::zero();
                let mut padded_bytes = [0u8; BYTES_LEN_17_WORDS];
                for (offset, &byte) in bytes.iter().enumerate().take(BYTES_LEN_17_WORDS) {
                    self.q_all.enable(&mut region, offset)?;
                    if offset != 0 {
                        self.q_without_first.enable(&mut region, offset)?;
                    }
                    if offset != LAST {
                        self.q_without_last.enable(&mut region, offset)?;
                    }
                    is_finalize.clone().copy_advice(
                        || "flag enable",
                        &mut region,
                        self.is_finalize,
                        offset,
                    )?;
                    input_len_cell.copy_advice(
                        || "input len",
                        &mut region,
                        self.input_len,
                        offset,
                    )?;
                    let acc_len =
                        acc_len_cell.value().cloned().unwrap_or_default() + F::from(offset as u64);
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
                    let is_finalize_bit =
                        is_finalize.value().cloned().unwrap_or_default() == F::one();
                    padded_bytes[offset] = byte
                        + diff_value
                            .map(|diff_value| (diff_value == F::zero()) as u8)
                            .unwrap_or_default()
                            * 0x80u8
                        + (((offset == LAST) && is_finalize_bit) as u8);
                }
                let padded_byte_cells: Result<Vec<_>, _> = padded_bytes
                    .iter()
                    .take(BYTES_LEN_17_WORDS)
                    .enumerate()
                    .map(|(offset, &padded_byte)| {
                        region.assign_advice(
                            || "padded byte",
                            self.padded_byte,
                            offset,
                            || Ok(F::from(padded_byte as u64)),
                        )
                    })
                    .collect();
                let padded_byte_cells = padded_byte_cells?;
                let words: Result<Vec<_>, _> = padded_byte_cells
                    .iter()
                    .chunks(8)
                    .into_iter()
                    .enumerate()
                    .map(|(idx, chunk)| {
                        let bytes: [AssignedCell<F, F>; 8] =
                            chunk.cloned().collect_vec().try_into().unwrap();
                        self.word_config.assign_region(&mut region, idx * 8, bytes)
                    })
                    .collect();
                let words: [AssignedCell<F, F>; 17] = words?.try_into().unwrap();

                Ok(words)
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
        pairing::bn256::Fr,
        plonk::{Advice, Circuit},
    };
    use pretty_assertions::assert_eq;
    use rand::{thread_rng, Fill};
    use std::marker::PhantomData;

    struct MyCircuit<F> {
        bytes: [u8; BYTES_LEN_17_WORDS],
        is_finalize: bool,
        input_len: u64,
        acc_len: u64,
        _marker: PhantomData<F>,
    }
    impl<F: Field> Default for MyCircuit<F> {
        fn default() -> Self {
            Self {
                bytes: [0; BYTES_LEN_17_WORDS],
                is_finalize: true,
                input_len: 0,
                acc_len: 0,
                _marker: PhantomData,
            }
        }
    }

    #[derive(Clone)]
    struct MyConfig<F> {
        padding_conf: PaddingConfig<F>,
        is_finalize: Column<Advice>,
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
            let is_finalize = meta.advice_column();
            let input_len = meta.advice_column();
            let acc_len = meta.advice_column();
            meta.enable_equality(is_finalize);
            meta.enable_equality(input_len);
            meta.enable_equality(acc_len);

            Self::Config {
                padding_conf,
                is_finalize,
                acc_len,
                input_len,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let (is_finalize, input_len, acc_len) = layouter.assign_region(
                || "external values",
                |mut region| {
                    let offset = 0;
                    let is_finalize = region.assign_advice(
                        || "parent flag",
                        config.is_finalize,
                        offset,
                        || Ok(F::from(self.is_finalize)),
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
                    Ok((is_finalize, input_len, acc_len))
                },
            )?;

            config.padding_conf.assign_region(
                &mut layouter,
                is_finalize,
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
            is_finalize: true,
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
            is_finalize: true,
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
            is_finalize: true,
            input_len: 135,
            acc_len: 0,
            _marker: PhantomData,
        };
        let prover = MockProver::<Fr>::run(9, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_no_pad() {
        let mut bytes = [0u8; BYTES_LEN_17_WORDS];
        let mut rng = thread_rng();
        bytes.try_fill(&mut rng).unwrap();
        let circuit = MyCircuit::<Fr> {
            bytes,
            is_finalize: false,
            input_len: 136,
            acc_len: 0,
            _marker: PhantomData,
        };
        let prover = MockProver::<Fr>::run(9, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
