use eth_types::Field;
use halo2_proofs::{
    plonk::{Advice, Column, ConstraintSystem, Expression, Fixed, SecondPhase},
    poly::Rotation,
};
use zkevm_circuits::{
    table::U8Table,
    util::{Challenges, Expr},
};

#[derive(Clone, Debug)]
pub struct BlobDataConfig {
    /// Fixed column to indicate that the constraints on this row are enabled.
    pub q_enable: Column<Fixed>,
    /// Incremental index assigned to the row.
    pub idx: Column<Advice>,
    /// Fixed column to indicate the first byte of every 32-bytes chunk, always set to 0 so that
    /// the other 31 bytes represent a canonical BLS12-381 scalar field element.
    pub q_zero: Column<Fixed>,
    /// Fixed column to indicate the first 32 bytes, representing blob metadata.
    pub q_metadata: Column<Fixed>,
    /// Byte value at this row.
    pub byte_value: Column<Advice>,
    /// A running accumulator for the random-linear combination of byte values over the entire
    /// blob.
    pub blob_bytes_rlc: Column<Advice>,
    /// A boolean advice column that is set to 1 every time we encounter the end of a chunk.
    pub is_boundary: Column<Advice>,
    /// An incremental accumulator that holds the number of bytes seen so far, that resets every
    /// time we encounter the end of a chunk.
    pub chunk_len: Column<Advice>,
    /// A running accumulator for the random-linear combination of byte values seen so far, that
    /// resets every time we encounter the end of a chunk.
    pub chunk_bytes_rlc: Column<Advice>,
    /// Indicates the # of chunk that we are currently seeing.
    pub chunk_idx: Column<Advice>,
    /// Column used to store the decoded size (in # of bytes) of a chunk. This has meaningful data
    /// only in the metadata section.
    pub size_chunk: Column<Advice>,
    /// The hash of all the chunk bytes concatenated.
    pub chunk_hash_rlc: Column<Advice>,
    /// The hash of all the blob bytes concatenated.
    pub blob_hash_rlc: Column<Advice>,
    /// Boolean column to mark right-padded zeroes to blob data.
    pub is_padding: Column<Advice>,
}

impl BlobDataConfig {
    /// Configure the constraints for a blob's metadata, chunk sizes and the RLC accumulation.
    pub fn configure<F: Field>(
        meta: &mut ConstraintSystem<F>,
        challenge: Challenges,
        u8_table: U8Table,
    ) -> Self {
        let challenge_expr = challenge.exprs(meta);
        let config = Self {
            q_enable: meta.fixed_column(),
            idx: meta.advice_column(),
            q_zero: meta.fixed_column(),
            q_metadata: meta.fixed_column(),
            byte_value: meta.advice_column(),
            blob_bytes_rlc: meta.advice_column_in(SecondPhase),
            is_boundary: meta.advice_column(),
            chunk_len: meta.advice_column(),
            chunk_bytes_rlc: meta.advice_column_in(SecondPhase),
            chunk_idx: meta.advice_column(),
            size_chunk: meta.advice_column(),
            chunk_hash_rlc: meta.advice_column_in(SecondPhase),
            blob_hash_rlc: meta.advice_column_in(SecondPhase),
            is_padding: meta.advice_column(),
        };

        // chunk_idx (on the last blob byte) == byte_value (on the first blob byte).
        meta.enable_equality(config.byte_value);
        meta.enable_equality(config.chunk_idx);

        // bytes_len (on the last blob byte of each chunk) == size_chunk (in metadata).
        meta.enable_equality(config.size_chunk);
        meta.enable_equality(config.chunk_len);

        meta.lookup("BlobDataConfig: byte value range check", |meta| {
            let condition = meta.query_fixed(config.q_enable, Rotation::cur());
            vec![(
                condition * meta.query_advice(config.byte_value, Rotation::cur()),
                u8_table.into(),
            )]
        });

        meta.create_gate("BlobDataConfig: metadata and idx", |meta| {
            let is_first = meta.query_fixed(config.q_zero, Rotation::cur())
                * meta.query_fixed(config.q_metadata, Rotation::cur());
            let is_not_first = 1.expr() - is_first.expr();

            let mut is_first_cs = vec![];
            is_first_cs.push(
                // idx == 1
                meta.query_advice(config.idx, Rotation::cur()) - 1.expr(),
            );
            for i in 1..16 {
                is_first_cs.push(
                    // size_chunk(2*i) == byte_value(2*i) + byte_value(2*i + 1) * 256
                    meta.query_advice(config.size_chunk, Rotation(2 * i))
                        - meta.query_advice(config.byte_value, Rotation(2 * i))
                        - (256.expr() * meta.query_advice(config.byte_value, Rotation(2 * i + 1))),
                );
            }

            // idx::cur == idx::prev + 1
            let is_not_first_cs = meta.query_advice(config.idx, Rotation::cur())
                - meta.query_advice(config.idx, Rotation::prev())
                - 1.expr();

            is_first_cs
                .into_iter()
                .map(|cs| is_first.expr() * cs)
                .chain(std::iter::once(is_not_first * is_not_first_cs))
                .collect::<Vec<Expression<F>>>()
        });

        meta.create_gate("BlobDataConfig: main gate", |meta| {
            let is_metadata = meta.query_fixed(config.q_metadata, Rotation::cur());
            let is_not_metadata = 1.expr() - is_metadata.expr();
            let is_first = meta.query_fixed(config.q_zero, Rotation::cur())
                * meta.query_fixed(config.q_metadata, Rotation::prev());

            // if q_zero immediately follows a chunk boundary
            let cond1 = meta.query_fixed(config.q_zero, Rotation::cur())
                * meta.query_advice(config.is_boundary, Rotation::prev());

            // if q_zero follows a byte that is not marked by q_zero
            let cond2 = (1.expr() - meta.query_fixed(config.q_zero, Rotation::cur()))
                * meta.query_advice(config.is_boundary, Rotation::prev());

            // if q_zero does not follow a chunk boundary.
            let cond3 = meta.query_fixed(config.q_zero, Rotation::cur())
                * (1.expr() - meta.query_advice(config.is_boundary, Rotation::prev()));

            // if encounter meaningful byte, i.e. q_zero != 1
            let cond4 = 1.expr() - meta.query_fixed(config.q_zero, Rotation::cur());

            // if not chunk boundary
            let cond5 = 1.expr() - meta.query_advice(config.is_boundary, Rotation::cur());

            // if padding
            let is_padding = meta.query_advice(config.is_padding, Rotation::cur());

            // if boundary encountered but not yet in padding.
            let cond6 = meta.query_advice(config.is_boundary, Rotation::prev())
                * (1.expr() - is_padding.expr());

            let is_not_metadata_cs = vec![
                // first byte of the first chunk: chunk_len == 0
                is_first.expr() * meta.query_advice(config.chunk_len, Rotation::cur()),
                // first byte of the first chunk: chunk_bytes_rlc == 0
                is_first.expr() * meta.query_advice(config.chunk_bytes_rlc, Rotation::cur()),
                // first byte of the first chunk: is_padding == 0
                is_first.expr() * meta.query_advice(config.is_padding, Rotation::cur()),
                // first byte of the first chunk: chunk_idx == 1
                is_first.expr() * (1.expr() - meta.query_advice(config.chunk_idx, Rotation::cur())),
                // chunk cannot end of a q_zero
                meta.query_fixed(config.q_zero, Rotation::cur())
                    * meta.query_advice(config.is_boundary, Rotation::cur()),
                // byte_value == 0 at q_zero
                meta.query_fixed(config.q_zero, Rotation::cur())
                    * meta.query_advice(config.byte_value, Rotation::cur()),
                // if cond1: initialise chunk_len == 0
                cond1.expr() * meta.query_advice(config.chunk_len, Rotation::cur()),
                // if cond1: initialise chunk_bytes_rlc == 0
                cond1.expr() * meta.query_advice(config.chunk_bytes_rlc, Rotation::cur()),
                // if cond2: initialise chunk_len == 1
                cond2.expr() * (1.expr() - meta.query_advice(config.chunk_len, Rotation::cur())),
                // if cond2: initialise chunk_bytes_rlc == byte_value
                cond2.expr()
                    * (meta.query_advice(config.chunk_bytes_rlc, Rotation::cur())
                        - meta.query_advice(config.byte_value, Rotation::cur())),
                // if cond3: continue chunk_len
                cond3.expr()
                    * (meta.query_advice(config.chunk_len, Rotation::cur())
                        - meta.query_advice(config.chunk_len, Rotation::prev())),
                // if cond3: continue chunk_bytes_rlc
                cond3.expr()
                    * (meta.query_advice(config.chunk_bytes_rlc, Rotation::cur())
                        - meta.query_advice(config.chunk_bytes_rlc, Rotation::prev())),
                // if cond4: increment chunk_len
                cond4.expr()
                    * (meta.query_advice(config.chunk_len, Rotation::cur())
                        - meta.query_advice(config.chunk_len, Rotation::prev())
                        - 1.expr()),
                // if cond4: accumulate chunk_bytes_rlc
                cond4.expr()
                    * (meta.query_advice(config.chunk_bytes_rlc, Rotation::cur())
                        - challenge_expr.keccak_input()
                            * meta.query_advice(config.chunk_bytes_rlc, Rotation::prev())
                        - meta.query_advice(config.byte_value, Rotation::cur())),
                // if cond5: continue chunk_hash
                cond5.expr()
                    * (meta.query_advice(config.chunk_hash_rlc, Rotation::next())
                        - meta.query_advice(config.chunk_hash_rlc, Rotation::cur())),
                // if cond5: continue chunk_idx
                cond5.expr()
                    * (meta.query_advice(config.chunk_idx, Rotation::next())
                        - meta.query_advice(config.chunk_idx, Rotation::cur())),
                // if cond6: increment chunk idx
                cond6.expr()
                    * (meta.query_advice(config.chunk_idx, Rotation::cur())
                        - meta.query_advice(config.chunk_idx, Rotation::prev())
                        - 1.expr()),
                // padding only transitions from 0 -> 1
                {
                    let padding_diff = meta.query_advice(config.is_padding, Rotation::cur())
                        - meta.query_advice(config.is_padding, Rotation::prev());
                    padding_diff.expr() * (1.expr() - padding_diff.expr())
                },
                // if padding: byte value == 0
                is_padding.expr() * meta.query_advice(config.byte_value, Rotation::cur()),
                // if padding: continue chunk_idx
                is_padding.expr()
                    * (meta.query_advice(config.chunk_idx, Rotation::cur())
                        - meta.query_advice(config.chunk_idx, Rotation::prev())),
            ];

            let is_metadata_cs = vec![
                // metadata rows cannot be padding
                meta.query_advice(config.is_padding, Rotation::cur()),
                // metadata rows cannot be chunk boundaries
                meta.query_advice(config.is_boundary, Rotation::cur()),
            ];

            is_not_metadata_cs
                .into_iter()
                .map(|cs| is_not_metadata.expr() * cs)
                .chain(is_metadata_cs.into_iter().map(|cs| is_metadata.expr() * cs))
                .collect::<Vec<Expression<F>>>()
        });

        config
    }
}
