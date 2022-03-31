// TODO Remove this
#![allow(missing_docs)]

use std::{marker::PhantomData, os::unix::prelude::FileTypeExt};

use ecc::GeneralEccChip;
use ecdsa::ecdsa::{EcdsaChip, EcdsaConfig};
use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig};
use pairing::arithmetic::FieldExt;
use secp256k1::Secp256k1Affine;

use crate::gadget::is_zero::{IsZeroChip, IsZeroConfig};
use halo2_proofs::{
    arithmetic::CurveAffine,
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, VirtualCells},
    poly::Rotation,
};

// TODO: Move these utils outside of `evm_circuit` so that they can be used by
// other circuits without crossing boundaries.
use crate::evm_circuit::util::{
    and, constraint_builder::BaseConstraintBuilder, not, or, select, RandomLinearCombination,
};

/// Auxiliary Gadget to verify a that a message hash is signed by the public
/// key corresponding to an Ethereum Address.
struct SignVerifyChip<F: FieldExt> {
    ecdsa_chip: EcdsaChip<Secp256k1Affine, F>,
}

const KECCAK_IS_ENABLED: usize = 0;
const KECCAK_INPUT_RLC: usize = 0;
const KECCAK_INPUT_LEN: usize = 0;
const KECCAK_OUTPUT_RLC: usize = 0;

struct SignVerifyConfig<F: FieldExt> {
    pub_key_hash: [Column<Advice>; 32],
    address: Column<Advice>,
    msg_hash_rlc: Column<Advice>,
    msg_hash_rlc_is_zero: IsZeroConfig<F>,
    msg_hash_rlc_inv: Column<Advice>,

    // ECDSA
    ecdsa_config: EcdsaConfig,
    // signature: [[Column<Advice>; 32]; 2],
    pub_key: [[Column<Advice>; 32]; 2],
    msg_hash: [Column<Advice>; 32],

    power_of_randomness: [Expression<F>; 31],

    // [is_enabled, input_rlc, input_len, output_rlc]
    keccak_table: [Column<Advice>; 4],
}

impl<F: FieldExt> SignVerifyChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Expression<F>; 31],
    ) -> SignVerifyConfig<F> {
        // create ecdsa config
        const BIT_LEN_LIMB: usize = 68;
        let (rns_base, rns_scalar) = GeneralEccChip::<Secp256k1Affine, F>::rns(BIT_LEN_LIMB);
        let main_gate_config = MainGate::<F>::configure(meta);
        let mut overflow_bit_lengths: Vec<usize> = vec![];
        overflow_bit_lengths.extend(rns_base.overflow_lengths());
        overflow_bit_lengths.extend(rns_scalar.overflow_lengths());
        let range_config = RangeChip::<F>::configure(meta, &main_gate_config, overflow_bit_lengths);

        let ecdsa_config = EcdsaConfig::new(range_config, main_gate_config);
        let pub_key = [(); 2].map(|_| [(); 32].map(|_| meta.advice_column()));
        let msg_hash = [(); 32].map(|_| meta.advice_column());

        // create address, msg_hash, pub_key_hash, and msg_hash_inv, and iz_zero

        let address = meta.advice_column();
        let pub_key_hash = [(); 32].map(|_| meta.advice_column());

        let msg_hash_rlc = meta.advice_column();

        // is_enabled === msg_hash_rlc != 0

        let msg_hash_rlc_inv = meta.advice_column();
        let msg_hash_rlc_is_zero = IsZeroChip::configure(
            meta,
            |_| Expression::Constant(F::one()), // always activate
            |virtual_cells| virtual_cells.query_advice(msg_hash_rlc, Rotation::cur()),
            msg_hash_rlc_inv, // helper column used internally?
        );
        let is_enabled = not::expr(msg_hash_rlc_is_zero.is_zero_expression.clone());

        // lookup keccak table

        let keccak_table = [(); 4].map(|_| meta.advice_column());

        // keccak lookup
        meta.lookup_any("keccak", |meta| {
            /*
                    // Conditions:
                    // - On the row with the last byte (`is_final == 1`)
                    // - Not padding
                    let enable = and::expr(vec![
                        meta.query_advice(is_final, Rotation::cur()),
                        not::expr(meta.query_advice(padding, Rotation::cur())),
                    ]);
                    let lookup_columns = vec![hash_rlc, hash_length, hash];
                    let mut constraints = vec![];
                    for i in 0..crate::bytecode_circuit::param::KECCAK_WIDTH {
                        constraints.push((
                            enable.clone() * meta.query_advice(lookup_columns[i], Rotation::cur()),
                            meta.query_advice(keccak_table[i], Rotation::cur()),
                        ))
                    }
            */

            let mut table_map = Vec::new();

            let keccak_is_enabled =
                meta.query_advice(keccak_table[KECCAK_IS_ENABLED], Rotation::cur());
            table_map.push((is_enabled.clone(), keccak_is_enabled));

            let pub_key_hash = pub_key_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            let pub_key_hash_rlc = RandomLinearCombination::random_linear_combine_expr(
                pub_key_hash,
                &power_of_randomness,
            );

            let keccak_input_rlc = meta.query_advice(msg_hash_rlc, Rotation::cur());
            table_map.push((is_enabled.clone() * pub_key_hash_rlc, keccak_input_rlc));

            /*
            let keccak_input_rlc = meta.query_advice(keccak_input_rlc, Rotation::cur());
            table_map.push((is_enabled.clone() * pub_key_hash_rlc, keccak_input_rlc));
            */

            table_map
        });

        SignVerifyConfig {
            pub_key_hash,
            address,
            msg_hash_rlc,
            msg_hash_rlc_is_zero,
            msg_hash_rlc_inv,
            ecdsa_config,
            pub_key,
            msg_hash,
            power_of_randomness,
            keccak_table,
        }
    }

    /*
        pub fn load_tables(config: &SignVerifyConfig<F>, layouter: &mut impl Layouter<F>) {
            use ecdsa::maingate::RangeInstructions;
            const BIT_LEN_LIMB: usize = 68;
            use ecdsa::integer::NUMBER_OF_LOOKUP_LIMBS;

            let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;
            let range_chip = RangeChip::<F>::new(config.range_config.clone(), bit_len_lookup).unwrap();
            range_chip.load_limb_range_table(layouter).unwrap();
            range_chip.load_overflow_range_tables(layouter).unwrap();
       }
    */
}

pub trait SignVerifyInstruction<F: FieldExt> {
    fn check(pub_key_hash: Vec<u8>, address: F, msg_hash_rlc: F, random: F) -> Result<(), Error>;
}
/*
impl<C: CurveAffine, N: FieldExt> SignVerifyConfig1<C, N> {
    pub fn create_global_configs(meta: &mut ConstraintSystem<N>) -> (RangeConfig, MainGateConfig) {
   }

    pub fn new(range_config: RangeConfig, main_gate_config: MainGateConfig) -> Self {
        Self {
            ecdsa_config: EcdsaConfig::new(range_config, main_gate_config),
            _marker_: (PhantomData::default(), PhantomData::default()),
        }
    }

}
*/

#[test]
fn test() {}

/*
class SignVerifyGadget:
    """
    Auxiliary Gadget to verify a that a message hash is signed by the public
    key corresponding to an Ethereum Address.
    """

    pub_key_hash: RLC
    address: FQ
    msg_hash_rlc: FQ  # Set to 0 to disable verification check
    ecdsa_chip: ECDSAVerifyChip

    def __init__(
        self,
        pub_key_hash: RLC,
        address: FQ,
        msg_hash_rlc: FQ,
        ecdsa_chip: ECDSAVerifyChip,
    ) -> None:
        self.pub_key_hash = pub_key_hash
        self.address = address
        self.msg_hash_rlc = msg_hash_rlc
        self.ecdsa_chip = ecdsa_chip

    @classmethod
    def assign(
        cls, signature: KeyAPI.Signature, pub_key: KeyAPI.PublicKey, msg_hash: bytes, randomness: FQ
    ):
        pub_key_hash = keccak(pub_key.to_bytes())
        self_pub_key_hash = RLC(pub_key_hash, randomness)
        self_address = FQ(int.from_bytes(pub_key_hash[-20:], "big"))
        self_msg_hash_rlc = RLC(int.from_bytes(msg_hash, "big"), randomness).value
        self_ecdsa_chip = ECDSAVerifyChip.assign(signature, pub_key, msg_hash)
        return cls(self_pub_key_hash, self_address, self_msg_hash_rlc, self_ecdsa_chip)

    def verify(self, keccak_table: KeccakTable, randomness: FQ, assert_msg: str):
        is_enabled = FQ(1 - (self.msg_hash_rlc == 0))  # 1 - is_zero(self.msg_hash_rlc)

        # 0. Verify that the first 20 bytes of the pub_key_hash equal the address
        addr_expr = FQ.linear_combine(list(reversed(self.pub_key_hash.le_bytes[-20:])), FQ(2**8))
        assert (
            addr_expr == self.address
        ), f"{assert_msg}: {hex(addr_expr.n)} != {hex(self.address.n)}"

        # 1. Verify that keccak(pub_key_bytes) = pub_key_hash by keccak table
        # lookup, where pub_key_bytes is built from the pub_key in the
        # ecdsa_chip
        pub_key_bytes = bytes(reversed(self.ecdsa_chip.pub_key[0].limbs)) + bytes(
            reversed(self.ecdsa_chip.pub_key[1].limbs)
        )
        keccak_table.lookup(
            is_enabled,
            RLC(bytes(reversed(pub_key_bytes)), randomness).value,
            FQ(64) * is_enabled,
            self.pub_key_hash.value,
            assert_msg,
        )

        # 2. Verify that the signed message in the ecdsa_chip with RLC encoding
        # corresponds to msg_hash_rlc
        msg_hash_rlc_expr = FQ.linear_combine(self.ecdsa_chip.msg_hash.limbs, randomness)
        assert (
            msg_hash_rlc_expr == self.msg_hash_rlc
        ), f"{assert_msg}: {hex(msg_hash_rlc_expr.n)} != {hex(self.msg_hash_rlc.n)}"

        # Verify the ECDSA signature
        self.ecdsa_chip.verify(is_enabled, assert_msg)
*/
