use super::*;

use crate::{evm_circuit::util::rlc, util::Challenges};
use eth_types::sign_types::SignData;

/// The sig table is used to verify signatures, used in tx circuit and ecrecover precompile.
#[derive(Clone, Copy, Debug)]
pub struct SigTable {
    /// Indicates whether or not the gates are enabled on the current row.
    pub q_enable: Column<Fixed>,
    /// Random-linear combination of the Keccak256 hash of the message that's signed.
    pub msg_hash_rlc: Column<Advice>,
    /// should be in range [0, 1]
    pub sig_v: Column<Advice>,
    /// Random-linear combination of the signature's `r` component.
    pub sig_r_rlc: Column<Advice>,
    /// Random-linear combination of the signature's `s` component.
    pub sig_s_rlc: Column<Advice>,
    /// The recovered address, i.e. the 20-bytes address that must have signed the message.
    pub recovered_addr: Column<Advice>,
    /// Indicates whether or not the signature is valid or not upon signature verification.
    pub is_valid: Column<Advice>,
}

impl SigTable {
    /// Construct the SigTable.
    pub fn construct<F: Field>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            q_enable: meta.fixed_column(),
            msg_hash_rlc: meta.advice_column_in(SecondPhase),
            sig_v: meta.advice_column(),
            sig_s_rlc: meta.advice_column_in(SecondPhase),
            sig_r_rlc: meta.advice_column_in(SecondPhase),
            recovered_addr: meta.advice_column(),
            is_valid: meta.advice_column(),
        }
    }

    /// Assign witness data from a block to the verification table.
    pub fn dev_load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
        challenges: &Challenges<Value<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "sig table (dev load)",
            |mut region| {
                let signatures: Vec<SignData> = block.get_sign_data(false);

                let evm_word = challenges.evm_word();
                for (offset, sign_data) in signatures.iter().enumerate() {
                    let msg_hash_rlc = evm_word.map(|challenge| {
                        rlc::value(
                            sign_data.msg_hash.to_bytes().iter().collect_vec(),
                            challenge,
                        )
                    });
                    let sig_r_rlc = evm_word.map(|challenge| {
                        rlc::value(
                            sign_data.signature.0.to_bytes().iter().collect_vec(),
                            challenge,
                        )
                    });
                    let sig_s_rlc = evm_word.map(|challenge| {
                        rlc::value(
                            sign_data.signature.1.to_bytes().iter().collect_vec(),
                            challenge,
                        )
                    });
                    let sig_v = Value::known(F::from(sign_data.signature.2 as u64));
                    let recovered_addr = Value::known(sign_data.get_addr().to_scalar().unwrap());
                    region.assign_fixed(
                        || format!("sig table q_enable {offset}"),
                        self.q_enable,
                        offset,
                        || Value::known(F::ONE),
                    )?;
                    for (column_name, column, value) in [
                        ("msg_hash_rlc", self.msg_hash_rlc, msg_hash_rlc),
                        ("sig_v", self.sig_v, sig_v),
                        ("sig_r_rlc", self.sig_r_rlc, sig_r_rlc),
                        ("sig_s_rlc", self.sig_s_rlc, sig_s_rlc),
                        ("recovered_addr", self.recovered_addr, recovered_addr),
                        (
                            "is_valid",
                            self.is_valid,
                            Value::known(F::from(!sign_data.get_addr().is_zero())),
                        ),
                    ] {
                        region.assign_advice(
                            || format!("sig table {column_name} {offset}"),
                            column,
                            offset,
                            || value,
                        )?;
                    }
                }

                Ok(())
            },
        )?;

        Ok(())
    }
}

impl<F: Field> LookupTable<F> for SigTable {
    fn columns(&self) -> Vec<Column<Any>> {
        vec![
            self.q_enable.into(),
            self.msg_hash_rlc.into(),
            self.sig_v.into(),
            self.sig_r_rlc.into(),
            self.sig_s_rlc.into(),
            self.recovered_addr.into(),
            self.is_valid.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("q_enable"),
            String::from("msg_hash_rlc"),
            String::from("sig_v"),
            String::from("sig_r_rlc"),
            String::from("sig_s_rlc"),
            String::from("recovered_addr"),
            String::from("is_valid"),
        ]
    }
}
