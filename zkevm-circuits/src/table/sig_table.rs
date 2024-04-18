use super::*;

use eth_types::sign_types::SignData;

/// The sig table is used to verify signatures, used in tx circuit and ecrecover precompile.
#[derive(Clone, Copy, Debug)]
pub struct SigTable {
    /// Indicates whether or not the gates are enabled on the current row.
    pub q_enable: Column<Fixed>,
    /// Keccak256 hash of the message that's signed.
    pub msg_hash: WordLoHi<Column<Advice>>,
    /// signature's `r` component.
    pub sig_r: WordLoHi<Column<Advice>>,
    /// signature's `s` component.
    pub sig_s: WordLoHi<Column<Advice>>,
    /// should be in range [0, 1]
    pub sig_v: Column<Advice>,
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
            msg_hash: WordLoHi::new([meta.advice_column(), meta.advice_column()]),
            sig_r: WordLoHi::new([meta.advice_column(), meta.advice_column()]),
            sig_s: WordLoHi::new([meta.advice_column(), meta.advice_column()]),
            sig_v: meta.advice_column(),
            recovered_addr: meta.advice_column(),
            is_valid: meta.advice_column(),
        }
    }

    /// Assign witness data from a block to the verification table.
    pub fn dev_load<F: Field>(
        &self,
        layouter: &mut impl Layouter<F>,
        block: &Block<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "sig table (dev load)",
            |mut region| {
                let signatures: Vec<SignData> = block.get_sign_data(false);

                for (offset, sign_data) in signatures.iter().enumerate() {
                    let msg_hash =
                        WordLoHi::from(U256::from(sign_data.msg_hash.to_bytes())).into_value();
                    let sig_r =
                        WordLoHi::from(U256::from(sign_data.signature.0.to_bytes())).into_value();
                    let sig_s =
                        WordLoHi::from(U256::from(sign_data.signature.1.to_bytes())).into_value();
                    let sig_v = Value::known(F::from(sign_data.signature.2 as u64));
                    let recovered_addr = Value::known(sign_data.get_addr().to_scalar().unwrap());
                    region.assign_fixed(
                        || format!("sig table q_enable {offset}"),
                        self.q_enable,
                        offset,
                        || Value::known(F::ONE),
                    )?;
                    for (column, value) in [
                        (self.sig_v, sig_v),
                        (self.recovered_addr, recovered_addr),
                        (
                            self.is_valid,
                            Value::known(F::from(!sign_data.get_addr().is_zero() as u64)),
                        ),
                    ] {
                        region.assign_advice(
                            || "assign sign data on sig table",
                            column,
                            offset,
                            || value,
                        )?;
                    }
                    for (column, value) in [
                        (self.msg_hash, msg_hash),
                        (self.sig_r, sig_r),
                        (self.sig_s, sig_s),
                    ] {
                        value.assign_advice(
                            &mut region,
                            || "assign sign data on sig table",
                            column,
                            offset,
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
            self.msg_hash.lo().into(),
            self.msg_hash.hi().into(),
            self.sig_v.into(),
            self.sig_r.lo().into(),
            self.sig_r.hi().into(),
            self.sig_s.lo().into(),
            self.sig_s.hi().into(),
            self.recovered_addr.into(),
            self.is_valid.into(),
        ]
    }

    fn annotations(&self) -> Vec<String> {
        vec![
            String::from("q_enable"),
            String::from("msg_hash_lo"),
            String::from("msg_hash_hi"),
            String::from("sig_v"),
            String::from("sig_r_lo"),
            String::from("sig_r_hi"),
            String::from("sig_s_lo"),
            String::from("sig_s_hi"),
            String::from("recovered_addr"),
            String::from("is_valid"),
        ]
    }
}
