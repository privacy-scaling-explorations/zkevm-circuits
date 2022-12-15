use std::collections::HashMap;

use anyhow::Context;
use anyhow::Result;
use eth_types::{geth_types::Account, Address, Bytes, H256, U256};

use crate::compiler::Compiler;

use super::JsonStateTestBuilder;

/// returns the element as an address
pub fn parse_address(as_str: &str) -> Result<Address> {
    if let Some(hex) = as_str.strip_prefix("0x") {
        Ok(Address::from_slice(
            &hex::decode(hex).context("parse_address")?,
        ))
    } else {
        Ok(Address::from_slice(
            &hex::decode(as_str).context("parse_address")?,
        ))
    }
}

/// returns the element as a to address
pub fn parse_to_address(as_str: &str) -> Result<Option<Address>> {
    if as_str.trim().is_empty() {
        return Ok(None);
    }
    parse_address(as_str).map(|x| Ok(Some(x)))?
}

/// returns the element as an array of bytes
pub fn parse_bytes(as_str: &str) -> Result<Bytes> {
    if let Some(hex) = as_str.strip_prefix("0x") {
        Ok(Bytes::from(hex::decode(hex).context("parse_bytes")?))
    } else {
        Ok(Bytes::from(hex::decode(as_str).context("parse_bytes")?))
    }
}

/// parse a hash entry
pub fn parse_hash(value: &str) -> Result<H256> {
    if let Some(hex) = value.strip_prefix("0x") {
        Ok(H256::from_slice(&hex::decode(hex).context("parse_hash")?))
    } else {
        Ok(H256::from_slice(&hex::decode(value).context("parse_hash")?))
    }
}

/// parse an uint256 entry
pub fn parse_u256(as_str: &str) -> Result<U256> {
    if let Some(stripped) = as_str.strip_prefix("0x") {
        Ok(U256::from_str_radix(stripped, 16)?)
    } else if as_str
        .to_lowercase()
        .contains(['a', 'b', 'c', 'd', 'e', 'f'])
    {
        Ok(U256::from_str_radix(as_str, 16)?)
    } else {
        Ok(U256::from_str_radix(as_str, 10)?)
    }
}

/// parse u64 entry
#[allow(clippy::cast_sign_loss)]
pub fn parse_u64(as_str: &str) -> Result<u64> {
    if let Some(stripped) = as_str.strip_prefix("0x") {
        Ok(U256::from_str_radix(stripped, 16)?.as_u64())
    } else {
        Ok(U256::from_str_radix(as_str, 10)?.as_u64())
    }
}
