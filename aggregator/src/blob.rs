use crate::{barycentric::interpolate, ChunkHash};
use eth_types::U256;
use ethers_core::utils::keccak256;
use halo2_proofs::halo2curves::bls12_381::Scalar;
use std::iter::once;

pub const BLOB_WIDTH: usize = 4096;
pub const BYTES_PER_BLOB_ELEMENT: usize = 32;
pub const LOG_BLOG_WIDTH: usize = 12;

#[derive(Clone, Debug)]
pub struct Blob(Vec<Vec<u8>>);

impl Blob {
    pub fn new(chunk_hashes: &[ChunkHash]) -> Self {
        Self(
            chunk_hashes
                .iter()
                .filter(|chunk_hash| !chunk_hash.is_padding)
                .map(|chunk_hash| chunk_hash.tx_bytes.clone())
                .collect(),
        )
    }

    pub fn coefficients(&self) -> [Scalar; BLOB_WIDTH] {
        let mut scalar_bytes = [[0; BYTES_PER_BLOB_ELEMENT]; BLOB_WIDTH];
        for (i, byte) in self.0.iter().flat_map(|x| x.into_iter()).enumerate() {
            scalar_bytes[i / 31][i % 31] = *byte;
        }
        scalar_bytes.map(|bytes| Scalar::from_bytes(&bytes).unwrap())
    }

    pub fn random_point(&self) -> Scalar {
        let n_chunks = self.0.len();
        let chunk_lengths = self.0.iter().map(Vec::len);
        let chunk_tx_bytes_hashes = self.0.iter().flat_map(keccak256);

        let input: Vec<_> = once(u8::try_from(n_chunks).unwrap())
            .chain(chunk_lengths.flat_map(|x| u16::try_from(x).unwrap().to_le_bytes()))
            .chain(chunk_tx_bytes_hashes)
            .collect();
        // Convert to U256 first because Scalar::from_bytes will fail if bytes are non-canonical.
        Scalar::from_raw(U256::from(keccak256(input)).0)
    }
}

#[derive(Clone, Debug)]
pub struct BlobAssignments {
    pub z: Scalar,
    pub y: Scalar,
    pub coefficients: [Scalar; BLOB_WIDTH],
}

impl From<&Blob> for BlobAssignments {
    fn from(blob: &Blob) -> Self {
        let coefficients = blob.coefficients();
        let z = blob.random_point();

        Self {
            z,
            coefficients,
            y: interpolate(z, coefficients),
        }
    }
}

impl Default for BlobAssignments {
    fn default() -> Self {
        Self {
            z: Scalar::default(),
            y: Scalar::default(),
            coefficients: [Scalar::default(); BLOB_WIDTH],
        }
    }
}
