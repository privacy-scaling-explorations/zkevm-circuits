use crate::barycentric::interpolate;
use eth_types::U256;
use ethers_core::utils::keccak256;
use halo2_proofs::halo2curves::bls12_381::Scalar;

pub const BLOB_WIDTH: usize = 4096;
pub const BYTES_PER_BLOB_ELEMENT: usize = 32;
pub const LOG_BLOG_WIDTH: usize = 12;

#[derive(Clone, Copy, Debug)]
pub struct Blob([[u8; BYTES_PER_BLOB_ELEMENT]; BLOB_WIDTH]);

impl Blob {
    pub fn new(bytes: impl Iterator<Item = u8>) -> Self {
        let mut blob = [[0; BYTES_PER_BLOB_ELEMENT]; BLOB_WIDTH];
        for (i, byte) in bytes.enumerate() {
            blob[i / 31][i % 31] = byte;
        }
        Self(blob)
    }

    pub fn bytes(&self) -> Vec<u8> {
        self.0.into_iter().flat_map(|x| x.into_iter()).collect()
    }

    pub fn coefficients(&self) -> [Scalar; BLOB_WIDTH] {
        self.0
            .map(|bytes| Scalar::from_bytes(&bytes).expect("asdf;wlqkrj;alskdf"))
    }

    pub fn hash_to_scalar(&self) -> Scalar {
        // Convert to U256 first because Scalar::from_bytes will fail if bytes are non-canonical.
        Scalar::from_raw(U256::from(keccak256(self.bytes())).0)
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
        let z = blob.hash_to_scalar();

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
