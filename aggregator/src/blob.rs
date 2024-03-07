use crate::{barycentric::interpolate, ChunkHash};
use eth_types::U256;
use ethers_core::utils::keccak256;
use halo2_proofs::halo2curves::bls12_381::Scalar;
use std::iter::once;

pub const BLOB_WIDTH: usize = 4096;
pub const BYTES_PER_BLOB_ELEMENT: usize = 32;
pub const LOG_BLOG_WIDTH: usize = 12;

#[derive(Clone, Debug, Default)]
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
        for (i, byte) in self.bytes().enumerate() {
            scalar_bytes[i / 31][i % 31] = byte;
        }
        scalar_bytes.map(|bytes| Scalar::from_bytes(&bytes).unwrap())
    }

    pub fn random_point(&self) -> Scalar {
        let chunk_tx_bytes_hashes = self.0.iter().flat_map(keccak256);

        let input: Vec<_> = self.metadata_bytes().chain(chunk_tx_bytes_hashes).collect();
        // Convert to U256 first because Scalar::from_bytes will fail if bytes are non-canonical.
        Scalar::from_raw(U256::from(keccak256(input)).0)
    }

    fn metadata_bytes(&self) -> impl Iterator<Item = u8> + '_ {
        let n_chunks = self.0.len();
        let chunk_lengths = self.0.iter().map(Vec::len);
        once(u8::try_from(n_chunks).unwrap())
            .chain(chunk_lengths.flat_map(|x| u16::try_from(x).unwrap().to_le_bytes()))
    }

    fn bytes(&self) -> impl Iterator<Item = u8> + '_ {
        self.metadata_bytes()
            .chain(self.0.iter().flat_map(|x| x.into_iter().map(|x| *x)))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::barycentric::ROOTS_OF_UNITY;
    use reth_primitives::{
        constants::eip4844::MAINNET_KZG_TRUSTED_SETUP,
        kzg::{Blob as RethBlob, KzgProof},
    };

    #[test]
    fn empty_chunks_random_point() {
        let empty_blob = Blob::default();
        assert_eq!(
            empty_blob.random_point(),
            Scalar::from_raw(U256::from(keccak256([0u8])).0)
        )
    }

    #[test]
    fn zero_blob() {
        let blob = Blob::default();

        let z = blob.random_point();
        let y = interpolate(z, blob.coefficients());

        let mut z_bytes = z.to_bytes();
        z_bytes.reverse();

        let reth_blob = RethBlob::new([0; 131072]);
        let (proof, y) =
            KzgProof::compute_kzg_proof(&reth_blob, &z_bytes.into(), &MAINNET_KZG_TRUSTED_SETUP)
                .unwrap();

        assert_eq!(
            Scalar::from_bytes(&y).unwrap(),
            interpolate(z, blob.coefficients())
        );
        assert_eq!(Scalar::from_bytes(&y).unwrap(), Scalar::zero(),);
    }

    #[test]
    fn identity_polynomial() {
        let reth_blob = RethBlob::from_bytes(
            &ROOTS_OF_UNITY
                .into_iter()
                .flat_map(|x| to_be_bytes(x))
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let z = to_be_bytes(Scalar::from(2341234));
        let (_, y) =
            KzgProof::compute_kzg_proof(&reth_blob, &z.into(), &MAINNET_KZG_TRUSTED_SETUP).unwrap();

        assert_eq!(y, z.into());
    }

    // #[test]
    // fn mason() {
    //     let blob = Blob(vec![
    //         vec![30; 56],
    //         vec![200; 100],
    //         vec![0; 340],
    //         vec![10; 23],
    //     ]);

    //     let z = blob.random_point();
    //     let y = interpolate(z, blob.coefficients());

    //     let mut z_bytes = z.to_bytes();
    //     z_bytes.reverse();

    //     let reth_blob = RethBlob::from_bytes(
    //         &blob
    //             .coefficients()
    //             .iter()
    //             .flat_map(|x| {
    //                 let mut bytes = x.to_bytes();
    //                 bytes.reverse();
    //                 bytes
    //             })
    //             .collect::<Vec<_>>(),
    //     )
    //     .unwrap();
    //     let (proof, y) =
    //         KzgProof::compute_kzg_proof(&reth_blob, &z_bytes.into(), &MAINNET_KZG_TRUSTED_SETUP)
    //             .unwrap();

    //     assert_eq!(
    //         Scalar::from_bytes(&y).unwrap(),
    //         interpolate(z, blob.coefficients())
    //     );
    //     assert_eq!(Scalar::from_bytes(&y).unwrap(), Scalar::zero(),);
    //     // assert_eq!(Scalar::from_bytes(&y).unwrap(), Scalar::one(),);
    // }

    fn to_be_bytes(x: Scalar) -> [u8; 32] {
        let mut bytes = x.to_bytes();
        bytes.reverse();
        bytes
    }

    #[test]
    fn test_be_bytes() {
        let mut be_bytes_one = [0; 32];
        be_bytes_one[31] = 1;
        assert_eq!(to_be_bytes(Scalar::one()), be_bytes_one);
    }
}
