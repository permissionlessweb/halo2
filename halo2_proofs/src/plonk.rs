//! This module provides an implementation of a variant of (Turbo)[PLONK][plonk]
//! that is designed specifically for the polynomial commitment scheme described
//! in the [Halo][halo] paper.
//!
//! [halo]: https://eprint.iacr.org/2019/1021
//! [plonk]: https://eprint.iacr.org/2019/953

use blake2b_simd::Params as Blake2bParams;
use group::ff::{Field, FromUniformBytes, PrimeField};

use crate::arithmetic::CurveAffine;
use crate::helpers::{pack, unpack, CurveRead};
use crate::poly::{
    commitment::Params, Coeff, EvaluationDomain, ExtendedLagrangeCoeff, LagrangeCoeff,
    PinnedEvaluationDomain, Polynomial,
};
use crate::transcript::{ChallengeScalar, EncodedChallenge, Transcript};
mod assigned;
mod circuit;
mod error;
mod keygen;
mod lookup;
pub(crate) mod permutation;
mod vanishing;

mod prover;
mod verifier;

pub use assigned::*;
pub use circuit::*;
pub use error::*;
pub use keygen::*;
pub use prover::*;
pub use verifier::*;

use std::io;

/// This is a verifying key which allows for the verification of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct VerifyingKey<C: CurveAffine> {
    domain: EvaluationDomain<C::Scalar>,
    fixed_commitments: Vec<C>,
    permutation: permutation::VerifyingKey<C>,
    cs: ConstraintSystem<C::Scalar>,
    /// Cached maximum degree of `cs` (which doesn't change after construction).
    cs_degree: usize,
    /// The representative of this `VerifyingKey` in transcripts.
    transcript_repr: C::Scalar,
    /// used for serialization/deserialization:
    selectors: Vec<Vec<bool>>,
}

impl<C: CurveAffine> VerifyingKey<C>
where
    C::Scalar: FromUniformBytes<64>,
{
    /// Serialized format of a [`VerifyingKey<C>`] (Zcash-style binary serialization)
    ///
    /// The format is as follows (all multi-byte integers are **little-endian**):
    ///
    /// ```text
    /// +-------------------+--------------------------+
    /// | Field             | Size / Description       |
    /// +-------------------+--------------------------+
    /// | version           | 1 byte  (always 0x01)    |
    /// | num_fixed_columns | u32 LE                   |
    /// | fixed_commitments | num_fixed_columns × C::G1 (compressed) |
    /// | permutation_vk    | variable (see permutation::VerifyingKey::write) |
    /// | num_selectors     | u32 LE                   |
    /// | selectors         | variable (bit-packed)    |
    /// +-------------------+--------------------------+
    pub fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        let mut vk_buf = Vec::new();
        vk_buf.extend_from_slice(&[0x01]);

        // normal vk serialization and write spec
        let mut fixed_commitments_buf = Vec::with_capacity(self.fixed_commitments.len());
        fixed_commitments_buf.extend_from_slice(
            &(u32::try_from(self.fixed_commitments.len()).unwrap()).to_le_bytes(),
        );

        for commitment in &self.fixed_commitments {
            fixed_commitments_buf.extend_from_slice(commitment.to_bytes().as_ref());
        }
        let fixed_commitments_checksum =
            hex::encode(&<sha2::Sha256 as sha2::Digest>::digest(&fixed_commitments_buf).to_vec());
        println!(
            "halo2::write::vk::fixed_commitments::(checksum::{},length::{}) ",
            fixed_commitments_checksum,
            fixed_commitments_buf.len()
        );

        vk_buf.extend_from_slice(&fixed_commitments_buf);

        let mut permutation_buf = Vec::new();
        self.permutation.write(&mut permutation_buf)?;
        let permutation_checksum =
            hex::encode(&<sha2::Sha256 as sha2::Digest>::digest(&permutation_buf).to_vec());

        println!(
            "halo2::write::vk::permutation::(checksum::{},len::{})",
            permutation_checksum,
            permutation_buf.len()
        );

        vk_buf.extend_from_slice(&permutation_buf);

        let mut selectors_buf = Vec::new();
        selectors_buf
            .extend_from_slice(&(u32::try_from(self.selectors.len()).unwrap()).to_le_bytes());

        for selector in &self.selectors {
            for bits in selector.chunks(8) {
                // pack 8 at a time into bytes and then write
                selectors_buf.extend_from_slice(&[pack(bits)]);
            }
        }

        let selectors_checksum =
            hex::encode(&<sha2::Sha256 as sha2::Digest>::digest(&selectors_buf).to_vec());
        println!(
            "halo2::write::vk::selectors::(checksum::{},length::{})",
            selectors_checksum,
            selectors_buf.len()
        );

        vk_buf.extend_from_slice(&selectors_buf);
        let vk_checksum = hex::encode(&<sha2::Sha256 as sha2::Digest>::digest(&vk_buf).to_vec());
        println!(
            "halo2::write::vk::(checksum::{},length::{})",
            vk_checksum,
            vk_buf.len()
        );

        writer.write_all(&vk_buf)?;

        Ok(())
    }

    /// clone cs: (s)
    pub fn cs(&self) -> ConstraintSystem<C::Scalar> {
        self.cs.clone()
    }

    /// Reads a verifying key from a buffer using a pre-built constraint system.
    ///
    /// This method enables circuit-agnostic verification by using a deserialized
    /// ConstraintSystem instead of calling Circuit::configure().
    // Reads a verifying key from a buffer using a pre-built constraint system.
    ///
    /// This method enables circuit-agnostic verification by using a deserialized
    /// ConstraintSystem instead of calling Circuit::configure().
    pub fn read_with_cs<R: io::Read>(
        reader: &mut R,
        params: &Params<C>,
        cs: ConstraintSystem<C::Scalar>,
        selectors: Vec<Vec<bool>>,
    ) -> io::Result<Self> {
        eprintln!("🔑 VerifyingKey::read_with_cs starting...");
        eprintln!("  params.k: {}", params.k);
        eprintln!("  cs.num_fixed_columns: {}", cs.num_fixed_columns);
        eprintln!("  cs.num_advice_columns: {}", cs.num_advice_columns);
        eprintln!("  cs.num_instance_columns: {}", cs.num_instance_columns);
        eprintln!("  cs.num_selectors: {}", cs.num_selectors);

        // Create domain from params and CS degree
        let degree = cs.degree();
        eprintln!("  cs.degree(): {}", degree);
        let domain = EvaluationDomain::new(degree as u32, params.k);

        // Read version byte
        let mut version_byte = [0u8; 1];
        reader.read_exact(&mut version_byte)?;
        eprintln!("  version_byte: 0x{:02x}", version_byte[0]);

        if 0x01 != version_byte[0] {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "unexpected version byte: 0x{:02x} (expected 0x01)",
                    version_byte[0]
                ),
            ));
        }

        // Read fixed commitments
        let mut num_fixed_columns_le_bytes = [0u8; 4];
        reader.read_exact(&mut num_fixed_columns_le_bytes)?;
        let num_fixed_columns = u32::from_le_bytes(num_fixed_columns_le_bytes);
        eprintln!("  num_fixed_columns from VK: {}", num_fixed_columns);

        let fixed_commitments: Vec<_> = (0..num_fixed_columns)
            .map(|_| C::read(reader))
            .collect::<io::Result<_>>()?;

        // Read permutation verifying key
        eprintln!("  Reading permutation verifying key...");
        let permutation = permutation::VerifyingKey::read(reader, &cs.permutation)?;

        // Read and validate selectors count
        let mut num_selectors_le_bytes = [0u8; 4];
        reader.read_exact(&mut num_selectors_le_bytes)?;
        let num_selectors = u32::from_le_bytes(num_selectors_le_bytes);
        eprintln!("  num_selectors from VK: {}", num_selectors);

        if cs.num_selectors != num_selectors as usize {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "selector count mismatch: CS has {}, VK has {}",
                    cs.num_selectors, num_selectors
                ),
            ));
        }

        // Read selector data from VK (we already have selectors from CS, but validate/merge)
        let vk_selectors: Vec<Vec<bool>> = vec![vec![false; params.n as usize]; cs.num_selectors]
            .into_iter()
            .map(|mut selector| {
                let mut selector_bytes = vec![0u8; (selector.len() + 7) / 8];
                reader.read_exact(&mut selector_bytes)?;
                for (bits, byte) in selector.chunks_mut(8).zip(selector_bytes) {
                    unpack(byte, bits);
                }
                Ok(selector)
            })
            .collect::<io::Result<_>>()?;

        // Use the selectors from the VK (they contain the actual assignments)
        // let (cs, _) = cs.compress_selectors(vk_selectors.clone());

        eprintln!("✓ VerifyingKey::read_with_cs completed successfully");
        Ok(Self::from_parts(
            domain,
            fixed_commitments,
            permutation,
            cs,
            vk_selectors,
        ))
    }

    /// Reads a verifying key from a slice of bytes using a pre-built constraint system.
    pub fn from_bytes_with_cs(
        mut bytes: &[u8],
        params: &Params<C>,
        cs: ConstraintSystem<C::Scalar>,
        selectors: Vec<Vec<bool>>,
    ) -> io::Result<Self> {
        Self::read_with_cs(&mut bytes, params, cs, selectors)
    }

    fn from_parts(
        domain: EvaluationDomain<C::Scalar>,
        fixed_commitments: Vec<C>,
        permutation: permutation::VerifyingKey<C>,
        cs: ConstraintSystem<C::Scalar>,
        selectors: Vec<Vec<bool>>,
    ) -> Self {
        // Compute cached values.
        let cs_degree = cs.degree();

        let mut vk = Self {
            domain,
            fixed_commitments,
            permutation,
            cs,
            cs_degree,
            // Temporary, this is not pinned.
            transcript_repr: C::Scalar::ZERO,
            selectors,
        };

        let mut hasher = Blake2bParams::new()
            .hash_length(64)
            .personal(b"Halo2-Verify-Key")
            .to_state();

        let s = format!("{:?}", vk.pinned());

        hasher.update(&(s.len() as u64).to_le_bytes());
        hasher.update(s.as_bytes());

        // Hash in final Blake2bState
        vk.transcript_repr = C::Scalar::from_uniform_bytes(hasher.finalize().as_array());

        vk
    }
}

impl<C: CurveAffine> VerifyingKey<C> {
    /// Hashes a verification key into a transcript.
    pub fn hash_into<E: EncodedChallenge<C>, T: Transcript<C, E>>(
        &self,
        transcript: &mut T,
    ) -> io::Result<()> {
        transcript.common_scalar(self.transcript_repr)?;

        Ok(())
    }

    /// Obtains a pinned representation of this verification key that contains
    /// the minimal information necessary to reconstruct the verification key.
    pub fn pinned(&self) -> PinnedVerificationKey<'_, C> {
        PinnedVerificationKey {
            base_modulus: C::Base::MODULUS,
            scalar_modulus: C::Scalar::MODULUS,
            domain: self.domain.pinned(),
            fixed_commitments: &self.fixed_commitments,
            permutation: &self.permutation,
            cs: self.cs.pinned(),
        }
    }
}

/// Minimal representation of a verification key that can be used to identify
/// its active contents.
#[allow(dead_code)]
#[derive(Debug)]
pub struct PinnedVerificationKey<'a, C: CurveAffine> {
    base_modulus: &'static str,
    scalar_modulus: &'static str,
    domain: PinnedEvaluationDomain<'a, C::Scalar>,
    cs: PinnedConstraintSystem<'a, C::Scalar>,
    fixed_commitments: &'a Vec<C>,
    permutation: &'a permutation::VerifyingKey<C>,
}
/// This is a proving key which allows for the creation of proofs for a
/// particular circuit.
#[derive(Clone, Debug)]
pub struct ProvingKey<C: CurveAffine> {
    vk: VerifyingKey<C>,
    l0: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    l_blind: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    l_last: Polynomial<C::Scalar, ExtendedLagrangeCoeff>,
    fixed_values: Vec<Polynomial<C::Scalar, LagrangeCoeff>>,
    fixed_polys: Vec<Polynomial<C::Scalar, Coeff>>,
    fixed_cosets: Vec<Polynomial<C::Scalar, ExtendedLagrangeCoeff>>,
    permutation: permutation::ProvingKey<C>,
}

impl<C: CurveAffine> ProvingKey<C> {
    /// Get the underlying [`VerifyingKey`].
    pub fn get_vk(&self) -> &VerifyingKey<C> {
        &self.vk
    }
}

impl<C: CurveAffine> VerifyingKey<C> {
    /// Get the underlying [`EvaluationDomain`].
    pub fn get_domain(&self) -> &EvaluationDomain<C::Scalar> {
        &self.domain
    }
}

#[derive(Clone, Copy, Debug)]
struct Theta;
type ChallengeTheta<F> = ChallengeScalar<F, Theta>;

#[derive(Clone, Copy, Debug)]
struct Beta;
type ChallengeBeta<F> = ChallengeScalar<F, Beta>;

#[derive(Clone, Copy, Debug)]
struct Gamma;
type ChallengeGamma<F> = ChallengeScalar<F, Gamma>;

#[derive(Clone, Copy, Debug)]
struct Y;
type ChallengeY<F> = ChallengeScalar<F, Y>;

#[derive(Clone, Copy, Debug)]
struct X;
type ChallengeX<F> = ChallengeScalar<F, X>;
