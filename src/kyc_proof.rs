use super::core::*;
use rand_core::RngCore;
use rand_core::OsRng;
//use crypto::digest::Digest as Dgst;
use alloc::vec::*;
use sha2::Sha256;
use sha2::Digest;
use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;
use sha2::Sha512;

pub struct KYCProof {
    new_public_key: CurveVector,
    ap_recoverable_keys: CurveVector,
    proof: Proof,
    r: Vec<Scalar>,
}

// pub fn create_kyc_shuffle(
//         tuples: &mut [VectorTuple],
//         secret: Scalar,
//     ) -> KYCProof {
//         let hidden_index = shuffle(tuples);
//         return create_kyc(tuples, hidden_index, secret);
//     }
//Sa and sBa are required only when the KYC proof is provided at spend.
//But anyway the AP traceability cannot be done from the sending side, so in case
// of KYC proof at send, we do not need
#[allow(non_snake_case)]
pub fn create_kyc(
    sources: Vec<CurveVector>,
    hidden_index: usize,
    ap_bases: &mut [EdwardsPoint],
    T: EdwardsPoint,
    secret: Scalar,
) -> (Scalar, KYCProof) {
    let mut csprng: OsRng = OsRng::default();
    let mut Aa = EdwardsPoint::default();
    let mut rs = Vec::new();
    for i in 0..ap_bases.len() {
        let r = Scalar::random(&mut csprng);
        Aa += r * ap_bases[i];
        rs.push(r);
    }
    let Ba = secret * Aa;
    let H = hash_to_edwards(&T.compress().to_bytes());
    let pH = secret * H;
    let s = Scalar::random(&mut csprng);
    let Sa = s * Aa;
    let sBa = s * Ba;
    let mut input_tuples = Vec::new();
    for source in sources {
        let mut vector_tuple = Vec::new();
        vector_tuple.push(source);
        vector_tuple.push(CurveVector { x: H, y: pH });
        vector_tuple.push(CurveVector { x: Aa, y: Ba });
        vector_tuple.push(CurveVector { x: Sa, y: sBa });

        input_tuples.push(VectorTuple {
            values: vector_tuple,
        });
    }
    let proof = create_zkplmt(&input_tuples, hidden_index, secret);
    return (
        s,
        KYCProof {
            new_public_key: CurveVector { x: H, y: pH },
            ap_recoverable_keys: CurveVector { x: Aa, y: Ba },
            proof: proof,
            r: rs,
        },
    );
}

#[allow(non_snake_case)]
pub fn verify_kyc(
    sources: Vec<CurveVector>,
    sources_S: Vec<EdwardsPoint>,
    ap_bases: &mut [EdwardsPoint],
    T: EdwardsPoint,
    kyc_proof: KYCProof,
    U: EdwardsPoint,
) -> bool {
    let H = hash_to_edwards(&T.compress().to_bytes());

    if H != kyc_proof.new_public_key.x {
        return false;
    }

    let mut Aa = EdwardsPoint::default();
    for i in 0..ap_bases.len() {
        let r = kyc_proof.r[i];
        Aa += r * ap_bases[i];
    }
    if Aa != kyc_proof.ap_recoverable_keys.x {
        return false;
    }
    let Ba = kyc_proof.ap_recoverable_keys.y;

    let mut input_tuples = Vec::new();

    for i in 0..sources.len() {
        let mut vector_tuple = Vec::new();
        let source = sources[i];
        vector_tuple.push(source);
        vector_tuple.push(kyc_proof.new_public_key);
        vector_tuple.push(CurveVector { x: Aa, y: Ba });
        vector_tuple.push(CurveVector {
            x: sources_S[i],
            y: U,
        });

        input_tuples.push(VectorTuple {
            values: vector_tuple,
        });
    }
    return verify_zkplmt(&input_tuples, &kyc_proof.proof);
}
