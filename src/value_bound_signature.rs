use super::core::*;
use alloc::vec::*;
use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;

use rand_core::RngCore;
use rand_core::OsRng;

#[derive(Clone, Copy)]
struct Source {
    one_time_key: CurveVector,
}

#[derive(Copy, Clone)]
#[allow(non_snake_case)]
pub struct ValueCommitmentPublic {
    S: EdwardsPoint,
    V: EdwardsPoint,
    A: EdwardsPoint,
    B: EdwardsPoint,
}

#[derive(Copy, Clone)]
#[allow(non_snake_case)]
pub struct ValueCommitment {
    value_commitment_public: ValueCommitmentPublic,
    v: Scalar,
    s: Scalar,
}

#[derive(Clone)]
#[allow(non_snake_case)]
pub struct BlindingSignature {
    value_commitment_public: ValueCommitmentPublic,
    proof: Proof,
    I_: EdwardsPoint,
}

fn transform_blinding_key(vc: ValueCommitment, ss: Scalar) -> ValueCommitment {
    let t = ss * vc.s.invert();
    let vcp = vc.value_commitment_public;
    ValueCommitment {
        value_commitment_public: ValueCommitmentPublic {
            S: t * vcp.S,
            V: t * vcp.V,
            A: t * vcp.A,
            B: t * vcp.B,
        },
        v: vc.v,
        s: ss,
    }
}

#[allow(non_snake_case)]
pub fn verify_blinding_signatures(
    input_commitments: &[ValueCommitmentPublic],
    signature: &BlindingSignature,
) -> bool {
    let S_ = signature.value_commitment_public.S;
    let V_ = signature.value_commitment_public.V;
    let A_ = signature.value_commitment_public.A;
    let B_ = signature.value_commitment_public.B;

    let mut tuples = Vec::new();
    for c in input_commitments {
        let mut vt = Vec::new();
        vt.push(CurveVector { x: c.S, y: S_ });
        vt.push(CurveVector { x: c.V, y: V_ });
        vt.push(CurveVector { x: c.A, y: A_ });
        vt.push(CurveVector { x: c.B, y: B_ });
        let H = hash_to_edwards(c.A.compress().as_bytes());
        vt.push(CurveVector {
            x: signature.I_,
            y: H,
        });
        tuples.push(VectorTuple { values: vt });
    }
    verify_zkplmt(&tuples, &signature.proof)
}

#[allow(non_snake_case)]
pub fn create_blinding_signature(
    input_commitments: &mut [ValueCommitmentPublic],
    v: Scalar,
    s: Scalar,
    ss: Scalar,
    k: usize,
) -> BlindingSignature {
    let transformed_commitment = transform_blinding_key(
        ValueCommitment {
            value_commitment_public: input_commitments[k],
            s: s,
            v: v,
        },
        ss,
    );

    let t = ss * s.invert();

    let I = t.invert() * (hash_to_edwards(input_commitments[k].A.compress().as_bytes()));

    let mut tuples = Vec::new();
    let S_ = transformed_commitment.value_commitment_public.S;
    let V_ = transformed_commitment.value_commitment_public.V;
    let A_ = transformed_commitment.value_commitment_public.A;
    let B_ = transformed_commitment.value_commitment_public.B;
    for c in input_commitments {
        let mut vt = Vec::new();
        vt.push(CurveVector { x: c.S, y: S_ });
        vt.push(CurveVector { x: c.V, y: V_ });
        vt.push(CurveVector { x: c.A, y: A_ });
        vt.push(CurveVector { x: c.B, y: B_ });
        let H = hash_to_edwards(c.A.compress().as_bytes());
        vt.push(CurveVector { x: I, y: H });
        tuples.push(VectorTuple { values: vt });
    }

    BlindingSignature {
        proof: create_zkplmt(&tuples, k, t),
        value_commitment_public: transformed_commitment.value_commitment_public,
        I_: I,
    }
}

fn create_random_divisions(sum: Scalar, count: usize) -> Vec<Scalar> {
    let mut csprng: OsRng = OsRng::default();
    let mut output = Vec::new();
    let mut s = sum;
    for _ in 0..count - 1 {
        let r = Scalar::random(&mut csprng);
        s -= r;
        output.push(r);
    }
    output.push(s);
    return output;
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::scalar::Scalar;
    use rand_core::OsRng;

    #[test]
    fn test_random_divisions() {
        let mut csprng: OsRng = OsRng::default();
        let sum = Scalar::random(&mut csprng);
        let divisions = create_random_divisions(sum, 5);
        assert_eq!(divisions.len(), 5);

        let mut s = Scalar::zero();
        for r in divisions {
            s += r;
        }

        assert_eq!(s, sum);
    }

    #[test]
    fn test_blinding_signature() {
        let mut csprng: OsRng = OsRng::default();

        let mut input_tuples = Vec::new();

        for _ in 0..3 {
            let s = Scalar::random(&mut csprng);
            let S = s * get_G();
            let v = Scalar::random(&mut csprng);
            let V = v * s * get_K();
            let a = Scalar::random(&mut csprng);
            let A = a * get_G();
            let p = Scalar::random(&mut csprng);
            let B = p * A;
            let vc_public = ValueCommitmentPublic {
                S: S,
                V: V,
                A: A,
                B: B,
            };

            input_tuples.push(vc_public);
        }

        let s = Scalar::random(&mut csprng);
        let S = s * get_G();
        let v = Scalar::random(&mut csprng);
        let V = v * s * get_K();
        let a = Scalar::random(&mut csprng);
        let A = a * get_G();
        let p = Scalar::random(&mut csprng);
        let B = p * A;
        let vc_public = ValueCommitmentPublic {
            S: S,
            V: V,
            A: A,
            B: B,
        };
        input_tuples.push(vc_public);
        assert_eq!(input_tuples.len(), 4);

        for _ in 0..5 {
            let s = Scalar::random(&mut csprng);
            let S = s * get_G();
            let v = Scalar::random(&mut csprng);
            let V = v * s * get_K();
            let a = Scalar::random(&mut csprng);
            let A = a * get_G();
            let p = Scalar::random(&mut csprng);
            let B = p * A;
            let vc_public = ValueCommitmentPublic {
                S: S,
                V: V,
                A: A,
                B: B,
            };

            input_tuples.push(vc_public);
        }

        let ss = Scalar::random(&mut csprng);
        let signature = create_blinding_signature(&mut input_tuples, v, s, ss, 3);
        assert!(verify_blinding_signatures(&input_tuples, &signature));
    }
}
