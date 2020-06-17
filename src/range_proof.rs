

extern crate sha2;

extern crate curve25519_dalek;

use super::core::*;
use super::value_bound_signature::*;
use alloc::vec::*;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;

#[allow(non_snake_case)]
#[derive(Clone)]
pub struct RangeProof {
    proofs: Vec<Proof>,
    X: Vec<EdwardsPoint>,
    S: EdwardsPoint,
}

fn get_ith_power_of_2(i: usize) -> Scalar {
    let byte_pos = i / 8;
    let bit_pos = i % 8;
    let mut byte_val = 1;

    byte_val <<= bit_pos;

    let mut bytes = [0u8; 32];
    bytes[byte_pos] = byte_val;
    return Scalar::from_bits(bytes);
}

#[allow(non_snake_case)]
pub fn verify_range_proof(
    V: EdwardsPoint,
    bases: &[EdwardsPoint],
    n: usize,
    range_proof: &RangeProof,
) -> bool {
    if bases.len() != n || range_proof.X.len() != n || range_proof.proofs.len() != n {
        return false;
    }
    let mut sum = EdwardsPoint::default();
    for X in &range_proof.X {
        sum = sum + X;
    }

    if V != sum {
        return false;
    }

    let G = get_G();
    let S = range_proof.S;

    for i in 0..n {
        let proof = &range_proof.proofs[i];
        let X = range_proof.X[i];
        let R = bases[i];
        let W = R + get_ith_power_of_2(i) * get_K();

        let mut one_tuple = Vec::new();
        one_tuple.push(CurveVector { x: G, y: S });
        one_tuple.push(CurveVector { x: W, y: X });

        let one_vector_tuple = VectorTuple { values: one_tuple };

        let mut zero_tuple = Vec::new();
        zero_tuple.push(CurveVector { x: G, y: S });
        zero_tuple.push(CurveVector { x: R, y: X });

        let zero_vector_tuple = VectorTuple { values: zero_tuple };

        let mut tuples = Vec::new();
        tuples.push(zero_vector_tuple);
        tuples.push(one_vector_tuple);

        if !verify_zkplmt(&tuples, proof) {
            return false;
        }
    }

    return true;
}

#[allow(non_snake_case)]
pub fn create_range_proof(v: Scalar, s: Scalar, bases: &[EdwardsPoint]) -> RangeProof {
    let bytes = v.to_bytes();
    let mut bits = Vec::new();
    let mut k = 0;
    'outer: for i in 0..bytes.len() {
        let mut value = bytes[i];
        for j in 0..8 {
            if k >= bases.len() {
                break 'outer;
            }
            let bit = value & 0x1;
            if bit > 0 {
                bits.push(true)
            } else {
                bits.push(false);
            }
            value = value >> 1;
            k += 1;
        }
    }

    let G = get_G();
    let S = s * G;
    //Now we have the bit values, so we create a proof for each bit
    let mut proofs = Vec::new();

    let mut Xs = Vec::new();
    for i in 0..bits.len() {
        let R = bases[i];
        let W = R + get_ith_power_of_2(i) * get_K();
        let X = if bits[i] { s * W } else { s * R };

        let mut one_tuple = Vec::new();
        one_tuple.push(CurveVector { x: G, y: S });
        one_tuple.push(CurveVector { x: W, y: X });

        let one_vector_tuple = VectorTuple { values: one_tuple };

        let mut zero_tuple = Vec::new();
        zero_tuple.push(CurveVector { x: G, y: S });
        zero_tuple.push(CurveVector { x: R, y: X });

        let zero_vector_tuple = VectorTuple { values: zero_tuple };

        let mut tuples = Vec::new();
        tuples.push(zero_vector_tuple);
        tuples.push(one_vector_tuple);

        let proof = create_zkplmt(&tuples, if bits[i] { 1 } else { 0 }, s);
        proofs.push(proof);
        Xs.push(X);
    }
    return RangeProof {
        proofs: proofs,
        X: Xs,
        S: S,
    };
}

#[cfg(test)]
mod tests {
    use super::super::value_bound_signature::*;
    use super::*;

    use rand_core::OsRng;

    #[test]

    fn test_get_ith_power_of_2() {
        let four = [
            4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];

        let s_4 = Scalar::from_bits(four);
        assert_eq!(s_4, get_ith_power_of_2(2));

        let huge_number = [
            0u8, 0u8, 4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];

        let s_hn = Scalar::from_bits(huge_number);

        assert_eq!(s_hn, get_ith_power_of_2(18));
    }

    #[test]
    fn test_scalar_bits() {
        let one = [
            1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];
        let four = [
            4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];
        let five = [
            5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];
        let huge_number = [
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];

        let huge_result = [
            5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];

        let s_1 = Scalar::from_bits(one);
        let s_4 = Scalar::from_bits(four);
        let s_5 = Scalar::from_bits(five);
        let s_hn = Scalar::from_bits(huge_number);
        let s_hr = Scalar::from_bits(huge_result);

        assert_eq!(s_1 + s_4, s_5);

        assert_eq!(s_5 + s_hn, s_hr);

        let base_point = get_G();

        assert_eq!(s_1 * base_point, base_point);

        let value = 5;
        assert_eq!(value >> 1, 2);
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_range_proof() {
        let five = [
            5u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];

        let v = Scalar::from_bits(five);
        let G = get_G();

        let mut csprng: OsRng = OsRng::default();
        let s = Scalar::random(&mut csprng);
        let K = get_K();
        let V = v * s * K;

        let mut bases = Vec::new();
        let n = 8;
        let mut sum = Scalar::zero();
        for _ in 0..n - 1 {
            let r = Scalar::random(&mut csprng);
            sum = sum + r;
            let R = r * G;
            bases.push(R);
        }
        bases.push((-sum) * G);
        let range_proof = create_range_proof(v, s, &bases);
        assert!(verify_range_proof(V, &bases, n, &range_proof));

        //////////////////////////////////////////////////
        let huge_number = [
            31u8, 111u8, 4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
            0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
        ];

        let v = Scalar::from_bits(huge_number);

        let V = v * s * K;
        let mut bases = Vec::new();
        let n = 19;
        let mut sum = Scalar::zero();
        for _ in 0..n - 1 {
            let r = Scalar::random(&mut csprng);
            sum = sum + r;
            let R = r * G;
            bases.push(R);
        }
        bases.push((-sum) * G);

        let range_proof = create_range_proof(v, s, &bases);
        assert!(verify_range_proof(V, &bases, n, &range_proof));
    }
}
