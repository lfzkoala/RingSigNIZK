
use sha2::Sha256;
use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::edwards::EdwardsPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;
use sha2::Sha512;
use sha2::Digest;

use alloc::vec::*;
use curve25519_dalek::traits::MultiscalarMul;
use rand_core::RngCore;
use rand_core::OsRng;

pub fn get_random_curve_point() -> EdwardsPoint {
    let mut inputs = [0u8; 8];
    let mut csprng: OsRng = OsRng::default();

    csprng.fill_bytes(&mut inputs);
    hash_to_edwards(&inputs)
}

pub fn hash_to_edwards(input: &[u8]) -> EdwardsPoint {
    let mut bytes = vec![0u8; input.len()];
    copy(&mut bytes, &input);
    let mut hash = [0u8; 32];
    let mut source_hash = [0u8; 32];

    let mut hasher = Sha256::new();
    hasher.input(&bytes);
    source_hash.copy_from_slice(hasher.result().as_slice());

    loop {
        let mut hasher = Sha256::new();
        bytes.push(0);
        hasher.input(&bytes);
        hash.copy_from_slice(hasher.result().as_slice());

        //this is to avoid second preimage attacks.
        for i in 0..32 {
            hash[i] = hash[i] ^ source_hash[i];
        }

        let point = CompressedEdwardsY(hash);
        match point.decompress() {
            Some(ed_point) => {
                let group_point = Scalar::from(8u32) * ed_point;
                if !group_point.is_identity() {
                    return group_point;
                }
            }
            None => {}
        }
    }
}

//Sort the first parameter and do the same swaps in the second parameter
pub fn joint_quicksort<S: PartialOrd, T>(input: &mut [S], conjugate: &mut [T]) -> usize {
    assert_eq!(input.len(), conjugate.len());

    let mut index_of_first = 0;
    let mut stack = Vec::new();
    stack.push((0, input.len() - 1));
    while let Some(slice) = stack.pop() {
        let start = slice.0;
        let end = slice.1;
        let mut i = start;
        let mut j = end;
        let mut forward = true;
        while i < j {
            if input[i] > input[j] {
                if i == index_of_first {
                    index_of_first = j;
                } else if j == index_of_first {
                    index_of_first = i;
                }
                forward = !forward;
                input.swap(i, j);
                conjugate.swap(i, j);
            }
            if forward {
                i += 1;
            } else {
                j -= 1;
            }
        }

        //now the pivot is at i==j
        if i > 0 && start < i - 1 {
            stack.push((start, i - 1));
        }

        if end > i + 1 {
            stack.push((i + 1, end));
        }
    }

    return index_of_first;
}

//returns the index of the first element in the original slice in the final slice
pub fn shuffle<T>(input: &mut [T]) -> usize {
    let mut csprng: OsRng = OsRng::default();
    let mut tags = Vec::new();
    for _ in 0..input.len() {
        tags.push(csprng.next_u32());
    }

    return joint_quicksort(&mut tags, input);
}

pub fn copy<T: Copy>(target: &mut [T], source: &[T]) {
    assert!(target.len() >= source.len());
    for i in 0..source.len() {
        target[i] = source[i];
    }
}
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct CurveVector {
    pub x: EdwardsPoint,
    pub y: EdwardsPoint,
}

impl CurveVector {
    const size: usize = 2 * 32;
    pub fn fill_bytes(&self, buf: &mut [u8]) {
        let bytes = self.x.compress().to_bytes();
        copy(buf, &bytes);
        let bytes = self.y.compress().to_bytes();
        copy(&mut buf[32..], &bytes);
    }
}

#[macro_export]
macro_rules! proof_system {
    ($num_vectors:expr, $num_candidates:expr, $tuple_type_name:ident, $proof_name:ident) => {
        #[derive(Clone, Debug, PartialEq)]
        pub struct $tuple_type_name {
            pub values: [CurveVector; $num_vectors],
        }
        impl $tuple_type_name {
            const Tuple_Size: usize = $num_vectors * CurveVector::size;

            pub fn fill_bytes(&self, buf: &mut [u8]) {
                for i in 0..$num_vectors {
                    self.values[i].fill_bytes(&mut buf[CurveVector::size * i..]);
                }
            }
        }

        #[derive(Clone, Debug, PartialEq)]
        pub struct $proof_name {
            c: [Scalar; $num_candidates],
            d: [Scalar; $num_candidates],
        }

        impl $proof_name {
            const Size_of_Ls: usize = 32 * $num_candidates * $num_vectors * 2;
            const Size_of_Tuples: usize = $tuple_type_name::Tuple_Size * $num_candidates;
            #[allow(non_snake_case)]
            pub fn create_zkplmt(
                tuples: &[$tuple_type_name; $num_candidates],
                hidden_index: usize,
                secret: Scalar,
            ) -> $proof_name {
                let vectors_per_tuple = $num_vectors;

                let mut csprng: OsRng = OsRng::default();
                let r = Scalar::random(&mut csprng);
                let mut c = [Scalar::zero(); $num_candidates];
                let mut d = [Scalar::zero(); $num_candidates];
                let mut sum = Scalar::zero();
                let mut hash_input = [0u8; $proof_name::Size_of_Ls + $proof_name::Size_of_Tuples];
                for j in 0..tuples.len() {
                    assert!(tuples[j].values.len() == vectors_per_tuple);
                    if j != hidden_index {
                        c[j] = Scalar::random(&mut csprng);
                        d[j] = Scalar::random(&mut csprng);
                        for i in 0..vectors_per_tuple {
                            let L = c[j] * tuples[j].values[i].x + d[j] * tuples[j].values[i].y;
                            let bytes = L.compress().to_bytes();
                            let target_index = (j * vectors_per_tuple + i) * bytes.len();
                            copy(&mut hash_input[target_index..], &bytes);
                        }
                        sum += d[j];
                    }
                }
                for i in 0..vectors_per_tuple {
                    let L = r * tuples[hidden_index].values[i].x;
                    let bytes = L.compress().to_bytes();
                    let target_index = (hidden_index * vectors_per_tuple + i) * bytes.len();
                    copy(&mut hash_input[target_index..], &bytes);
                }

                for i in 0..tuples.len() {
                    tuples[i].fill_bytes(
                        &mut hash_input
                            [$proof_name::Size_of_Ls + i * $tuple_type_name::Tuple_Size..],
                    );
                }
                let hash_scalar = Scalar::hash_from_bytes::<Sha512>(&hash_input);
                d[hidden_index] = hash_scalar - sum;
                c[hidden_index] = r - d[hidden_index] * secret;

                $proof_name { c: c, d: d }
            }

            #[allow(non_snake_case)]
            pub fn verify_zkplmt(&self, tuples: &[$tuple_type_name; $num_candidates]) -> bool {
                let vectors_per_tuple = tuples[0].values.len();
                let mut mult_sc_vec = [Scalar::zero(); 2];
                let mut mult_ed_vec = [EdwardsPoint::default(); 2];
                if vectors_per_tuple == 0 {
                    return false;
                }
                let c = &self.c;
                let d = &self.d;
                let vectors_per_tuple = tuples[0].values.len();

                let mut sum = Scalar::zero();
                let mut hash_input = [0u8; $proof_name::Size_of_Ls + $proof_name::Size_of_Tuples];

                for j in 0..tuples.len() {
                    if tuples[j].values.len() != vectors_per_tuple {
                        return false;
                    }
                    for i in 0..vectors_per_tuple {
                        mult_ed_vec[0] = tuples[j].values[i].x;
                        mult_ed_vec[1] = tuples[j].values[i].y;
                        mult_sc_vec[0] = c[j];
                        mult_sc_vec[1] = d[j];

                        let L = EdwardsPoint::multiscalar_mul(&mult_sc_vec, &mult_ed_vec);
                        let bytes = L.compress().to_bytes();
                        let target_index = (j * vectors_per_tuple + i) * bytes.len();
                        copy(&mut hash_input[target_index..], &bytes);
                    }
                    sum += d[j];
                }

                for i in 0..tuples.len() {
                    tuples[i].fill_bytes(
                        &mut hash_input
                            [$proof_name::Size_of_Ls + i * $tuple_type_name::Tuple_Size..],
                    );
                }
                let hash_scalar = Scalar::hash_from_bytes::<Sha512>(&hash_input);
                if hash_scalar.eq(&sum) {
                    return true;
                } else {
                    return false;
                }
            }

            pub fn create_zkplmt_shuffle(
                tuples: &mut [$tuple_type_name; $num_candidates],
                secret: Scalar,
            ) -> $proof_name {
                let hidden_index = shuffle(tuples);
                return $proof_name::create_zkplmt(tuples, hidden_index, secret);
            }
        }
    };
}

proof_system!(3, 5, XTuple, XProof);
proof_system!(5, 5, YTuple, YProof);

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::scalar::Scalar;
    use rand_core::OsRng;
    #[test]
    fn test_zkplmt() {
        let mut csprng: OsRng = OsRng::default();
        let secret = Scalar::random(&mut csprng);
        let base_1 = get_random_curve_point();
        let base_2 = get_random_curve_point();
        let base_3 = get_random_curve_point();

        let per_1 = secret * base_1;
        let per_2 = secret * base_2;
        let per_3 = secret * base_3;

        let curve_points_1: [CurveVector; 3] = [
            CurveVector {
                x: base_1,
                y: per_1,
            },
            CurveVector {
                x: base_2,
                y: per_2,
            },
            CurveVector {
                x: base_3,
                y: per_3,
            },
        ];

        let tuple_1 = XTuple {
            values: curve_points_1,
        };

        let mut tuples = [
            tuple_1.clone(),
            tuple_1.clone(),
            tuple_1.clone(),
            tuple_1.clone(),
            tuple_1,
        ];

        for i in 1..5 {
            let base_1 = get_random_curve_point();
            let base_2 = get_random_curve_point();
            let base_3 = get_random_curve_point();

            let per_1 = get_random_curve_point();
            let per_2 = get_random_curve_point();
            let per_3 = get_random_curve_point();

            let curve_points_1: [CurveVector; 3] = [
                CurveVector {
                    x: base_1,
                    y: per_1,
                },
                CurveVector {
                    x: base_2,
                    y: per_2,
                },
                CurveVector {
                    x: base_3,
                    y: per_3,
                },
            ];

            let tuple_2 = XTuple {
                values: curve_points_1,
            };

            tuples[i] = tuple_2;
        }

        let signature = XProof::create_zkplmt_shuffle(&mut tuples, secret);
        let result = signature.verify_zkplmt(&tuples);
        assert_eq!(result, true);
    }

    // #[test]
    // fn test_zkplmt_single() {
    //     let mut csprng: OsRng = OsRng::new().unwrap();
    //     let secret = Scalar::random(&mut csprng);
    //     let base_1 = get_random_curve_point();
    //     let base_2 = get_random_curve_point();
    //     let base_3 = get_random_curve_point();
    //     let base_4 = get_random_curve_point();
    //     let base_5 = get_random_curve_point();

    //     let per_1 = secret * base_1;
    //     let per_2 = secret * base_2;
    //     let per_3 = secret * base_3;
    //     let per_4 = secret * base_4;
    //     let per_5 = secret * base_5;

    //     let curve_points_1 = vec![
    //         CurveVector {
    //             x: base_1,
    //             y: per_1,
    //         },
    //         CurveVector {
    //             x: base_2,
    //             y: per_2,
    //         },
    //         CurveVector {
    //             x: base_3,
    //             y: per_3,
    //         },
    //         CurveVector {
    //             x: base_4,
    //             y: per_4,
    //         },
    //         CurveVector {
    //             x: base_5,
    //             y: per_5,
    //         },
    //     ];

    //     let tuple_1 = VectorTuple {
    //         values: curve_points_1,
    //     };

    //     let mut tuples = vec![tuple_1];

    //     let signature = create_zkplmt(&mut tuples, 0, secret);
    //     let result = verify_zkplmt(&tuples, &signature);
    //     assert_eq!(result, true);
    // }
    // #[test]
    // fn test_zkplmt_fail() {
    //     let mut csprng: OsRng = OsRng::new().unwrap();
    //     let secret = Scalar::random(&mut csprng);
    //     let base_1 = get_random_curve_point();
    //     let base_2 = get_random_curve_point();
    //     let base_3 = get_random_curve_point();

    //     let per_1 = secret * base_1;
    //     let per_2 = secret * base_2;
    //     let per_3 = secret * base_3;

    //     let curve_points_1 = vec![
    //         CurveVector {
    //             x: base_1,
    //             y: per_1,
    //         },
    //         CurveVector {
    //             x: base_2,
    //             y: per_2,
    //         },
    //         CurveVector {
    //             x: base_3,
    //             y: per_3,
    //         },
    //     ];

    //     let tuple_1 = VectorTuple {
    //         values: curve_points_1,
    //     };

    //     let base_1 = get_random_curve_point();
    //     let base_2 = get_random_curve_point();
    //     let base_3 = get_random_curve_point();

    //     let per_1 = get_random_curve_point();
    //     let per_2 = get_random_curve_point();
    //     let per_3 = get_random_curve_point();

    //     let curve_points_1 = vec![
    //         CurveVector {
    //             x: base_1,
    //             y: per_1,
    //         },
    //         CurveVector {
    //             x: base_2,
    //             y: per_2,
    //         },
    //         CurveVector {
    //             x: base_3,
    //             y: per_3,
    //         },
    //     ];

    //     let tuple_2 = VectorTuple {
    //         values: curve_points_1,
    //     };

    //     let base_1 = get_random_curve_point();
    //     let base_2 = get_random_curve_point();
    //     let base_3 = get_random_curve_point();

    //     let per_1 = get_random_curve_point();
    //     let per_2 = get_random_curve_point();
    //     let per_3 = get_random_curve_point();

    //     let curve_points_1 = vec![
    //         CurveVector {
    //             x: base_1,
    //             y: per_1,
    //         },
    //         CurveVector {
    //             x: base_2,
    //             y: per_2,
    //         },
    //         CurveVector {
    //             x: base_3,
    //             y: per_3,
    //         },
    //     ];

    //     let tuple_3 = VectorTuple {
    //         values: curve_points_1,
    //     };

    //     let tuples = vec![tuple_2, tuple_1, tuple_3];

    //     let signature = create_zkplmt(&tuples, 2usize, secret);
    //     let result = verify_zkplmt(&tuples, &signature);
    //     assert_eq!(result, false);
    // }

    #[test]
    fn test_joint_quicksort() {
        let mut array = [1, 5, 2, 3, 1, 5];
        let mut conj = [0, 1, 2, 3, 4, 5];
        joint_quicksort(&mut array, &mut conj);
        assert_eq!(array, [1, 1, 2, 3, 5, 5]);
    }

    #[test]
    fn test_joint_quicksort_2() {
        let mut array = [5, 1, 4, 3, 2];
        let mut conj = [0, 1, 2, 3, 4];
        let index_of_first = joint_quicksort(&mut array, &mut conj);
        assert_eq!(array, [1, 2, 3, 4, 5]);
        assert_eq!(conj, [1, 4, 3, 2, 0]);
        assert_eq!(index_of_first, 4);
    }
}
