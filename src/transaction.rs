use super::core::*;
use super::*;
use alloc::vec::*;
use curve25519_dalek::edwards::*;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use crate::bulletproofs::Bases;
use bulletproofs::*;
use sha2::Sha256;
use sha2::Digest;
use rand_core::RngCore;
use rand_core::OsRng;
use serde::*;
use bincode;


#[derive(Copy, Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TransactionOutput {
    pub commitment: EdwardsPoint,
    pub public_key: (EdwardsPoint, EdwardsPoint),
}

impl TransactionOutput {
    pub fn new(
        commitment: EdwardsPoint,
        public_key: (EdwardsPoint, EdwardsPoint),
    ) -> TransactionOutput {
        TransactionOutput {
            commitment,
            public_key,
        }
    }
}





#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TransactionInputSet {
    pub components: Vec<TransactionOutput>,
}



impl TransactionInputSet {
    pub fn new(components: Vec<TransactionOutput>) -> TransactionInputSet {
        TransactionInputSet { components }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct AP_Declaration_Of_Public_key {
    pi_1: Proof,
    pi_2: Proof,
    Z: EdwardsPoint,
    X: EdwardsPoint,
    Y: EdwardsPoint,
    Qs: EdwardsPoint,
    Qsz: EdwardsPoint,
}


#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Transaction {
    input_condidates: Vec<TransactionInputSet>,
    outputs: Vec<TransactionOutput>,
    key_images: Vec<EdwardsPoint>,
    Z: EdwardsPoint,
    pi: Proof,
    alpha: Proof,
    AP_public_key: EdwardsPoint,
    S_vector: CurveVector,
    AP_Declaration_Of_Public_key: AP_Declaration_Of_Public_key,
    AP_Declaration_Of_Value: Vec<AP_Declaration_Of_Value>,
    range_proof: BulletRangeProof,
    spendingLimitProof: SpendingLimitProof,
}

impl Transaction {
    pub fn new(
        input_condidates: Vec<TransactionInputSet>,
        pAP_key: EdwardsPoint,
        outputs: Vec<TransactionOutput>,
        key_images: Vec<EdwardsPoint>,
        Z: EdwardsPoint,
        pi: Proof,
        alpha: Proof,
        AP_public_key: EdwardsPoint,
        S_vector: CurveVector,
        AP_Declaration_Of_Public_key: AP_Declaration_Of_Public_key,
        AP_Declaration_Of_Value: Vec<AP_Declaration_Of_Value>,
        range_proof: BulletRangeProof,
        spendingLimitProof: SpendingLimitProof,
    ) -> Transaction {
        Transaction {
            input_condidates,
            outputs,
            key_images,
            Z,
            pi,
            alpha,
            AP_public_key,
            S_vector,
            AP_Declaration_Of_Public_key,
            AP_Declaration_Of_Value,
            range_proof,
            spendingLimitProof,
        }
    }
}

fn verify_AP_declaration_of_public_key(
    dec: &AP_Declaration_Of_Public_key,
    S: EdwardsPoint,
    Sp: EdwardsPoint,
    Q: EdwardsPoint,
) -> bool {
    let G = get_G();
    let Z = dec.Z;
    let X = dec.X;
    let Y = dec.Y;
    let Qs = dec.Qs;
    let Qsz = dec.Qsz;

    let gs = CurveVector { x: G, y: S };

    let xy = CurveVector { x: X, y: Y };

    let qqs = CurveVector { x: Q, y: Qs };

    let tuple = VectorTuple {
        values: vec![gs, xy, qqs],
    };

    if !verify_zkplmt(&vec![tuple], &dec.pi_1) {
        return false;
    }

    let gz = CurveVector { x: G, y: Z };

    let qsqsz = CurveVector { x: Qs, y: Qsz };

    let tuple_2 = VectorTuple {
        values: vec![gz, qsqsz],
    };

    if !verify_zkplmt(&vec![tuple_2], &dec.pi_2) {
        return false;
    }

    return true;
}
//TODO complete it
fn generate_AP_declaration_of_public_key(
    p: Scalar,
    s: Scalar,
    S: EdwardsPoint,
    Sp: EdwardsPoint,
    Q: EdwardsPoint,
) -> AP_Declaration_Of_Public_key {
    let G = get_G();
    let P = p * G;
    let mut csprng: OsRng = OsRng::default();
    let z = Scalar::random(&mut csprng);

    let Z = z * G;
    let X = z * Q + P;
    let Y = s * X;
    let Qs = s * Q;
    let Qsz = z * Qs;

    let gs = CurveVector { x: G, y: S };

    let xy = CurveVector { x: X, y: Y };

    let qqs = CurveVector { x: Q, y: Qs };

    let tuple = VectorTuple {
        values: vec![gs, xy, qqs],
    };

    let pi_1 = create_zkplmt(&vec![tuple], 0, s);

    let gz = CurveVector { x: G, y: Z };

    let qsqsz = CurveVector { x: Qs, y: Qsz };

    let tuple_2 = VectorTuple {
        values: vec![gz, qsqsz],
    };

    let pi_2 = create_zkplmt(&vec![tuple_2], 0, z);

    return AP_Declaration_Of_Public_key {
        pi_1,
        pi_2,
        Z,
        X,
        Y,
        Qs,
        Qsz,
    };
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[allow(non_snake_case)]
pub struct AP_Declaration_Of_Value {
    W: EdwardsPoint,
    Wc: EdwardsPoint,
    Vc: EdwardsPoint,
    Lcv: EdwardsPoint,
    Rc: EdwardsPoint,
    alpha_1: Proof,
    sigma_1: Proof,
    sigma_2: Proof,
}

fn verify_AP_declaration_of_value(
    V: EdwardsPoint,
    dec: AP_Declaration_Of_Value,
    G: &EdwardsPoint,
    L: &EdwardsPoint,
    Q: &EdwardsPoint,
) -> bool {
    let W = dec.W;
    let Vc = dec.Vc;
    let Wc = dec.Wc;
    let Lcv = dec.Lcv;
    let Rc = dec.Rc;
    let alpha_1 = dec.alpha_1;
    let sigma_1 = dec.sigma_1;
    let sigma_2 = dec.sigma_2;

    let tuple = VectorTuple {
        values: vec![CurveVector { x: V, y: Vc }, CurveVector { x: W, y: Wc }],
    };

    let tuple_2 = VectorTuple {
        values: vec![CurveVector { x: *L, y: Lcv }],
    };

    let tuple_3 = VectorTuple {
        values: vec![CurveVector { x: *G, y: Rc }, CurveVector { x: *Q, y: Wc }],
    };

    return verify_zkplmt(&vec![tuple], &sigma_1)
        && verify_zkplmt(&vec![tuple_2], &alpha_1)
        && verify_zkplmt(&vec![tuple_3], &sigma_2);
}

#[allow(non_snake_case)]
fn generate_AP_declaration_of_value(
    r: Scalar,
    v: Scalar,
    G: &EdwardsPoint,
    L: &EdwardsPoint,
    Q: &EdwardsPoint,
) -> AP_Declaration_Of_Value {
    let W = r * Q;
    let V = EdwardsPoint::multiscalar_mul(vec![r, v], vec![G, L]);
    let mut csprng: OsRng = OsRng::default();
    let c = Scalar::random(&mut csprng);
    let Vc = c * V;
    let Wc = c * W;

    let tuple = VectorTuple {
        values: vec![CurveVector { x: V, y: Vc }, CurveVector { x: W, y: Wc }],
    };

    let sigma_1 = create_zkplmt(&vec![tuple], 0, c);

    let Lcv = v * c * L;
    let tuple_2 = VectorTuple {
        values: vec![CurveVector { x: *L, y: Lcv }],
    };

    let alpha_1 = create_zkplmt(&vec![tuple_2], 0, c * v);
    let Rc = Vc - Lcv;

    let tuple_3 = VectorTuple {
        values: vec![CurveVector { x: *G, y: Rc }, CurveVector { x: *Q, y: Wc }],
    };

    let sigma_2 = create_zkplmt(&vec![tuple_3], 0, r * c);

    return AP_Declaration_Of_Value {
        W,
        Wc,
        Vc,
        Lcv,
        Rc,
        alpha_1,
        sigma_1,
        sigma_2,
    };
}
fn get_edward_hash(C: &EdwardsPoint, D: &EdwardsPoint) -> EdwardsPoint {
    let mut bytes = [0u8; 64];
    copy(&mut bytes[0..32], C.compress().as_bytes());
    copy(&mut bytes[32..64], D.compress().as_bytes());
    let hash = hash_to_edwards(&bytes);
    return hash;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SpendingLimitProof {
    sources: Vec<SpendingLimitProof>,
    totalSpendingCommitment: EdwardsPoint,
    uniqueMarker: EdwardsPoint,
    C_: EdwardsPoint,
    D_: EdwardsPoint,
    alpha_2: Option<Proof>,
    gamma: Option<Proof>,
}

fn verify_KYC_proof(
    proof: &SpendingLimitProof,
    A_: EdwardsPoint,
    B_: EdwardsPoint,
    Vt: &[EdwardsPoint],
    S: &EdwardsPoint,
    Sp: &EdwardsPoint,
) -> bool {
    let hashes: Vec<EdwardsPoint> = proof
        .sources
        .iter()
        .map(|source| get_edward_hash(&source.C_, &source.D_))
        .collect();
    let J = proof.uniqueMarker;

    let a_tuples: Vec<VectorTuple> = proof
        .sources
        .iter()
        .map(|source| VectorTuple {
            values: vec![CurveVector {
                x: source.C_,
                y: proof.C_,
            }],
        })
        .collect();
    match &proof.alpha_2 {
        Some(al) => {
            if !verify_zkplmt(&a_tuples, &al) {
                return false;
            }
        }
        None => {}
    }

    let V_ = Vt[0];
    let sum = Vt.iter().fold(EdwardsPoint::default(), |X, Y| X + Y);
    let CC = proof.totalSpendingCommitment;
    let tuples: Vec<VectorTuple> = proof
        .sources
        .iter()
        .zip(hashes.iter())
        .map(|(source, hash)| {
            let E_ = CC - source.totalSpendingCommitment + V_ - sum;
            VectorTuple {
                values: vec![
                    CurveVector { x: *S, y: *Sp },
                    CurveVector {
                        x: source.C_,
                        y: source.D_,
                    },
                    CurveVector {
                        x: proof.C_,
                        y: proof.D_,
                    },
                    CurveVector {
                        x: source.D_,
                        y: E_,
                    },
                    CurveVector { x: A_, y: B_ },
                    CurveVector { x: *hash, y: J },
                ],
            }
        })
        .collect();
    match &proof.gamma {
        Some(gam) => {
            if !verify_zkplmt(&tuples, &gam) {
                return false;
            }
        }
        None => {}
    }

    return true;
}
pub fn generate_starting_KYC_proof(p: Scalar) -> SpendingLimitProof {
    let G = get_G();

    return SpendingLimitProof {
        sources: vec![],
        totalSpendingCommitment: EdwardsPoint::default(),
        uniqueMarker: EdwardsPoint::default(),
        C_: G,
        D_: p * G,
        alpha_2: None,
        gamma: None,
    };
}

pub struct KYCSpendingLimitSource{
    C: EdwardsPoint,
    D: EdwardsPoint,
    totalSpendingCommitment: EdwardsPoint
}

fn generate_KYC_proof(
    sources: Vec<SpendingLimitProof>,
    A_: EdwardsPoint,
    B_: EdwardsPoint,
    Vt: &[EdwardsPoint],
    S: &EdwardsPoint,
    Sp: &EdwardsPoint,
    k: usize,
    p: Scalar,
) -> SpendingLimitProof {
    let C = sources[k].C_;
    let D = sources[k].D_;
    let E = p * D;
    let hashes: Vec<EdwardsPoint> = sources
        .iter()
        .map(|source| get_edward_hash(&source.C_, &source.D_))
        .collect();
    let hash = hashes[k];
    let J = p * hash;
    let mut csprng: OsRng = OsRng::default();
    let x = Scalar::random(&mut csprng);
    let C_ = x * C;
    let D_ = x * D;
    let a_tuples: Vec<VectorTuple> = sources
        .iter()
        .map(|source| VectorTuple {
            values: vec![CurveVector {
                x: source.C_,
                y: C_,
            }],
        })
        .collect();
    let alpha_2 = create_zkplmt(&a_tuples, k, x);
    let V_ = Vt[0];
    let sum = Vt.iter().fold(EdwardsPoint::default(), |X, Y| X + Y);
    let CC = sources[k].totalSpendingCommitment + E - V_ + sum;

    let tuples: Vec<VectorTuple> = sources
        .iter()
        .zip(hashes.iter())
        .map(|(source, hash)| {
            let E_ = CC - source.totalSpendingCommitment + V_ - sum;
            VectorTuple {
                values: vec![
                    CurveVector { x: *S, y: *Sp },
                    CurveVector {
                        x: source.C_,
                        y: source.D_,
                    },
                    CurveVector { x: C_, y: D_ },
                    CurveVector {
                        x: source.D_,
                        y: E_,
                    },
                    CurveVector { x: A_, y: B_ },
                    CurveVector { x: *hash, y: J },
                ],
            }
        })
        .collect();

    let gamma = create_zkplmt(&tuples, k, p);
    let result = SpendingLimitProof {
        sources: sources,
        totalSpendingCommitment: CC,
        uniqueMarker: J,
        C_: C_,
        D_: D_,
        alpha_2: Some(alpha_2),
        gamma: Some(gamma),
    };

    return result;
}

#[allow(non_snake_case)]
pub fn create_transaction(
    inputs: Vec<TransactionInputSet>,
    ri: Vec<Scalar>,
    vo: Vec<u64>,
    output_pub_keys: Vec<(EdwardsPoint, EdwardsPoint)>,
    p: Scalar,
    AP_public_key: EdwardsPoint,
    kyc_sources: Vec<SpendingLimitProof>,
    bases: Bases,
) -> Transaction {
    let G = get_G();
    let mut csprng: OsRng = OsRng::default();
    let z = Scalar::random(&mut csprng);
    let s = Scalar::random(&mut csprng);
    let Z = z * G;
    let S = s * G;
    let Sp = p * S;
    let Q = AP_public_key;

    let S_vector = CurveVector { x: S, y: Sp };

    let mut ro: Vec<Scalar> = (0..vo.len()).map(|_| Scalar::random(&mut csprng)).collect();

    let diff =
        ri.iter().fold(Scalar::zero(), |x, y| x + y) - ro.iter().fold(Scalar::zero(), |x, y| x + y);
    ro[0] += diff - z * p;

    let sum_ri = ri.iter().fold(Scalar::zero(), |x, y| x + y);
    let sum_ro = ro.iter().fold(Scalar::zero(), |x, y| x + y);

    assert_eq!(sum_ri, sum_ro + p * z);

    let alpha_tuple = VectorTuple {
        values: vec![CurveVector { x: G, y: Z }],
    };

    let alpha = create_zkplmt(&[alpha_tuple], 0, z);

    let H: Vec<Vec<EdwardsPoint>> = inputs
        .iter()
        .map(|input| {
            let list: Vec<EdwardsPoint> = input
                .components
                .iter()
                .map(|c| {
                    let (A, B) = c.public_key;
                    let Ac = A.compress();
                    let Bc = B.compress();
                    let A_bytes = Ac.as_bytes();
                    let B_bytes = Bc.as_bytes();
                    let mut bytes = [0u8; 64];
                    copy(&mut bytes, A_bytes);
                    copy(&mut bytes[32..], B_bytes);
                    hash_to_edwards(&bytes)
                })
                .collect();
            list
        })
        .collect();

    let key_images: Vec<EdwardsPoint> = H[0].iter().map(|hash| p * hash).collect();
    //assert_eq!(get_G(), get_L());
    let outputs_comms: Vec<EdwardsPoint> = ro
        .iter()
        .zip(vo.iter())
        .map(|(r, v)| {
            EdwardsPoint::multiscalar_mul(vec![*r, Scalar::from(*v)], vec![&get_G(), &get_L()])
        })
        .collect();

    let sum_output = outputs_comms
        .iter()
        .fold(EdwardsPoint::default(), |X, Y| X + Y);

    let s_input = inputs[0]
        .components
        .iter()
        .map(|x| x.commitment)
        .fold(EdwardsPoint::default(), |X, Y| X + Y);
    assert_eq!(s_input - sum_output, p * Z);

    let tuples: Vec<VectorTuple> = inputs
        .iter()
        .zip(H.iter())
        // .zip(kyc_set.iter())
        .map(|(input, hashes)| {
            let components = &input.components;
            let mut curve_vectors: Vec<CurveVector> = components
                .iter()
                .map(|c| CurveVector {
                    x: c.public_key.0,
                    y: c.public_key.1,
                })
                .collect();
            let mut hash_vectors = hashes
                .iter()
                .zip(key_images.iter())
                .map({ |(hash, I)| CurveVector { x: *hash, y: *I } })
                .collect();
            curve_vectors.append(&mut hash_vectors);

            curve_vectors.push(S_vector);

            let sum_input = input
                .components
                .iter()
                .map({ |c| c.commitment })
                .fold(EdwardsPoint::default(), |X, Y| X + Y);
            let sum_diff = sum_input - sum_output;

            curve_vectors.push(CurveVector { x: Z, y: sum_diff });
            VectorTuple {
                values: curve_vectors,
            }
        })
        .collect();

    let mut indexes: Vec<usize> = (0..tuples.len()).map(|x| x).collect();
    let s_index = shuffle(&mut indexes);

    let shuffle_tuple: Vec<VectorTuple> = indexes.iter().map(|j| tuples[*j].clone()).collect();

    let pi = create_zkplmt(&shuffle_tuple, s_index, p);
    let inputs_shuffle: Vec<TransactionInputSet> =
        indexes.iter().map(|j| inputs[*j].clone()).collect();

    // let kyc_set_shuffle: Vec<(EdwardsPoint, EdwardsPoint)> =
    //     indexes.iter().map(|j| kyc_set[*j]).collect();

    let outputs: Vec<TransactionOutput> = outputs_comms
        .iter()
        .zip(output_pub_keys.iter())
        .map(|(comm, key)| TransactionOutput {
            commitment: *comm,
            public_key: *key,
        })
        .collect();

    let AP_Declaration_Of_Public_key = generate_AP_declaration_of_public_key(p, s, S, Sp, Q);
    let mut AP_Declaration_Of_Value = Vec::new();

    let L = get_L();
    let Q = AP_public_key;
    for i in 0..vo.len() {
        let r = ro[i];
        let v = Scalar::from(vo[i]);
        let proof = generate_AP_declaration_of_value(r, v, &G, &L, &Q);
        AP_Declaration_Of_Value.push(proof);
    }
    let mut kyc_sources = kyc_sources.clone();
    let k = shuffle(&mut kyc_sources);
    let range_proof = bullet_range_proof(&ro, &vo, &bases);
    let spendingLimitProof = generate_KYC_proof(
        kyc_sources,
        output_pub_keys[0].0,
        output_pub_keys[0].1,
        &outputs_comms,
        &S,
        &Sp,
        k,
        p,
    );

    Transaction {
        input_condidates: inputs_shuffle,
        outputs: outputs,
        key_images: key_images,
        Z: Z,
        pi: pi,
        alpha: alpha,
        AP_public_key: AP_public_key,
        S_vector: S_vector,
        AP_Declaration_Of_Public_key: AP_Declaration_Of_Public_key,
        AP_Declaration_Of_Value: AP_Declaration_Of_Value,
        range_proof: range_proof,
        spendingLimitProof: spendingLimitProof,
    }
}

#[allow(non_snake_case)]
pub fn verify_transaction(transaction: &Transaction, bases: Bases) -> bool {
    let G = get_G();
    let alpha_tuple = VectorTuple {
        values: vec![CurveVector {
            x: G,
            y: transaction.Z,
        }],
    };
    if !verify_zkplmt(&[alpha_tuple], &transaction.alpha) {
        return false;
    }

    let H: Vec<Vec<EdwardsPoint>> = transaction
        .input_condidates
        .iter()
        .map(|input| {
            let list: Vec<EdwardsPoint> = input
                .components
                .iter()
                .map(|c| {
                    let (A, B) = c.public_key;
                    let Ac = A.compress();
                    let Bc = B.compress();
                    let A_bytes = Ac.as_bytes();
                    let B_bytes = Bc.as_bytes();
                    let mut bytes = [0u8; 64];
                    copy(&mut bytes, A_bytes);
                    copy(&mut bytes[32..], B_bytes);
                    hash_to_edwards(&bytes)
                })
                .collect();
            list
        })
        .collect();

    let sum_output = transaction
        .outputs
        .iter()
        .map(|output| output.commitment)
        .fold(EdwardsPoint::default(), |X, Y| X + Y);

    let key_images = &transaction.key_images;
    // let kyc_set = &transaction.kyc_set;
    let Z = transaction.Z;

    let tuples: Vec<VectorTuple> = transaction
        .input_condidates
        .iter()
        .zip(H.iter())
        // .zip(kyc_set.iter())
        .map(|(input, hashes)| {
            let components = &input.components;
            let mut curve_vectors: Vec<CurveVector> = components
                .iter()
                .map(|c| CurveVector {
                    x: c.public_key.0,
                    y: c.public_key.1,
                })
                .collect();
            let mut hash_vectors = hashes
                .iter()
                .zip(key_images.iter())
                .map({ |(hash, I)| CurveVector { x: *hash, y: *I } })
                .collect();
            curve_vectors.append(&mut hash_vectors);

            curve_vectors.push(transaction.S_vector);

            let sum_input = input
                .components
                .iter()
                .map({ |c| c.commitment })
                .fold(EdwardsPoint::default(), |X, Y| X + Y);
            let sum_diff = sum_input - sum_output;

            curve_vectors.push(CurveVector { x: Z, y: sum_diff });
            VectorTuple {
                values: curve_vectors,
            }
        })
        .collect();
    if !verify_AP_declaration_of_public_key(
        &transaction.AP_Declaration_Of_Public_key,
        transaction.S_vector.x,
        transaction.S_vector.y,
        transaction.AP_public_key,
    ) {
        return false;
    }

    let L = get_L();

    for (output, dec) in transaction
        .outputs
        .iter()
        .zip(transaction.AP_Declaration_Of_Value.iter())
    {
        let V = output.commitment;
        if !verify_AP_declaration_of_value(V, dec.clone(), &G, &L, &transaction.AP_public_key) {
            return false;
        }
    }
    let mut outComms = vec![];
    for i in 0..transaction.outputs.len() {
        let com = transaction.outputs[i].commitment;
        outComms.push(com);
        let rcom = transaction.range_proof.V[i];
        //assert_eq!(com, rcom);
        if !com.eq(&rcom) {
            return false;
        }
    }

    if !bullet_range_verify(&transaction.range_proof, bases) {
        return false;
    }
    if !verify_KYC_proof(
        &transaction.spendingLimitProof,
        transaction.outputs[0].public_key.0,
        transaction.outputs[0].public_key.1,
        &outComms,
        &transaction.S_vector.x,
        &transaction.S_vector.y,
    ) {
        return false;
    }

    return verify_zkplmt(&tuples, &transaction.pi);
}

#[cfg(test)]
mod tests {
    use super::super::value_bound_signature::*;
    use super::*;

    use rand_core::RngCore;
    use rand_core::OsRng;

    #[allow(non_snake_case)]
    #[test]

    fn test_transaction() {
        let ginit = get_G();
        let G = get_G();
        let L = get_L();
        let mut csprng: OsRng = OsRng::default();
        let p = Scalar::random(&mut csprng);

        let n = 5;
        let ri: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut csprng)).collect();

        let vi: Vec<u64> = (0..n).map(|_| csprng.next_u32() as u64).collect();
        assert_eq!(vi.len(), n);
        let mut vo: Vec<u64> = vi.iter().map(|v| v - 2u64).collect();
        vo[0] = vi[0] + (2u64 * (n - 1) as u64);

        let sum_vi = vi.iter().fold(0, |x, y| x + y);
        let sum_vo = vo.iter().fold(0, |x, y| x + y);

        assert_eq!(sum_vi, sum_vo);

        let mut input_bases = Vec::new();
        for _ in 0..n {
            input_bases.push(get_hash(&ginit, &ginit) * ginit);
        }

        let input_components: Vec<TransactionOutput> = input_bases
            .iter()
            .zip(ri.iter().zip(vi.iter()))
            .map(|(base, (r, v))| {
                let key = p * base;
                let pub_key = (*base, key);
                TransactionOutput {
                    public_key: pub_key,
                    commitment: r * G + Scalar::from(*v) * L,
                }
            })
            .collect();

        let mut inputs = Vec::new();
        inputs.push(TransactionInputSet {
            components: input_components,
        });
        let m = 5;
        for _ in 0..(m - 1) {
            let input_components: Vec<TransactionOutput> = input_bases
                .iter()
                .zip(ri.iter().zip(vi.iter()))
                .map(|(_, (_, _))| {
                    let pub_key = (get_random_curve_point(), get_random_curve_point());
                    TransactionOutput {
                        public_key: pub_key,
                        commitment: get_random_curve_point(),
                    }
                })
                .collect();

            inputs.push(TransactionInputSet {
                components: input_components,
            });
        }

        let mut output_pub_keys: Vec<(EdwardsPoint, EdwardsPoint)> = input_bases
            .iter()
            .map(|base| (get_random_curve_point(), get_random_curve_point()))
            .collect();
        let A_ = get_random_curve_point();
        let B_ = p * A_;
        output_pub_keys[0] = (A_, B_);

        let AP_public_key = get_random_curve_point();

        let input_sum = vi.iter().fold(0, |x, y| x + y);
        let output_sum = vo.iter().fold(0, |x, y| x + y);

        assert_eq!(input_sum, output_sum);

        let bases = Bases::new(get_L(), get_G(), 20);

        let mut kyc_sources = vec![generate_starting_KYC_proof(p)];
        for i in 0..5 {
            let t = Scalar::random(&mut csprng);
            kyc_sources.push(generate_starting_KYC_proof(t));
        }
        let transaction = create_transaction(
            inputs,
            ri,
            vo,
            output_pub_keys,
            p,
            AP_public_key,
            kyc_sources,
            bases.clone(),
        );
        assert!(verify_transaction(&transaction, bases));
    }

    fn test_serialization() {
        let ginit = get_G();
        let G = get_G();
        let L = get_L();
        let mut csprng: OsRng = OsRng::default();
        let p = Scalar::random(&mut csprng);

        let n = 5;
        let ri: Vec<Scalar> = (0..n).map(|_| Scalar::random(&mut csprng)).collect();

        let vi: Vec<u64> = (0..n).map(|_| csprng.next_u32() as u64).collect();
        assert_eq!(vi.len(), n);
        let mut vo: Vec<u64> = vi.iter().map(|v| v - 2u64).collect();
        vo[0] = vi[0] + (2u64 * (n - 1) as u64);

        let sum_vi = vi.iter().fold(0, |x, y| x + y);
        let sum_vo = vo.iter().fold(0, |x, y| x + y);

        assert_eq!(sum_vi, sum_vo);

        let mut input_bases = Vec::new();
        for _ in 0..n {
            input_bases.push(get_hash(&ginit, &ginit) * ginit);
        }

        let input_components: Vec<TransactionOutput> = input_bases
            .iter()
            .zip(ri.iter().zip(vi.iter()))
            .map(|(base, (r, v))| {
                let key = p * base;
                let pub_key = (*base, key);
                TransactionOutput {
                    public_key: pub_key,
                    commitment: r * G + Scalar::from(*v) * L,
                }
            })
            .collect();

        let mut inputs = Vec::new();
        inputs.push(TransactionInputSet {
            components: input_components,
        });
        let m = 5;
        for _ in 0..(m - 1) {
            let input_components: Vec<TransactionOutput> = input_bases
                .iter()
                .zip(ri.iter().zip(vi.iter()))
                .map(|(_, (_, _))| {
                    let pub_key = (get_random_curve_point(), get_random_curve_point());
                    TransactionOutput {
                        public_key: pub_key,
                        commitment: get_random_curve_point(),
                    }
                })
                .collect();

            inputs.push(TransactionInputSet {
                components: input_components,
            });
        }

        let mut output_pub_keys: Vec<(EdwardsPoint, EdwardsPoint)> = input_bases
            .iter()
            .map(|base| (get_random_curve_point(), get_random_curve_point()))
            .collect();
        let A_ = get_random_curve_point();
        let B_ = p * A_;
        output_pub_keys[0] = (A_, B_);

        let AP_public_key = get_random_curve_point();

        let input_sum = vi.iter().fold(0, |x, y| x + y);
        let output_sum = vo.iter().fold(0, |x, y| x + y);

        assert_eq!(input_sum, output_sum);

        let bases = Bases::new(get_L(), get_G(), 20);

        let mut kyc_sources = vec![generate_starting_KYC_proof(p)];
        for i in 0..5 {
            let t = Scalar::random(&mut csprng);
            kyc_sources.push(generate_starting_KYC_proof(t));
        }
        let transaction = create_transaction(
            inputs,
            ri,
            vo,
            output_pub_keys,
            p,
            AP_public_key,
            kyc_sources,
            bases.clone(),
        );
        let ser = bincode::serialize(&transaction).unwrap();
        let dec:Transaction = bincode::deserialize(&ser).unwrap();
        assert!(verify_transaction(&dec, bases));
    }
}
