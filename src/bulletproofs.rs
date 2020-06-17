use super::core::*;
use super::*;
use alloc::vec::*;
use curve25519_dalek::edwards::*;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;

use sha2::Sha256;
use sha2::Digest;
use rand_core::RngCore;
use rand_core::OsRng;
use serde::*;

const RANGE_SIZE: usize = 64;

struct DLTable {
    array: Vec<Vec<(CompressedEdwardsY, u64)>>,
}
impl DLTable {
    pub fn new() -> DLTable {
        let mut list = Vec::new();
        for _ in 0..(1 << 20) {
            list.push(Vec::<(CompressedEdwardsY, u64)>::new());
        }

        DLTable { array: list }
    }

    pub fn insert(&mut self, V: CompressedEdwardsY, i: u64) {
        let b = V.as_bytes();
        let index = ((b[29] as usize & 0xf) << 16) | ((b[30] as usize) << 8) | (b[31] as usize);
        self.array[index].push((V, i));
    }

    pub fn get(&mut self, V: &CompressedEdwardsY) -> Option<u64> {
        let b = V.as_bytes();
        let index = ((b[29] as usize & 0xf) << 16) | ((b[30] as usize) << 8) | (b[31] as usize);
        let list = &self.array[index];
        for (W, i) in list {
            if *V == *W {
                return Some(*i);
            }
        }
        return None;
    }
}

pub fn discrete_log_2n_bit(n: u64, G: EdwardsPoint, H: EdwardsPoint) -> u64 {
    let two_to_the_n: u64 = 1 << n;
    let mut saved_map = DLTable::new();
    let mut V = EdwardsPoint::default();

    //Generate table
    for j in 0..two_to_the_n {
        let C = V.compress();
        saved_map.insert(C, j);
        V = V + G;
    }
    //V = Scalar::from(two_to_the_20) * G;
    let mut S = H;
    for i in 0..two_to_the_n {
        let C = S.compress();
        match saved_map.get(&C) {
            Some(j) => {
                return (i << n) + j;
            }
            None => {
                S = S - V;
            }
        }
    }

    return 0;
}

pub fn inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
    assert_eq!(a.len(), b.len());
    let mut sum = Scalar::zero();
    for i in 0..a.len() {
        sum += a[i] * b[i];
    }
    return sum;
}

fn add_mult_ed(x: Scalar, a: &[EdwardsPoint], y: Scalar, b: &[EdwardsPoint]) -> Vec<EdwardsPoint> {
    assert_eq!(a.len(), b.len());
    let mut output = vec![EdwardsPoint::default(); a.len()];
    for i in 0..a.len() {
        output[i] = x * a[i] + y * b[i];
    }
    return output;
}

fn mult_ed(x: &[Scalar], a: &[EdwardsPoint]) -> Vec<EdwardsPoint> {
    assert_eq!(x.len(), a.len());
    let mut output = vec![EdwardsPoint::default(); a.len()];
    for i in 0..a.len() {
        output[i] = x[i] * a[i];
    }
    return output;
}

fn mult_ed_single(x: Scalar, a: &[EdwardsPoint]) -> Vec<EdwardsPoint> {
    let mut output = vec![EdwardsPoint::default(); a.len()];
    for i in 0..a.len() {
        output[i] = x * a[i];
    }
    return output;
}

pub fn multiscalar_mul_add(
    x: &[Scalar],
    a: &[EdwardsPoint],
    y: &[Scalar],
    b: &[EdwardsPoint],
) -> EdwardsPoint {
    let mut s = Vec::new();
    let mut v = Vec::new();
    for i in 0..x.len() {
        s.push(x[i]);
        v.push(a[i]);
    }
    for i in 0..y.len() {
        s.push(y[i]);
        v.push(b[i]);
    }
    return EdwardsPoint::multiscalar_mul(&s, &v);
}

fn add_mult(x: Scalar, a: &[Scalar], y: Scalar, b: &[Scalar]) -> Vec<Scalar> {
    assert_eq!(a.len(), b.len());
    let mut output = vec![Scalar::zero(); a.len()];
    for i in 0..a.len() {
        output[i] = x * a[i] + y * b[i];
    }
    return output;
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BulletProof {
    Ls: Vec<EdwardsPoint>,
    Rs: Vec<EdwardsPoint>,
    a: Scalar,
    b: Scalar,
}

pub fn fake_bullet_proof() -> BulletProof {
    return BulletProof {
        Ls: vec![],
        Rs: vec![],
        a: Scalar::zero(),
        b: Scalar::zero(),
    };
}
pub fn create_bulletproof(
    n: usize,
    g: &[EdwardsPoint],
    h: &[EdwardsPoint],
    u: EdwardsPoint,
    a: &Vec<Scalar>,
    b: &Vec<Scalar>,
) -> BulletProof {
    let mut a__ = a.clone();
    let mut b__ = b.clone();
    let mut Ls = Vec::new();
    let mut Rs = Vec::new();
    let mut G = g.to_vec();
    let mut H = h.to_vec();
    let mut n_ = n;
    while n_ > 1 {
        let (L, R, a_, b_, x) = create_bulletproof_one_step(n_, &G, &H, &u, &a__, &b__);
        Ls.push(L);
        Rs.push(R);
        a__ = a_;
        b__ = b_;
        n_ = n_ / 2;
        G = add_mult_ed(x.invert(), &G[0..n_], x, &G[n_..]);
        H = add_mult_ed(x, &H[0..n_], x.invert(), &H[n_..]);
    }

    return BulletProof {
        Ls: Ls,
        Rs: Rs,
        a: a__[0],
        b: b__[0],
    };
}
fn create_bulletproof_one_step(
    n: usize,
    g: &[EdwardsPoint],
    h: &[EdwardsPoint],
    u: &EdwardsPoint,
    a: &[Scalar],
    b: &[Scalar],
) -> (EdwardsPoint, EdwardsPoint, Vec<Scalar>, Vec<Scalar>, Scalar) {
    assert_eq!(n, g.len());
    assert_eq!(n, h.len());
    assert_eq!(n, a.len());
    assert_eq!(n, b.len());
    let n_ = n / 2;
    assert_eq!(n_ * 2, n);
    let a1 = &a[0..n_];
    let a2 = &a[n_..];
    let b1 = &b[0..n_];
    let b2 = &b[n_..];

    let L = multiscalar_mul_add(a1, &g[n_..], b2, &h[0..n_]) + inner_product(a1, b2) * u;
    let R = multiscalar_mul_add(a2, &g[0..n_], b1, &h[n_..]) + inner_product(a2, b1) * u;
    let x = get_hash(&L, &R);
    let x_ = x.invert();
    let a_ = add_mult(x, a1, x_, a2);
    let b_ = add_mult(x_, b1, x, b2);

    return (L, R, a_, b_, x);
}

pub fn get_hash_of_data_and_points(data: &[u8], points: &[&EdwardsPoint]) -> Scalar {
    let mut bytes = vec![0u8; points.len() * 32 + data.len()];
    let len = points.len();
    copy(&mut bytes[0..data.len()], &data);
    for i in 0..len {
        let point = points[i];
        copy(
            &mut bytes[i * 32..(i + 1) * 32],
            &point.compress().to_bytes(),
        );
    }
    let mut hash = [0u8; 32];

    let mut hasher = Sha256::new();
    hasher.input(&bytes);
    hash.copy_from_slice(hasher.result().as_slice());
    let x = Scalar::from_bytes_mod_order(hash);
    return x;
}
#[allow(non_snake_case)]
pub fn get_hash(L: &EdwardsPoint, R: &EdwardsPoint) -> Scalar {

    let mut hash = [0u8; 32];

    let mut hasher = Sha256::new();
    hasher.input(&L.compress().to_bytes());
    hasher.input(&R.compress().to_bytes());
    hash.copy_from_slice(hasher.result().as_slice());
    let x = Scalar::from_bytes_mod_order(hash);
    return x;
}

fn alt_mult(x: Scalar, v: &mut [Scalar], b: usize) {
    let x_ = x.invert();
    let mut up = false;
    for i in 0..v.len() {
        if i % b == 0 {
            up = !up;
        }
        if up {
            v[i] *= x;
        } else {
            v[i] *= x_;
        }
    }
}

#[allow(non_snake_case)]
pub fn verify_bulletproof(
    n: usize,
    g: &[EdwardsPoint],
    h: &[EdwardsPoint],
    u: EdwardsPoint,
    P: EdwardsPoint,
    proof: &BulletProof,
) -> bool {
    let mut s = vec![Scalar::one(); n];
    let mut s_ = vec![Scalar::one(); n];
    let mut n_ = n;

    let mut Lmul = EdwardsPoint::default();
    let mut Rmul = EdwardsPoint::default();
    let Ls = &proof.Ls;
    let Rs = &proof.Rs;
    let a = proof.a;
    let b = proof.b;
    if Ls.len() != Rs.len() {
        return false;
    }
    for i in 0..Ls.len() {
        let L = Ls[i];
        let R = Rs[i];

        let x = get_hash(&L, &R);
        let x_ = x.invert();
        alt_mult(x_, &mut s, n_ / 2);
        alt_mult(x, &mut s_, n_ / 2);
        Lmul += x * x * L;
        Rmul += x_ * x_ * R;
        n_ = n_ / 2;
    }

    if n_ != 1 {
        return false;
    }
    let G = EdwardsPoint::multiscalar_mul(s, g);
    let H = EdwardsPoint::multiscalar_mul(s_, h);
    let P_ = a * G + b * H + a * b * u;

    return (P_) == P + Lmul + Rmul;
}

#[allow(non_snake_case)]
pub fn verify_bulletproof_hmul(
    n: usize,
    g: &[EdwardsPoint],
    h: &[EdwardsPoint],
    hmul: &[Scalar],
    u: EdwardsPoint,
    P: EdwardsPoint,
    proof: &BulletProof,
) -> bool {
    let mut s = vec![Scalar::one(); n];
    let mut s_ = vec![Scalar::one(); n];
    let mut n_ = n;

    let mut Lmul = EdwardsPoint::default();
    let mut Rmul = EdwardsPoint::default();
    let Ls = &proof.Ls;
    let Rs = &proof.Rs;
    let a = proof.a;
    let b = proof.b;
    if Ls.len() != Rs.len() {
        return false;
    }
    for i in 0..Ls.len() {
        let L = Ls[i];
        let R = Rs[i];

        let x = get_hash(&L, &R);
        let x_ = x.invert();
        alt_mult(x_, &mut s, n_ / 2);
        alt_mult(x, &mut s_, n_ / 2);
        Lmul += x * x * L;
        Rmul += x_ * x_ * R;
        n_ = n_ / 2;
    }

    if n_ != 1 {
        return false;
    }
    let G = EdwardsPoint::multiscalar_mul(s, g);
    let H = EdwardsPoint::multiscalar_mul(multiply_scalar_arrays(&s_, hmul), h);
    let P_ = EdwardsPoint::multiscalar_mul(&[a, b, a * b], &[G, H, u]);

    return (P_) == P + Lmul + Rmul;
}

fn fill_random_scalars(arr: &mut [Scalar]) {
    let mut csprng: OsRng = OsRng::default();
    for i in 0..arr.len() {
        arr[i] = Scalar::random(&mut csprng);
    }
}

fn scalars_array_from_bits(v: u64) -> [Scalar; RANGE_SIZE] {
    let mut arr = [Scalar::default(); RANGE_SIZE];
    let mut w = v;
    for i in 0..RANGE_SIZE {
        arr[i] = Scalar::from(w & 1u64);
        w >>= 1;
    }
    return arr;
}

fn scalars_vec_from_bits_of_values_array(v: &[u64]) -> Vec<Scalar> {
    let m = v.len();
    let mut arr = vec![Scalar::default(); RANGE_SIZE * m];

    for j in 0..m {
        let mut w = v[j];
        for i in 0..RANGE_SIZE {
            arr[j * RANGE_SIZE + i] = Scalar::from(w & 1u64);
            w >>= 1;
        }
    }

    return arr;
}
fn add_scalar_to_array(a: &[Scalar], b: Scalar) -> Vec<Scalar> {
    let mut arr = vec![Scalar::default(); a.len()];
    for i in 0..a.len() {
        arr[i] = a[i] + b;
    }
    return arr;
}

fn multiply_scalar_to_array(a: &[Scalar], b: Scalar) -> Vec<Scalar> {
    let mut arr = vec![Scalar::default(); a.len()];
    for i in 0..a.len() {
        arr[i] = a[i] * b;
    }
    return arr;
}

fn array_of(z: Scalar, n: usize) -> Vec<Scalar> {
    let mut arr = vec![Scalar::default(); n];
    for i in 0..n {
        arr[i] = z;
    }
    return arr;
}

fn add_scalar_arrays(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    let mut arr = vec![Scalar::default(); a.len()];
    for i in 0..a.len() {
        arr[i] = a[i] + b[i];
    }
    return arr;
}

fn substract_scalar_arrays(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    let mut arr = vec![Scalar::default(); a.len()];
    for i in 0..a.len() {
        arr[i] = a[i] - b[i];
    }
    return arr;
}

pub fn multiply_scalar_arrays(a: &[Scalar], b: &[Scalar]) -> Vec<Scalar> {
    let mut arr = vec![Scalar::default(); a.len()];
    for i in 0..a.len() {
        arr[i] = a[i] * b[i];
    }
    return arr;
}

fn to_the_n(x: Scalar, n: usize) -> Vec<Scalar> {
    let mut arr = vec![Scalar::default(); n];
    let mut prod = Scalar::one();
    for i in 0..n {
        arr[i] = prod;
        prod = prod * x;
    }
    return arr;
}

fn to_the_n_multi_var(x: Scalar, z: Scalar, n: usize, m: usize) -> Vec<Scalar> {
    let mut arr = vec![Scalar::default(); n * m];
    let mut z_pow = z * z;
    for j in 0..m {
        let mut prod = z_pow;
        for i in 0..n {
            arr[j * RANGE_SIZE + i] = prod;
            prod = prod * x;
        }
        z_pow *= z;
    }

    return arr;
}

#[allow(non_snake_case)]
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct BulletRangeProof {
    A: EdwardsPoint,
    SS: EdwardsPoint,
    T1: EdwardsPoint,
    T2: EdwardsPoint,
    tao_x: Scalar,
    mu: Scalar,
    t_cap: Scalar,
    pub V: Vec<EdwardsPoint>,
    bullet_proof: BulletProof,
}

pub fn bullet_range_verify(proof: &BulletRangeProof, bases: Bases) -> bool {
    return bullet_range_verify_ex(proof, &bases, None, Scalar::zero());
}

#[allow(non_snake_case)]
pub fn bullet_range_verify_ex(
    proof: &BulletRangeProof,
    bases: &Bases,
    extra_hash_input: Option<(&[u8], &EdwardsPoint, &EdwardsPoint)>,
    other_hash: Scalar,
) -> bool {
    let m = proof.V.len();
    let gs: Vec<EdwardsPoint> = bases.Gs[0..m * RANGE_SIZE].iter().map(|x| *x).collect();
    let hs: Vec<EdwardsPoint> = bases.Hs[0..m * RANGE_SIZE].iter().map(|x| *x).collect();
    let g = bases.GInit;
    let h = bases.HInit;
    let x = match extra_hash_input {
        Some((message, R, P)) => {
            get_hash_of_data_and_points(&message, &[&proof.T1, &proof.T2, R, P]) - other_hash
        }
        None => get_hash(&proof.T1, &proof.T2),
    };
    let y = get_hash(&proof.A, &proof.SS);
    let z = get_hash(&proof.SS, &proof.A);
    let ymn = to_the_n(y, RANGE_SIZE * m);
    let z_m = to_the_n(z, m);
    let twon = to_the_n(Scalar::from(2u64), RANGE_SIZE);
    let onen = to_the_n(Scalar::from(1u64), RANGE_SIZE);
    let one_m = to_the_n(Scalar::from(1u64), m);
    let mut _z2_z_m = multiply_scalar_to_array(&z_m, -z * z);
    let twon_z_pow = to_the_n_multi_var(Scalar::from(2u64), z, RANGE_SIZE, m);

    let one_mn = array_of(Scalar::from(1u64), RANGE_SIZE * m);
    let sig = (z - z * z) * inner_product(&one_mn, &ymn)
        - z * z * z * inner_product(&onen, &twon) * inner_product(&z_m, &one_m);

    let mut mult_scalars = vec![proof.t_cap, proof.tao_x, -sig, -x, -x * x];
    mult_scalars.append(&mut _z2_z_m);
    let mut mult_points = vec![g, h, g, proof.T1, proof.T2];
    mult_points.append(&mut proof.V.clone());

    let sum =
        EdwardsPoint::multiscalar_mul(&mut mult_scalars.into_iter(), &mut mult_points.into_iter());

    if sum != EdwardsPoint::default() {
        return false;
    }

    let y_mn = &to_the_n(y.invert(), RANGE_SIZE * m);

    let zymn = multiply_scalar_to_array(&ymn, z);
    let h__ = multiscalar_mul_add(
        &multiply_scalar_arrays(&twon_z_pow, &y_mn),
        &hs,
        &multiply_scalar_arrays(&zymn, &y_mn),
        &hs,
    );
    let g__ = EdwardsPoint::multiscalar_mul(array_of(-z, RANGE_SIZE * m), gs.clone());
    let P = proof.A + x * proof.SS + g__ + h__;

    let P_ = P - proof.mu * h + proof.t_cap * h;

    return verify_bulletproof_hmul(RANGE_SIZE * m, &gs, &hs, &y_mn, h, P_, &proof.bullet_proof);
}

fn to_2s_power(y: usize) -> usize {
    let mut num_ones = 0;
    let mut pows = 1usize;
    let mut x = y;
    while x > 0 {
        pows <<= 1;
        if x & 1 == 1 {
            num_ones += 1;
        }
        x >>= 1;
    }
    if num_ones == 1 {
        return y;
    } else {
        return pows;
    }
}

fn to_2s_pow_vec(v: &[u64]) -> Vec<u64> {
    let mut v: Vec<u64> = v.iter().map(|x| *x).collect();
    let twos_pow = to_2s_power(v.len());
    let m = v.len();
    for _ in m..twos_pow {
        v.push(0);
    }
    return v;
}

fn to_2s_pow_scalar_vec(g: &[Scalar]) -> Vec<Scalar> {
    let mut g: Vec<Scalar> = g.iter().map(|x| *x).collect();
    let twos_pow = to_2s_power(g.len());
    let m = g.len();

    for _ in m..twos_pow {
        g.push(Scalar::zero());
    }
    return g;
}
#[allow(non_snake_case)]
pub fn bullet_range_proof(
    gamma: &[Scalar],
    v: &[u64], //the length of v must be a power of 2 at this point.
    bases: &Bases,
) -> BulletRangeProof {
    return bullet_range_proof_ex(gamma, v, bases);
}

fn bullet_range_proof_ex_T1_T2(
    gamma: &[Scalar],
    v: &[u64], //the length of v must be a power of 2 at this point. In case of fake proof, this is a random value
    bases: &Bases,
) -> (
    EdwardsPoint,
    EdwardsPoint,
    Vec<Scalar>,
    Vec<Scalar>,
    Vec<Scalar>,
    Vec<Scalar>,
    Scalar,
    Scalar,
    Scalar,
    usize,
    Scalar,
    Scalar,
    Vec<EdwardsPoint>,
    Vec<EdwardsPoint>,
    EdwardsPoint,
    EdwardsPoint,
    Scalar,
    Vec<u64>,
    Vec<Scalar>,
) {
    let v = to_2s_pow_vec(v);
    let gamma = to_2s_pow_scalar_vec(gamma);
    let m = v.len();
    let gs: Vec<EdwardsPoint> = bases.Gs[0..RANGE_SIZE * m].iter().map(|x| *x).collect();
    let hs: Vec<EdwardsPoint> = bases.Hs[0..RANGE_SIZE * m].iter().map(|x| *x).collect();
    let g = bases.GInit;
    let h = bases.HInit;

    let aL = scalars_vec_from_bits_of_values_array(&v);

    let aR = substract_scalar_arrays(&aL, &to_the_n(Scalar::from(1u64), RANGE_SIZE * m));

    let mut csprng: OsRng = OsRng::default();
    let alpha = Scalar::random(&mut csprng);
    let mut sL = vec![Scalar::default(); RANGE_SIZE * m];
    let mut sR = vec![Scalar::default(); RANGE_SIZE * m];
    fill_random_scalars(&mut sL);
    fill_random_scalars(&mut sR);
    let rho = Scalar::random(&mut csprng);

    let A = alpha * h + multiscalar_mul_add(&aL, &gs, &aR, &hs);
    let SS = rho * h + multiscalar_mul_add(&sL, &gs, &sR, &hs);

    let y = get_hash(&A, &SS);
    let z = get_hash(&SS, &A);

    let tao1 = Scalar::random(&mut csprng);
    let tao2 = Scalar::random(&mut csprng);
    let zmn = array_of(z, RANGE_SIZE * m);
    let l0 = substract_scalar_arrays(&aL, &zmn);
    let l1 = sL;

    let ymn = to_the_n(y, RANGE_SIZE * m);
    let twon_z_pow = to_the_n_multi_var(Scalar::from(2u64), z, RANGE_SIZE, m);

    let r1 = multiply_scalar_arrays(&ymn, &sR);
    let r0 = add_scalar_arrays(
        &multiply_scalar_arrays(&ymn, &add_scalar_arrays(&aR, &zmn)),
        &twon_z_pow,
    );
    let t1 = inner_product(&l0, &r1) + inner_product(&l1, &r0);
    let t2 = inner_product(&l1, &r1);
    let T1 = g * t1 + h * tao1;
    let T2 = g * t2 + h * tao2;
    return (
        T1, T2, l0, r0, l1, r1, tao1, tao2, z, m, alpha, rho, gs, hs, A, SS, y, v, gamma,
    );
}

fn bullet_range_proof_rest(
    bases: &Bases,
    T1: EdwardsPoint,
    T2: EdwardsPoint,
    l0: Vec<Scalar>,
    r0: Vec<Scalar>,
    l1: Vec<Scalar>,
    r1: Vec<Scalar>,
    tao1: Scalar,
    tao2: Scalar,
    z: Scalar,
    m: usize,
    alpha: Scalar,
    rho: Scalar,
    gs: Vec<EdwardsPoint>,
    hs: Vec<EdwardsPoint>,
    A: EdwardsPoint,
    SS: EdwardsPoint,
    y: Scalar,
    v: Vec<u64>,
    gamma: &[Scalar],
    challenge: Scalar,
) -> BulletRangeProof {
    let g = bases.GInit;
    let h = bases.HInit;
    let x = challenge;
    let l = add_scalar_arrays(&l0, &multiply_scalar_to_array(&l1, x));
    let r = add_scalar_arrays(&r0, &multiply_scalar_to_array(&r1, x));

    let z_m = to_the_n(z, m);
    let tao_x = x * x * tao2 + x * tao1 + z * z * inner_product(&z_m, &gamma);

    // let t0 = inner_product(&l0, &r0);

    let t_cap = inner_product(&l, &r);

    //check t_cap is computed correctly.
    //assert_eq!(t2*x*x+t1*x+t0, t_cap);

    let mu = alpha + rho * x;
    //assert_eq!(g,h);
    let V: Vec<EdwardsPoint> = v
        .into_iter()
        .zip(gamma.into_iter())
        .map(|(x, gam)| Scalar::from(x) * g + gam * h)
        .collect();

    let h_ = mult_ed(&to_the_n(y.invert(), RANGE_SIZE * m), &hs);
    let bullet_proof = create_bulletproof(RANGE_SIZE * m, &gs, &h_, h, &l, &r);

    return BulletRangeProof {
        A: A,
        SS: SS,
        T1: T1,
        T2: T2,
        tao_x: tao_x,
        t_cap: t_cap,
        mu: mu,
        V: V,
        bullet_proof: bullet_proof,
    };
}

#[allow(non_snake_case)]
pub fn bullet_range_proof_ex(
    gamma: &[Scalar],
    v: &[u64], //the length of v must be a power of 2 at this point. In case of fake proof, this is a random value
    bases: &Bases,
) -> BulletRangeProof {
    let (T1, T2, l0, r0, l1, r1, tao1, tao2, z, m, alpha, rho, gs, hs, A, SS, y, v, gamma) =
        bullet_range_proof_ex_T1_T2(gamma, v, bases);

    let challenge = get_hash(&T1, &T2);

    return bullet_range_proof_rest(
        bases, T1, T2, l0, r0, l1, r1, tao1, tao2, z, m, alpha, rho, gs, hs, A, SS, y, v, &gamma,
        challenge,
    );
}

pub fn create_modified_schnorr(
    bases: &Bases,
    message: &[u8],
    private_key: Scalar,
    extrapoints: (&EdwardsPoint, &EdwardsPoint),
    fake_hash: Scalar,
) -> (Scalar, Scalar) {
    let mut csprng: OsRng = OsRng::default();
    let r = Scalar::random(&mut csprng);
    let P = private_key * bases.GInit;
    let R = r * bases.GInit;
    let h =
        get_hash_of_data_and_points(&message, &[extrapoints.0, extrapoints.1, &P, &R]) - fake_hash;
    let s = r - h * private_key;
    return (s, h);
}

pub fn verify_modified_schnorr(
    bases: &Bases,
    message: &[u8],
    signature: &(Scalar, Scalar),
    P: &EdwardsPoint,
    extrapoints: (&EdwardsPoint, &EdwardsPoint),
    other_hash: Scalar,
) -> bool {
    let R = EdwardsPoint::multiscalar_mul(&[signature.0, signature.1], &[bases.GInit, *P]);
    let hash =
        get_hash_of_data_and_points(&message, &[extrapoints.0, extrapoints.1, &P, &R]) - other_hash;
    return hash.eq(&signature.1);
}

pub struct RangeOrSchnorrProof {
    range_proof: BulletRangeProof,
    schnorr: (Scalar, Scalar),
    range_hash: Scalar,
}
pub fn create_range_or_schnorr_fake_range(
    gamma: Scalar,
    v: Scalar,
    bases: &Bases,
    AP_pr_key: Scalar,
    schnorr_message: &[u8],
) -> RangeOrSchnorrProof {
    let V = v * bases.GInit + gamma * bases.HInit;
    let mut csprng: OsRng = OsRng::default();
    let v_ = csprng.next_u64();
    let challenge = Scalar::random(&mut csprng);
    let (T1_, T2, l0, r0, l1, r1, tao1, tao2, z, m, alpha, rho, gs, hs, A, SS, y, v__, gamma) =
        bullet_range_proof_ex_T1_T2(&[gamma], &[v_], bases);

    let v_diff = v - Scalar::from(v_); //v = v_+v_diff;
    let T1 = T1_ - z * z * challenge.invert() * v_diff * bases.GInit;
    let sig = create_modified_schnorr(&bases, schnorr_message, AP_pr_key, (&T1, &T2), challenge);
    let mut bullet_range_proof = bullet_range_proof_rest(
        bases, T1, T2, l0, r0, l1, r1, tao1, tao2, z, m, alpha, rho, gs, hs, A, SS, y, v__, &gamma,
        challenge,
    );
    bullet_range_proof.V[0] = V;
    return RangeOrSchnorrProof {
        range_proof: bullet_range_proof,
        schnorr: sig,
        range_hash: challenge,
    };
}
pub fn create_range_or_schnorr_fake_schnorr(
    gamma: Scalar,
    v: u64,
    bases: &Bases,
    AP_key: &EdwardsPoint,
    schnorr_message: &[u8],
) -> RangeOrSchnorrProof {
    let mut csprng: OsRng = OsRng::default();
    let s = Scalar::random(&mut csprng);
    let h = Scalar::random(&mut csprng);
    let G = bases.GInit;
    let R = s * G + h * AP_key;
    let (T1, T2, l0, r0, l1, r1, tao1, tao2, z, m, alpha, rho, gs, hs, A, SS, y, v, gamma) =
        bullet_range_proof_ex_T1_T2(&[gamma], &[v], bases);
    let hash = get_hash_of_data_and_points(&schnorr_message, &[&T1, &T2, &AP_key, &R]);
    let challenge = hash - h;
    let bullet_range_proof = bullet_range_proof_rest(
        bases, T1, T2, l0, r0, l1, r1, tao1, tao2, z, m, alpha, rho, gs, hs, A, SS, y, v, &gamma,
        challenge,
    );
    return RangeOrSchnorrProof {
        range_proof: bullet_range_proof,
        schnorr: (s, h),
        range_hash: challenge,
    };
}

pub fn verify_range_or_schnorr(
    bases: &Bases,
    proof: &RangeOrSchnorrProof,
    AP_key: &EdwardsPoint,
    message: &[u8],
) -> bool {
    let T1 = proof.range_proof.T1;
    let T2 = proof.range_proof.T2;
    let P = AP_key;
    let R = EdwardsPoint::multiscalar_mul(&[proof.schnorr.0, proof.schnorr.1], &[bases.GInit, *P]);
    let hash = get_hash_of_data_and_points(&message, &[&T1, &T2, &P, &R]);

    hash.eq(&(proof.schnorr.1 + proof.range_hash))
        && bullet_range_verify_ex(
            &proof.range_proof,
            bases,
            Some((&message, &P, &R)),
            proof.schnorr.1,
        )
        && verify_modified_schnorr(
            bases,
            &message,
            &proof.schnorr,
            &AP_key,
            (&proof.range_proof.T1, &proof.range_proof.T2),
            proof.range_hash,
        )
}

#[derive(Clone, Debug, PartialEq)]
//The commitment V = v*G+gamma*H
pub struct Bases {
    GInit: EdwardsPoint,
    HInit: EdwardsPoint,
    Gs: Vec<EdwardsPoint>,
    Hs: Vec<EdwardsPoint>,
}

impl Bases {
    pub fn new(GInit: EdwardsPoint, HInit: EdwardsPoint, max_len: usize) -> Bases {
        let mut ginit = GInit;
        let mut hinit = HInit;
        let mut gs = Vec::new();
        let mut hs = Vec::new();
        for _ in 0..RANGE_SIZE * max_len {
            gs.push(get_hash(&ginit, &hinit) * ginit);
            hs.push(get_hash(&hinit, &ginit) * hinit);
            ginit = get_hash(&ginit, &hinit) * ginit;
            hinit = get_hash(&hinit, &ginit) * hinit;
        }
        return Bases {
            GInit: GInit,
            HInit: HInit,
            Gs: gs,
            Hs: hs,
        };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand_core::RngCore;
    use rand_core::OsRng;

    #[allow(non_snake_case)]
    #[test]

    fn test_bullet_range_proof_with_fake_schnorr() {
        let bases = Bases::new(get_L(), get_K(), 20);
        let mut csprng: OsRng = OsRng::default();
        let gamma = Scalar::random(&mut csprng);
        let v = csprng.next_u64();
        let AP_key = Scalar::random(&mut csprng) * bases.GInit;
        let message = [0u8, 1u8, 2u8];

        let proof = create_range_or_schnorr_fake_schnorr(gamma, v, &bases, &AP_key, &message);
        assert!(verify_range_or_schnorr(&bases, &proof, &AP_key, &message));
    }

    #[allow(non_snake_case)]
    #[test]

    fn test_bullet_range_proof_with_fake_range() {
        let bases = Bases::new(get_L(), get_K(), 20);
        let mut csprng: OsRng = OsRng::default();
        let gamma = Scalar::random(&mut csprng);
        let v = Scalar::random(&mut csprng);
        let AP__pr_key = Scalar::random(&mut csprng);
        let AP_key = AP__pr_key * bases.GInit;
        let message = [0u8, 1u8, 2u8];

        let proof = create_range_or_schnorr_fake_range(gamma, v, &bases, AP__pr_key, &message);
        assert!(verify_range_or_schnorr(&bases, &proof, &AP_key, &message));
    }

    #[allow(non_snake_case)]
    #[test]

    fn test_bullet_range_proof() {
        let bases = Bases::new(get_L(), get_K(), 20);
        let mut csprng: OsRng = OsRng::default();
        let gamma = [
            Scalar::random(&mut csprng),
            Scalar::random(&mut csprng),
            Scalar::random(&mut csprng),
            Scalar::random(&mut csprng),
            Scalar::random(&mut csprng),
        ];
        let v = [
            csprng.next_u64(),
            csprng.next_u64(),
            csprng.next_u64(),
            csprng.next_u64(),
            csprng.next_u64(),
        ];

        let proof = bullet_range_proof(&gamma, &v, &bases);
        assert!(bullet_range_verify(&proof, bases));
    }

    // #[allow(non_snake_case)]
    // #[test]

    // fn test_discrete_log() {
    //     let n = 20u64;
    //     let mut csprng: OsRng = OsRng::new().unwrap();
    //     let rand = csprng.next_u64();
    //     let trimmed_rand = rand >> (RANGE_SIZE - 2 * n); // make a 2n bit random number
    //     let G = get_G();
    //     let H = Scalar::from(trimmed_rand) * G;
    //     let log = discrete_log_2n_bit(n, G, H);
    //     assert_eq!(log, trimmed_rand);
    // }

    #[allow(non_snake_case)]
    #[test]
    fn test_bulletproof() {
        let mut ginit = get_G();
        let mut hinit = get_K();
        let u = get_L();
        let mut gs = Vec::new();
        let mut hs = Vec::new();
        let mut a = Vec::new();
        let mut b = Vec::new();
        for _ in 0..16 {
            gs.push(get_hash(&ginit, &hinit) * ginit);
            hs.push(get_hash(&hinit, &ginit) * hinit);
            ginit = get_hash(&ginit, &hinit) * ginit;
            hinit = get_hash(&hinit, &ginit) * hinit;
            let mut csprng: OsRng = OsRng::default();
            a.push(Scalar::random(&mut csprng));
            b.push(Scalar::random(&mut csprng));
        }

        let P = multiscalar_mul_add(&a, &gs, &b, &hs) + inner_product(&a, &b) * u;
        let proof = create_bulletproof(16, &gs, &hs, u, &a, &b);

        let ver = verify_bulletproof(16, &gs, &hs, u, P, &proof);
        assert!(ver);
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_modified_schnorr() {
        let mut csprng: OsRng = OsRng::default();
        let bases = Bases::new(get_L(), get_K(), 2);
        let private_key = Scalar::random(&mut csprng);
        let P = bases.GInit * private_key;
        let extra_points = (&bases.Gs[1], &bases.Hs[1]);
        let message = "hello".as_bytes();
        let other_hash = Scalar::random(&mut csprng);
        let signature =
            create_modified_schnorr(&bases, &message, private_key, extra_points, other_hash);
        assert!(verify_modified_schnorr(
            &bases,
            &message,
            &signature,
            &P,
            extra_points,
            other_hash
        ));
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_to_2s_power() {
        assert_eq!(to_2s_power(1), 1);
        assert_eq!(to_2s_power(3), 4);
        assert_eq!(to_2s_power(5), 8);
        assert_eq!(to_2s_power(8), 8);
    }
}
