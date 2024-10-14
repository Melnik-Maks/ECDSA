use num_bigint::{BigUint, BigInt, Sign};
use rand::Rng;
use num_traits::{One, Zero};
use sha2::{Sha256, Digest};
use num::Integer;

const SECP256K1_P: &str = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F";

const SECP256K1_N: &str = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";

const SECP256K1_GX: &str = "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798";

const SECP256K1_GY: &str = "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8";

fn gen_random_biguint_below(n: &BigUint) -> BigUint {
    let mut rng = rand::thread_rng();
    let bit_size = n.bits() as usize;

    loop {
        let mut random_bytes = vec![0u8; (bit_size + 7) / 8];
        rng.fill(&mut random_bytes[..]);

        let mut random_number = BigUint::from_bytes_be(&random_bytes);


        if random_number.bits() as usize > bit_size {
            random_number >>= random_number.bits() as usize - bit_size;
        }

        if random_number < *n {
            return random_number;
        }
    }
}

fn mod_add(a: &BigUint, b: &BigUint, p: &BigUint) -> BigUint {
    (a + b) % p
}

fn mod_sub(a: &BigUint, b: &BigUint, p: &BigUint) -> BigUint {
    if a >= b {
        (a - b) % p
    } else {
        (a + p - b) % p
    }
}

fn mod_mul(a: &BigUint, b: &BigUint, p: &BigUint) -> BigUint {
    (a * b) % p
}

#[derive(Clone, Debug)]
struct ECPoint {
    x: BigUint,
    y: BigUint,
}

impl ECPoint {
    fn add(&self, other: &ECPoint, p: &BigUint) -> ECPoint {
        let slope;
        if self.x == other.x && self.y == other.y {
            slope = mod_mul(&(BigUint::from(3u32) * mod_mul(&self.x , &self.x, &p)), &mod_inverse(&(BigUint::from(2u32) * &self.y), &p), &p);
        } else {
            slope = mod_mul(&mod_sub(&other.y, &self.y, &p), &mod_inverse(&mod_sub(&other.x, &self.x, &p), &p), &p);
        }

        let x_r = mod_sub(&mod_mul(&slope, &slope, &p), &self.x, &p);
        let x_r = mod_sub(&x_r, &other.x, &p);
        let y_r = mod_sub(&mod_mul(&slope , &mod_sub(&self.x, &x_r, &p), &p), &self.y, &p);

        ECPoint { x: x_r, y: y_r }
    }

    fn mul(&self, scalar: &BigUint, p: &BigUint) -> ECPoint {
        let mut result = self.clone();
        let mut temp = self.clone();
        let mut k = scalar.clone() - BigUint::one();

        while k > BigUint::zero() {

            if &k & BigUint::one() == BigUint::one() {
                result = result.add(&temp, p);
            }
            temp = temp.add(&temp, p);
            k >>= 1;
        }
        result
    }
}

fn mod_inverse(n: &BigUint, p: &BigUint) -> BigUint {
    let n = BigInt::from_biguint(Sign::Plus, n.clone());
    let p = BigInt::from_biguint(Sign::Plus, p.clone());

    if p.is_one() {
        return BigUint::one();
    }

    let (mut a, mut m, mut x, mut inv) = (n.clone(), p.clone(), BigInt::zero(), BigInt::one());

    while a > BigInt::one() {
        let (div, rem) = a.div_rem(&m);
        inv -= div * &x;
        a = rem;
        std::mem::swap(&mut a, &mut m);
        std::mem::swap(&mut x, &mut inv);
    }

    if inv < BigInt::zero() {
        inv += p;
    }

    BigUint::from_bytes_be(&inv.to_bytes_be().1)
}

fn generate_key_pair() -> (BigUint, ECPoint) {

    let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
    let g = ECPoint {
        x: BigUint::parse_bytes(SECP256K1_GX.as_bytes(), 16).unwrap(),
        y: BigUint::parse_bytes(SECP256K1_GY.as_bytes(), 16).unwrap(),
    };
    let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();

    let private_key = gen_random_biguint_below(&n);

    let public_key = g.mul(&private_key, &p);

    (private_key, public_key)
}

fn sign_message(private_key: &BigUint, message: &[u8]) -> (BigUint, BigUint) {
    let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
    let g = ECPoint {
        x: BigUint::parse_bytes(SECP256K1_GX.as_bytes(), 16).unwrap(),
        y: BigUint::parse_bytes(SECP256K1_GY.as_bytes(), 16).unwrap(),
    };
    let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();

    let hash = Sha256::digest(message);

    let z = BigUint::from_bytes_be(&hash) % &n;

    let k = gen_random_biguint_below(&n);


    let r_point = g.mul(&k, &p);
    let r = &r_point.x % &n;

    let k_inv = mod_inverse(&k, &n);
    let s = (&k_inv * (&z + r.clone() * private_key)) % &n;

    (r, s)
}

fn verify_signature(public_key: &ECPoint, message: &[u8], r: &BigUint, s: &BigUint) -> bool {
    let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
    let g = ECPoint {
        x: BigUint::parse_bytes(SECP256K1_GX.as_bytes(), 16).unwrap(),
        y: BigUint::parse_bytes(SECP256K1_GY.as_bytes(), 16).unwrap(),
    };
    let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();

    let hash = Sha256::digest(message);

    let h = BigUint::from_bytes_be(&hash) % &n;

    let s1 = mod_inverse(s, &n);

    let u1 = mod_mul(&h, &s1, &n);
    let u2 = mod_mul(r, &s1, &n);

    let point1 = g.mul(&u1, &p);
    let point2 = public_key.mul(&u2, &p);

    let point = point1.add(&point2, &p);

    &point.x % &n == *r
}

fn main() {

    let (private_key, public_key) = generate_key_pair();
    println!("Private_key: {:?},\nPublic_key: {:?}", private_key, public_key);

    let message = b"Hello, ECDSA!";

    let (r, s) = sign_message(&private_key, message);
    println!("Signed_message r: {}, s: {}", r, s);

    let is_valid = verify_signature(&public_key, message, &r, &s);
    println!("Verify_signature: {}", is_valid);
}
