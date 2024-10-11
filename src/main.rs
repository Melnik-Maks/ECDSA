use num_bigint::{BigUint};
use rand::Rng;
use num_traits::{One, Zero};
use sha2::{Sha256, Digest};
use std::ops::{Add, Mul};



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
        println!("{:?}", n.to_bytes_be());
        println!("{:?}", random_bytes);
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
        (a + BigUint::from(2u32) * p - b) % p
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
        //println!("\n-------\n{:?}", &self);
        //println!("{:?}", &other);
        //println!("P: {:?}", &p);
        let slope;
        if self.x == other.x && self.y == other.y {
            slope = mod_mul(&(BigUint::from(3u32) * mod_mul(&self.x , &self.x, p) % p), &mod_inverse(&(BigUint::from(2u32) * &self.y), p), p);
        } else {
            slope = mod_mul(&mod_sub(&other.y, &self.y, p), &mod_inverse(&mod_sub(&other.x, &self.x, p), p), p);
        }
        let x_r = mod_sub(&mod_mul(&slope, &slope, p), &self.x, p);
        let x_r = mod_sub(&x_r, &other.x, p);
        let y_r = mod_sub(&mod_mul(&slope , &mod_sub(&self.x, &x_r, p), p), &self.y, p);
        //println!("Result: X: {}, Y: {}", &x_r, &y_r);
        print!("{:?}\n", ((&y_r * &y_r)  % p) == (((&x_r * &x_r % p)* &x_r) % p + BigUint::from(7u32)) % p);
        ECPoint { x: x_r, y: y_r }
    }

    fn mul(&self, scalar: &BigUint, p: &BigUint) -> ECPoint {
        let mut result = ECPoint {
            x: BigUint::zero(),
            y: BigUint::zero(),
        };
        let mut temp = self.clone();
        let mut k = scalar.clone();

        while k > BigUint::zero() {
            if &k & BigUint::one() == BigUint::one() {
                //println!("111 - {:?}", temp);
                result = result.add(&temp, p);
            }
            //println!("222 - {:?}", temp);
            temp = temp.add(&temp, p);
            k >>= 1;
        }
        result
    }
}


fn mod_inverse(a: &BigUint, m: &BigUint) -> BigUint {
    let mut mn = (m.clone(), a.clone());
    let mut xy = (BigUint::zero(), BigUint::one());
    let p = m;

    while mn.1 != BigUint::zero() {
        let quotient = &mn.0 / &mn.1;
        mn = (mn.1.clone(), mod_sub(&mn.0.clone(), &mod_mul(&quotient, &mn.1.clone(), p), p));
        xy = (xy.1.clone(), mod_sub(&xy.0.clone(), &mod_mul(&quotient, &xy.1.clone(), p), p));
    }

    xy.0 % m
}

fn generate_key_pair() -> (BigUint, ECPoint) {
    let p = BigUint::parse_bytes(SECP256K1_P.as_bytes(), 16).unwrap();
    let g = ECPoint {
        x: BigUint::parse_bytes(SECP256K1_GX.as_bytes(), 16).unwrap(),
        y: BigUint::parse_bytes(SECP256K1_GY.as_bytes(), 16).unwrap(),
    };
    let n = BigUint::parse_bytes(SECP256K1_N.as_bytes(), 16).unwrap();

    let private_key = gen_random_biguint_below(&n);
    //println!("Private_key: {}", private_key);
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
    println!("{:?}", &hash);

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
    println!("{:?}", &hash);
    let h = BigUint::from_bytes_be(&hash) % &n;

    let s1 = mod_inverse(s, &n);

    let u1 = mod_mul(&h, &s1, &n);
    let u2 = mod_mul(r, &s1, &n);

    let point1 = g.mul(&u1, &p);
    let point2 = public_key.mul(&u2, &p);

    let point = point1.add(&point2, &p);

    println!("{:?} = {:?}", &point.x.clone() % &n, *r);
    &point.x % &n == *r
}

fn main() {
    //println!("{}", mod_inverse(&BigUint::from(2u64), &BigUint::from(99989u64)));
    //println!("2222222222222222");
    // Генерація ключів
    let (private_key, public_key) = generate_key_pair();
    println!("Private_key: {:?}, Public_key: {:?}", private_key, public_key);
    // Повідомлення для підпису
    let message = b"Hello, ECDSA!";
    println!("{:?}", message.clone());
    // Підписуємо повідомлення
    let (r, s) = sign_message(&private_key, message);
    println!("Signed_message r: {}, s: {}", r, s);

    // Перевірка підпису
    let is_valid = verify_signature(&public_key, message, &r, &s);
    println!("Verify_signature: {}", is_valid);
}
