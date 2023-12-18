// BLS Native

use std::ops::{Add, Sub, Neg, Mul, Div};

use std::{str::FromStr, vec};


use num_bigint::{BigUint, BigInt, Sign, ToBigInt};

use crate::big_arithmetic::{big_add, big_less_than, self};

pub fn modulus() -> BigUint {
    BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787").unwrap()
}

pub fn modulus_digits() -> Vec<u32> {
    modulus().to_u32_digits()
}

pub fn get_bls_12_381_parameter() -> BigUint {
    BigUint::from_str("15132376222941642752").unwrap()
}

pub fn get_negate(y: &[u32; 12]) -> [u32; 12] {
    let y_bu = BigUint::new(y.to_vec());
    let neg = modulus() - y_bu;
    get_u32_vec_from_literal(neg)
}

pub fn get_g2_invert(z1: &[u32; 12], z2: &[u32; 12]) -> [[u32; 12]; 2] {
    let fp2 = Fp2([
        Fp(z1.clone()),
        Fp(z2.clone())
    ]);
    [fp2.invert().0[0].0, fp2.invert().0[1].0]
}

pub fn get_u32_carries(x: &[u32; 12], y: &[u32; 12]) -> [u32; 12] {
    let mut carries = [0u32; 12];
    let mut prev_carry = 0;
    for i in 0..12 {
        if i!=0{
            prev_carry = carries[i-1];
        }
        let z = (x[i] as u64 + y[i] as u64 + prev_carry as u64);
        println!("i-{:?}--x:: {:?}, y:: {:?}, z:: {:?}, carry:: {:?}",i,x[i], y[i], prev_carry,(z>>32) as u32);
        if i!=11
         {carries[i] = (z>>32) as u32 }
    }
    carries[11] = 0;
    carries
}


pub fn multiply_by_slice(x: &[u32; 12], y: u32) -> ([u32; 13],[u32; 12]) {
    let mut res: [u32; 13] = [0u32; 13];
    let mut carries: [u32; 12] = [0u32; 12];
    let mut prev_carry = 0;
    for i in 0..12 {
        let temp = (x[i] as u64 * y as u64) + prev_carry as u64;
        let temp_res = temp as u32;
        let new_carry = (temp>>32) as u32;
        prev_carry = new_carry;
        res[i] = temp_res;
        carries[i] = prev_carry;
    }
    res[12] = prev_carry;
    (res, carries)
}

pub fn add_u32_slices(x: &[u32; 24], y: &[u32; 24]) -> ([u32; 24], [u32; 24]) {
    let mut prev_carry = 0u32;
    let mut res = [0u32; 24];
    let mut carries = [0u32; 24];
    for i in 0..24 {
        let s = x[i] as u64 + y[i] as u64 + prev_carry as u64;
        let sum = s as u32;
        let carry = (s >> 32) as u32;
        prev_carry = carry;
        res[i] = sum;
        carries[i] = carry;
    }
    (res, carries)
}

pub fn add_u32_slices_12(x: &[u32; 12], y: &[u32; 12]) -> ([u32; 12], [u32; 12]) {
    let mut prev_carry = 0u32;
    let mut res = [0u32; 12];
    let mut carries = [0u32; 12];
    for i in 0..12 {
        let s = x[i] as u64 + y[i] as u64 + prev_carry as u64;
        let sum = s as u32;
        let carry = (s >> 32) as u32;
        prev_carry = carry;
        res[i] = sum;
        carries[i] = carry;
    }
    (res, carries)
}

// assume x > y
pub fn sub_u32_slices(x: &[u32; 24], y: &[u32; 24]) -> ([u32; 24], [u32; 24]) {
    let mut prev_borrow = 0u32;
    let mut res = [0u32; 24];
    let mut borrows = [0u32; 24];
    for i in 0..24 {
        if x[i] >= y[i] + prev_borrow {
            res[i] = x[i]-y[i]-prev_borrow;
            borrows[i] = 0;
            prev_borrow = 0;
        } else {
            res[i] = ((1u64 << 32) + x[i] as u64 - y[i] as u64 - prev_borrow as u64) as u32;
            borrows[i] = 1;
            prev_borrow = 1;
        }
    }
    (res, borrows)
}

// assume x > y
pub fn sub_u32_slices_12(x: &[u32; 12], y: &[u32; 12]) -> ([u32; 12], [u32; 12]) {
    let mut prev_borrow = 0u32;
    let mut res = [0u32; 12];
    let mut borrows = [0u32; 12];
    for i in 0..12 {
        if x[i] >= y[i] + prev_borrow {
            res[i] = x[i]-y[i]-prev_borrow;
            borrows[i] = 0;
            prev_borrow = 0;
        } else {
            res[i] = ((1u64 << 32) + x[i] as u64 - y[i] as u64 - prev_borrow as u64) as u32;
            borrows[i] = 1;
            prev_borrow = 1;
        }
    }
    assert_eq!(borrows[11], 0);
    (res, borrows)
}

pub fn get_bits_as_array(number: u32) -> [u32; 32] {
    let mut result = [0u32; 32]; // Assuming a u32 has 32 bits

    for i in 0..32 {
        // Shift the 1 bit to the rightmost position and perform bitwise AND
        result[i] = ((number >> i) & 1) as u32;
    }

    result
}

pub fn add_u32_slices_1(x: &[u32; 24], y: &[u32; 25]) -> ([u32; 25], [u32; 24]) {
    let mut x_padded = [0u32; 25];
    x_padded[0..24].copy_from_slice(x);
    let mut prev_carry = 0u32;
    let mut res = [0u32; 25];
    let mut carries = [0u32; 24];
    for i in 0..24 {
        let s = x[i] as u64 + y[i] as u64 + prev_carry as u64;
        let sum = s as u32;
        let carry = (s >> 32) as u32;
        prev_carry = carry;
        res[i] = sum;
        carries[i] = carry;
    }
    res[24] = prev_carry;
    (res, carries)
}

pub fn egcd(a: BigUint, b: BigUint) -> BigUint {
    // if a == BigUint::from(0 as u32){
    //     (b, BigUint::from(0 as u32), BigUint::from(1 as u32))
    // } else {
    //     let (g, y, x) = egcd(b.clone()%a.clone(), a.clone());
    //     (g, x - (b.clone()*(y.clone()/a.clone())), y)
    // }
    let mut a_ = BigInt::from_biguint(Sign::Plus, a);
    let mut b_ = BigInt::from_biguint(Sign::Plus, b);

    let mut x = BigInt::from_str("0").unwrap();
    let mut y = BigInt::from_str("1").unwrap();
    let mut u = BigInt::from_str("1").unwrap();
    let mut v = BigInt::from_str("0").unwrap();

    let zero = BigInt::from_str("0").unwrap();
    while a_ != zero {
        let q = b_.clone()/a_.clone();
        let r = b_%a_.clone();
        let m = x-(u.clone()*q.clone());
        let n = y-(v.clone()*q);
        b_ = a_;
        a_ = r;
        x = u;
        y = v;
        u = m;
        v = n;
    }
    // println!("x {:?}", x);
    let mod_bigint = modulus().to_bigint().unwrap();
    ((x%mod_bigint.clone())+mod_bigint).to_biguint().unwrap()
}

pub fn mod_inverse(a: BigUint, m: BigUint) -> BigUint {
    egcd(a, m.clone())
    // x % m
}

pub fn fp4_square(a: Fp2, b: Fp2) -> (Fp2, Fp2) {
    let a2 = a * a;
    let b2 = b * b;
    (
        b2.mul_by_nonresidue()+a2,
        ((a+b)*(a+b)) - a2 - b2
    )
}

pub fn get_u32_vec_from_literal(x: BigUint) -> [u32; 12] {
    let mut x_u32_vec: Vec<u32> = x.to_u32_digits();
    while x_u32_vec.len() != 12 {
        x_u32_vec.push(0 as u32);
    }
    x_u32_vec.try_into().unwrap()
}

pub fn get_selector_bits_from_u32(x: u32) -> [u32; 12] {
    // assert!(x<=4096);
    let mut res = [0u32; 12];
    let mut val = x.clone();
    for i in 0..12 {
        res[i] = (val&1);
        val = val >> 1;
    }
    res
}

pub fn get_u32_vec_from_literal_24(x: BigUint) -> [u32; 24] {
    let mut x_u32_vec: Vec<u32> = x.to_u32_digits();
    while x_u32_vec.len() != 24 {
        x_u32_vec.push(0 as u32);
    }
    x_u32_vec.try_into().unwrap()
}

pub fn get_div_rem_modulus_from_biguint_12(x: BigUint) -> ([u32; 12], [u32; 12]) {
    let rem = x.clone()%modulus();
    let div = x/modulus();
    (get_u32_vec_from_literal(div), get_u32_vec_from_literal(rem))
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Fp(pub(crate) [u32; 12]);

impl Fp {
    pub fn zero() -> Fp {
        Fp([0; 12])
    }
    
    pub fn one() -> Fp {
        let mut x = Fp([0; 12]);
        x.0[0] = 1;
        x
    }

    pub fn get_fp_from_biguint(x: BigUint) -> Fp {
        Fp(get_u32_vec_from_literal(x))
    }

    pub fn get_bitlen(&self) -> u64 {
        BigUint::new(self.0.try_into().unwrap()).bits()
    }

    pub fn get_bit(&self, idx: u64) -> bool {
        BigUint::new(self.0.try_into().unwrap()).bit(idx)
    }

    pub fn invert(&self) -> Self {
        let rhs_buint = BigUint::new(self.0.try_into().unwrap());
        let inv = mod_inverse(rhs_buint, modulus());
        // println!("inv {:?}", inv);
        Fp::get_fp_from_biguint(inv)
    }

    pub fn to_biguint(&self) -> BigUint {
        BigUint::new(self.0.to_vec())
    }
}

impl Div for Fp {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let rhs_buint = BigUint::new(rhs.0.try_into().unwrap());
        let inv = mod_inverse(rhs_buint, modulus());
        self * Fp::get_fp_from_biguint(inv)
    }
}

impl Add for Fp {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        add_fp(self, rhs)
    }
}

impl Mul for Fp {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        // let x_b = BigUint::new(self.0.try_into().unwrap());
        // let y_b = BigUint::new(rhs.0.try_into().unwrap());
        // let z = (x_b * y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
        // Fp(get_u32_vec_from_literal(z))
        mul_fp(self, rhs)
    }
}

impl Neg for Fp {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let X: BigUint = BigUint::new(self.0.try_into().unwrap());
        Fp(get_u32_vec_from_literal(modulus()-X))
    }
}



impl Sub for Fp {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        // let x_b = BigUint::new(self.0.try_into().unwrap());
        // let y_b = BigUint::new(rhs.0.try_into().unwrap());
        // let z = (x_b - y_b + modulus()).modpow(&BigUint::from_str("1").unwrap(), &modulus());
        // Fp(get_u32_vec_from_literal(z))
        sub_fp(self, rhs)
    }
}

pub fn add_fp(x: Fp, y: Fp) -> Fp {
    // let x_b = BigUint::new(x.0.try_into().unwrap());
    // let y_b = BigUint::new(y.0.try_into().unwrap());
    // let z = (x_b + y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    // Fp(get_u32_vec_from_literal(z))
    let x_plus_y = big_add(&x.0, &y.0);
    let mut m = modulus_digits();
    m.push(0);
    if big_less_than(&x_plus_y, &m) {
        Fp(x_plus_y[..12].try_into().unwrap())
    } else {
        let (x_plus_y_reduce, _) = big_arithmetic::big_sub(&x_plus_y, &m);
        Fp(x_plus_y_reduce[..12].try_into().unwrap())
    }
    // todo!()
}

pub fn add_fp_without_reduction(x: Fp, y: Fp) -> [u32; 12] {
    // let x_b = BigUint::new(x.0.try_into().unwrap());
    // let y_b = BigUint::new(y.0.try_into().unwrap());
    // let z = (x_b + y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    // Fp(get_u32_vec_from_literal(z))
    let x_plus_y = big_add(&x.0, &y.0);
    get_u32_vec_from_literal(BigUint::new(x_plus_y))
    // todo!()
}

pub fn mul_fp(x: Fp, y: Fp) -> Fp {
    //println!("sub_fp x{:?}, y{:?}", x, y);
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(y.0.try_into().unwrap());
    let z = (x_b * y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    //println!("z {:?} {:?}", z.to_u32_digits(), z.to_u32_digits().len());
    Fp(get_u32_vec_from_literal(z))
}

pub fn mul_fp_without_reduction(x: Fp, y: Fp) -> [u32; 24] {
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(y.0.try_into().unwrap());
    let z = x_b * y_b;
    get_u32_vec_from_literal_24(z)
}

pub fn negate_fp(x: Fp) -> Fp {
    let X: BigUint = BigUint::new(x.0.try_into().unwrap());
    Fp(get_u32_vec_from_literal(modulus()-X))
}

pub fn sub_fp(x: Fp, y: Fp) -> Fp {
    // println!("sub_fp x{:?}, y{:?}", x, y);
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(y.0.try_into().unwrap());
    let z = (modulus() + x_b - y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    // println!("sub_fp::{:?}-{:?}",z.to_u32_digits(), z.to_u32_digits().len());
    Fp(get_u32_vec_from_literal(z))
}

pub fn sum_of_products(a: Vec<Fp>, b: Vec<Fp>) -> Fp{
    let acc = a.iter().zip(b.iter()).fold(Fp([0; 12]),|acc, (a_i, b_i)| {
        add_fp(mul_fp(a_i.clone(), b_i.clone()), acc)
    });
    acc
}

#[derive(Clone, Copy, Debug)]
pub struct Fp2(pub(crate) [Fp; 2]);

impl Fp2 {
    pub fn zero() -> Fp2 {
        Fp2([Fp::zero(), Fp::zero()])
    }

    pub fn one() -> Fp2 {
        Fp2([Fp::one(), Fp::zero()])
    }

    pub fn non_residue() -> Fp {
        Fp::get_fp_from_biguint(modulus()-BigUint::from(1 as u32))
    }

    pub fn multiply_by_B(&self) -> Fp2 {
        let t0 = self.0[0].mul(Fp::get_fp_from_biguint(BigUint::from(4 as u32)));
        let t1 = self.0[1].mul(Fp::get_fp_from_biguint(BigUint::from(4 as u32)));
        Fp2([t0-t1, t0+t1])
    }

    pub fn mul_by_nonresidue(&self) -> Self {
        let c0 = self.0[0];
        let c1 = self.0[1];
        Fp2([c0-c1, c0+c1])
    }

    pub fn invert(&self) -> Self {
        let re = self.0[0];
        let im = self.0[1];
        let factor_fp = ((re * re) + (im * im));
        let factor = factor_fp.invert();
        Fp2([
            factor * re,
            factor * (-im)
        ])
    }

    pub fn to_biguint(&self) -> [BigUint; 2] {
        [
            BigUint::new(self.0[0].0.to_vec()),
            BigUint::new(self.0[1].0.to_vec()),
        ]
    }
}

impl Add for Fp2 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
       add_Fp2(self, rhs)
    }
}

impl Mul for Fp2 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
       mul_Fp2(self, rhs)
    }
}

impl Sub for Fp2 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        sub_Fp2(self, rhs)
    }
}

impl Mul<Fp> for Fp2 {
    type Output = Fp2;

    fn mul(self, rhs: Fp) -> Self::Output {
        let mut ans = Fp2::zero();
        let mut found_one = false;
        for i in (0..rhs.get_bitlen()).rev() {
            if found_one {
                ans = ans + ans;
            }
            let bit  = rhs.get_bit(i);
            if bit {
                found_one = true;
                ans = ans + self;
            }
        }
        ans
    }
}

impl Neg for Fp2 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Fp2([self.0[0].neg(), self.0[1].neg()])
    }
}

pub fn sub_Fp2(x: Fp2, y: Fp2) -> Fp2 {
    Fp2 ([sub_fp(x.0[0],y.0[0]),sub_fp(x.0[1],y.0[1])])
}

pub fn add_Fp2(x: Fp2, y: Fp2) -> Fp2 {
    Fp2 ([add_fp(x.0[0],y.0[0]),add_fp(x.0[1],y.0[1])])
}

pub fn mul_Fp2(x: Fp2, y: Fp2) -> Fp2 {
    //println!("x:: {:?}", x);
    //println!("y:: {:?}", y);
    let c0 = sub_fp(mul_fp(x.0[0], y.0[0]),mul_fp(x.0[1], y.0[1]));
    let c1 = add_fp(mul_fp(x.0[0], y.0[1]),mul_fp(x.0[1], y.0[0]));
    Fp2 (
        [c0, c1]
    )
}

// pub fn mul_fp2_without_reduction(x: Fp2, y: Fp2) -> Fp2 {

// }

#[derive(Clone, Copy, Debug)]
pub struct Fp6([Fp;6]);

impl Fp6 {
    pub fn invert(&self) -> Self {
        let c0c1c2 = self;
        let c0 = Fp2(c0c1c2.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(c0c1c2.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(c0c1c2.0[4..6].to_vec().try_into().unwrap());
        let t0 = (c0 * c0) - (c2 * c1).mul_by_nonresidue();
        let t1 = (c2 * c2).mul_by_nonresidue() - (c0 * c1);
        let t2 = (c1 * c1) - (c0 * c2);
        let t4 = (((c2 * t1) + (c1 * t2)).mul_by_nonresidue() + (c0 * t0)).invert();
        Fp6([
            (t4*t0).0,
            (t4 * t1).0,
            (t4 * t2).0,
        ].concat().try_into().unwrap())
    }

    pub fn print(&self) {
        // println!("--- Printing Fp6 ---");
        // for i in 0..self.0.len() {
        //     let fp = Fp::get_fp_from_biguint(BigUint::new(self.0[i].0.to_vec()));
        //     println!("i -- {:?}",fp.to_biguint());
        // }
        // println!("--- Printed Fp6 ---");
    }
}

impl Add for Fp6 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        add_Fp6(self, rhs)
    }
}

impl Sub for Fp6 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        sub_Fp6(self, rhs)
    }
}

impl Div for Fp6 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.invert()
    }
}

impl Mul for Fp6 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        mul_Fp6(self, rhs)
    }
}

impl Neg for Fp6 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let c0c1c2 = self;
        let c0 = Fp2(c0c1c2.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(c0c1c2.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(c0c1c2.0[4..6].to_vec().try_into().unwrap());
        Fp6([
            c0.neg().0,
            c1.neg().0,
            c2.neg().0,
        ].concat().try_into().unwrap())
    }
}

pub fn add_Fp6(x: Fp6, y: Fp6) -> Fp6 {
    let X = x.0;
    let Y = y.0;
    Fp6([
        add_fp(X[0],Y[0]), 
        add_fp(X[1],Y[1]), 
        add_fp(X[2],Y[2]), 
        add_fp(X[3],Y[3]), 
        add_fp(X[4],Y[4]), 
        add_fp(X[5],Y[5]), 
    ])
}

pub fn sub_Fp6(x: Fp6, y: Fp6) -> Fp6 {
    let X = x.0;
    let Y = y.0;
    Fp6([
        sub_fp(X[0],Y[0]), 
        sub_fp(X[1],Y[1]), 
        sub_fp(X[2],Y[2]), 
        sub_fp(X[3],Y[3]), 
        sub_fp(X[4],Y[4]), 
        sub_fp(X[5],Y[5]), 
    ])
}
/*
Fp6 -> Fp2(c0), c1, c2

    [c0.c0, c0.c1, c1.c0, c1.c1, c2.c0, c2.c1]
 */
pub fn mul_Fp6(x: Fp6, y: Fp6) -> Fp6 {
    let X = x.0;
    let Y = y.0;

    let b10_p_b11 = add_fp(Y[2],Y[3]);//b.c1.c0 + b.c1.c1;
    let b10_m_b11 = sub_fp(Y[2], Y[3]);//b.c1.c0 - b.c1.c1;
    let b20_p_b21 = add_fp(Y[4], Y[5]);//b.c2.c0 + b.c2.c1;
    let b20_m_b21 = sub_fp(Y[4], Y[5]);
    Fp6([
        sum_of_products(
            vec![X[0], negate_fp(X[1]), X[2], negate_fp(X[3]), X[4], negate_fp(X[5])],
            vec![Y[0], Y[1], b20_m_b21, b20_p_b21, b10_m_b11, b10_p_b11],
        ),
        sum_of_products(
            vec![X[0], X[1], X[2], X[3], X[4], X[5]],
            vec![Y[1], Y[0], b20_p_b21, b20_m_b21, b10_p_b11, b10_m_b11],
        ),
        sum_of_products(
            vec![X[0], negate_fp(X[1]), X[2], negate_fp(X[3]), X[4], negate_fp(X[5])],
            vec![Y[2], Y[3], Y[0], Y[1], b20_m_b21, b20_p_b21],
        ),
        sum_of_products(
            vec![X[0], X[1], X[2], X[3], X[4], X[5]],
            vec![Y[3], Y[2], Y[1], Y[0], b20_p_b21, b20_m_b21],
        ),
        sum_of_products(
            vec![X[0], negate_fp(X[1]), X[2], negate_fp(X[3]), X[4], negate_fp(X[5])],
            vec![Y[4], Y[5], Y[2], Y[3], Y[0], Y[1]],
        ),
        sum_of_products(
            vec![X[0], X[1], X[2], X[3], X[4], X[5]],
            vec![Y[5], Y[4], Y[3], Y[2], Y[1], Y[0]],
        ),
    ])
}

pub fn mul_by_nonresidue(x: [Fp; 6]) -> Fp6 {
    let mut ans: [Fp; 6] = [Fp::zero(); 6];
    ans[2] = x[0];
    ans[3] = x[1];
    ans[4] = x[2];
    ans[5] = x[3];
    ans[0] = sub_fp(x[4], x[5]);
    ans[1] = add_fp(x[4], x[5]);
    Fp6(ans)
}

impl Fp6 {
    pub fn multiplyBy01(&self, b0: Fp2, b1: Fp2) -> Self {
        let c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());
        let t0 = c0 * b0;
        let t1 = c1 * b1;
        let ans1 = ((c1 + c2) * b1 - t1).mul_by_nonresidue() + t0;  
        let ans2 = (b0 + b1) * (c0 + c1) - t0 - t1;
        let ans3 = (c0 + c2) * b0 - t0 + t1;
        Fp6([
            ans1.0, ans2.0, ans3.0
        ].concat().try_into().unwrap())
    }

    pub fn multiplyBy1(&self, b1: Fp2) -> Self {
        let c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());
        Fp6([
            (c2*b1).mul_by_nonresidue().0,
            (c0*b1).0,
            (c1*b1).0,
        ].concat().try_into().unwrap())
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Fp12([Fp; 12]);

impl Fp12 {
    pub fn one() -> Fp12 {
        let mut x = [Fp::zero(); 12];
        x[0] = Fp::one();
        Fp12(x)
    }

    pub fn invert(&self) -> Self {
        let c0 = Fp6(self.0[0..6].try_into().unwrap());
        let c1 = Fp6(self.0[6..12].try_into().unwrap());
        let t = (c0 * c0 - mul_by_nonresidue((c1*c1).0)).invert();
        Fp12([
            (c0*t).0,
            (-(c1*t)).0,
        ].concat().try_into().unwrap())
    }

    pub fn print(&self) {
        // println!("--- Printing Fp12 ---");
        // for i in 0..self.0.len() {
        //     let fp = Fp::get_fp_from_biguint(BigUint::new(self.0[i].0.to_vec()));
        //     println!("i -- {:?}",fp.to_biguint());
        // }
        // println!("--- Printed Fp12 ---");
    }

    pub fn from_str(x: [&str; 12]) -> Self {
        let mut ans: Fp12 = Fp12::one();
        for i in 0..12 {
            let bu = Fp::get_fp_from_biguint(BigUint::from_str(x[i]).unwrap());
            ans.0[i] = bu;
        }
        ans
    }
}

impl Add for Fp12 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        add_fp12(self, rhs)
    }
}

impl Sub for Fp12 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl Mul for Fp12 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        mul_fp_12(self, rhs)
    }
}

impl Div for Fp12 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.invert()
    }
}

impl Neg for Fp12 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        todo!()
    }
}

// impl Debug for Fp12 {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.debug_tuple("Fp12").field(&self.0).finish()
//     }
// }

pub fn add_fp12(x: Fp12, y: Fp12) -> Fp12 {
    let mut ans: [Fp; 12] = [Fp::zero(); 12];
    for i in 0..12 {
        ans[i] = add_fp(x.0[i], y.0[i]);
    }
    Fp12(ans)
}

pub fn mul_fp_12(x: Fp12, y: Fp12) -> Fp12 {
    let x_c0 = Fp6(x.0[0..6].to_vec().try_into().unwrap());
    let x_c1 = Fp6(x.0[6..12].to_vec().try_into().unwrap());
    let y_c0 = Fp6(y.0[0..6].to_vec().try_into().unwrap());
    let y_c1 = Fp6(y.0[6..12].to_vec().try_into().unwrap());

    let aa = mul_Fp6(x_c0 , y_c0);
    let bb = mul_Fp6(x_c1,y_c1);
    let o =add_Fp6(y_c0 ,y_c1);
    let c1 = add_Fp6(x_c1 , x_c0);
    let c1 = mul_Fp6(c1 ,o);
    let c1 = sub_Fp6(c1, aa);
    let c1 = sub_Fp6(c1,bb);
    let c0 = mul_by_nonresidue(bb.0);
    let c0 = add_Fp6(c0 , aa);

    Fp12(
        [
            c0.0[0], c0.0[1], c0.0[2], c0.0[3], c0.0[4], c0.0[5],
            c1.0[0], c1.0[1], c1.0[2], c1.0[3], c1.0[4], c1.0[5]
        ]
    )
}

impl Fp2 {
    pub fn forbenius_map(&self, pow: usize) -> Self {
        let constants = [
            Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786").unwrap()),
        ];
        Fp2([
            self.0[0],
            self.0[1]*constants[pow%2]
        ])
    }
}

impl Fp6 {
    pub fn forbenius_map(&self, pow: usize) -> Self {
        // println!("--- fp6 forbenius map ---");
        let FP6_FROBENIUS_COEFFICIENTS_1 = [
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()),
            ]),
        ];

        let FP6_FROBENIUS_COEFFICIENTS_2 = [
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351").unwrap()),
            ]),
        ];
        self.print();
        let c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        // println!("c0 {:?}", c0.to_biguint());
        let c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        // println!("c1 {:?}", c0.to_biguint());
        let c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());
        // println!("c2 {:?}", c0.to_biguint());
        // println!("--- fp6 forbenius map ---");
        Fp6([
            c0.forbenius_map(pow).0,
            (c1.forbenius_map(pow) * FP6_FROBENIUS_COEFFICIENTS_1[pow%6]).0,
            (c2.forbenius_map(pow) * FP6_FROBENIUS_COEFFICIENTS_2[pow%6]).0,
        ].concat().try_into().unwrap())
    }
}

impl Fp12 {
    pub fn forbenius_map(&self, pow: usize) -> Self {
        // println!(" ---- forbenius - map -----");
        let FP12_FORBENIUS_COEFFICIENTS = [
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620351").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("793479390729215512621379701633421447060886740281060493010456487427281649075476305620758731620350").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559786").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("151655185184498381465642749684540099398075398968325446656007613510403227271200139370504932015952886146304766135027").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("3850754370037169011952147076051364057158807420970682438676050522613628423219637725072182697113062777891589506424760").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939436").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("2973677408986561043442465346520108879172042883009249989176415018091420807192182638567116318576472649347015917690530").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("4002409555221667392624310435006688643935503118305586438271171395842971157480381377015405980053539358417135540939437").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("877076961050607968509681729531255177986764537961432449499635504522207616027455086505066378536590128544573588734230").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("3125332594171059424908108096204648978570118281977575435832422631601824034463382777937621250592425535493320683825557").unwrap()),
            ]),
        ];
        let r0 = Fp6(self.0[0..6].to_vec().try_into().unwrap()).forbenius_map(pow);
        r0.print();
        let c0c1c2 = Fp6(self.0[6..12].to_vec().try_into().unwrap()).forbenius_map(pow);
        c0c1c2.print();
        let c0 = Fp2(c0c1c2.0[0..2].to_vec().try_into().unwrap());
        // println!("c0 - {:?}", c0.to_biguint());
        let c1 = Fp2(c0c1c2.0[2..4].to_vec().try_into().unwrap());
        // println!("c1 - {:?}", c1.to_biguint());
        let c2 = Fp2(c0c1c2.0[4..6].to_vec().try_into().unwrap());
        // println!("c2 - {:?}", c2.to_biguint());
        let coeff = FP12_FORBENIUS_COEFFICIENTS[pow % 12];
        // println!("coeff - {:?}", coeff.to_biguint());
        Fp12([
            r0.0,
            [(c0*coeff).0, (c1*coeff).0, (c2*coeff).0].concat().try_into().unwrap()
        ].concat().try_into().unwrap())

    }
}

impl Fp12 {
    pub fn multiplyBy014(&self, o0: Fp2, o1: Fp2, o4: Fp2) -> Self {
        let c0 = Fp6(self.0[0..6].to_vec().try_into().unwrap());
        let c1 = Fp6(self.0[6..12].to_vec().try_into().unwrap());
        let t0 = c0.multiplyBy01(o0, o1);
        let t1 = c1.multiplyBy1(o4);
        let a = add_Fp6(mul_by_nonresidue(t1.0),t0);
        // (c1 + c0) * [o0, o1+o4] - T0 - T1
        let b = sub_Fp6(sub_Fp6(add_Fp6(c1, c0).multiplyBy01(o0, o1+o4),t0),t1);
        Fp12([
            a.0,b.0
        ].concat().try_into().unwrap())
    }

    pub fn conjugate(&self) -> Self {
        let mut x = self.0.clone();
        for i in 6..12 {
            x[i] = -x[i];
        }
        Fp12((x))
    }

    pub fn cyclotomicSquare(&self) -> Self {
        let two = Fp::get_fp_from_biguint(BigUint::from(2 as u32));

        let c0c0 = Fp2(self.0[0..2].try_into().unwrap());
        let c0c1 = Fp2(self.0[2..4].try_into().unwrap());
        let c0c2 = Fp2(self.0[4..6].try_into().unwrap());
        let c1c0 = Fp2(self.0[6..8].try_into().unwrap());
        let c1c1 = Fp2(self.0[8..10].try_into().unwrap());
        let c1c2 = Fp2(self.0[10..12].try_into().unwrap());

        let (t3, t4)  = fp4_square(c0c0, c1c1);
        let (t5, t6)  = fp4_square(c1c0, c0c2);
        let (t7, t8)  = fp4_square(c0c1, c1c2);

        let t9 = t8.mul_by_nonresidue();

        Fp12(
            [
                (((t3 - c0c0) * two) + t3).0,
                (((t5 - c0c1) * two) + t5).0,
                (((t7 - c0c2) * two) + t7).0,
                (((t9 + c1c0) * two) + t9).0,
                (((t4 + c1c1) * two) + t4).0,
                (((t6 + c1c2) * two) + t6).0,
                
            ].concat().try_into().unwrap()
        )
    }

    pub fn cyclotocmicExponent(&self) -> Fp12 {
        let mut z = Fp12::one();
        for i in (0..get_bls_12_381_parameter().bits()).rev() {
            z = z.cyclotomicSquare();
            if get_bls_12_381_parameter().bit(i) {
                z = z * self.clone();
            }
        }
        z
    }

    pub fn final_exponentiate(&self) -> Self{
        println!("master self");
        self.print();
        let t0 = self.forbenius_map(6) / self.clone();
        println!("--- t0 ---");
        t0.print();
        let t1 = t0.forbenius_map(2) * t0;
        //println!("--- t1 ---");
        t1.print();
        let t2 = t1.cyclotocmicExponent().conjugate();
        //println!("--- t2 ---");
        t2.print();
        let t3 = t1.cyclotomicSquare().conjugate() * t2;
        //println!("--- t3 ---");
        t3.print();
        let t4 = t3.cyclotocmicExponent().conjugate();
        //println!("--- t4 ---");
        t4.print();
        let t5 = t4.cyclotocmicExponent().conjugate();
        //println!("--- t5 ---");
        t5.print();
        let t6 = t5.cyclotocmicExponent().conjugate() * t2.cyclotomicSquare();
        //println!("--- t6 ---");
        t6.print();
        let t7 = t6.cyclotocmicExponent().conjugate();
        //println!("--- t7 ---");
        t7.print();
        let t2_t5_pow_q2 = (t2*t5).forbenius_map(2);
        //println!("--- t2_t5_pow_q2 ---");
        t2_t5_pow_q2.print();
        let t4_t1_pow_q3 = (t4*t1).forbenius_map(3);
        //println!("--- t4_t1_pow_q3 ---");
        t4_t1_pow_q3.print();
        let t6_t1c_pow_q1 = (t6*t1.conjugate()).forbenius_map(1);
        //println!("--- t6_t1c_pow_q1 ---");
        t6_t1c_pow_q1.print();
        let t7_t3c_t1 = (t7*t3.conjugate())*(t1);
        //println!("--- t7_t3c_t1 ---");
        t7_t3c_t1.print();
        // (t2 * t5)^(q²) * (t4 * t1)^(q³) * (t6 * t1.conj)^(q^1) * t7 * t3.conj * t1
        return t2_t5_pow_q2*t4_t1_pow_q3*t6_t1c_pow_q1*t7_t3c_t1
    }
}


pub fn inverse_fp2(x: Fp2) -> Fp2 {
    let t0 = x.0[0] * x.0[0];
    let t1 = x.0[1] * x.0[1];
    let t2 = t0 - (t1 * Fp2::non_residue());
    let t3 = Fp::one()/t2;
    Fp2([x.0[0]*t3, -(x.0[1]*t3)])
}


pub fn calc_pairing_precomp(x: Fp2, y: Fp2, z: Fp2) -> Vec<[Fp2; 3]> {
    //println!("z_invert {:?}", z.invert());
    let ax = x*(z.invert());
    let ay = y*(z.invert());

    let Qx = ax.clone();
    let Qy = ay.clone();
    let Qz = Fp2::one();

    let mut Rx = Qx.clone();
    let mut Ry = Qy.clone();
    let mut Rz = Qz.clone();

    let mut ell_coeff: Vec<[Fp2; 3]> = Vec::<[Fp2; 3]>::new();

    for i in (0..get_bls_12_381_parameter().bits()-1).rev() {
        //println!("i -- {:?}", i);
        // println!("Rx {:?}", Rx.to_biguint());
        // println!("Ry {:?}", Ry.to_biguint());
        // println!("Rz {:?}", Rz.to_biguint());
        let t0 = Ry * Ry;
        // println!("t0 {:?}", t0.to_biguint());
        let t1 = Rz * Rz;
        // println!("t1 {:?}", t1.to_biguint());
        let t2 = t1.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32))).multiply_by_B();
        // println!("t2 {:?}", t2.to_biguint());
        let t3 = t2.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32)));
        // println!("t3 {:?}", t3.to_biguint());
        let t4 = Ry*Ry + Rz*Rz + (Ry * Rz).mul(Fp::get_fp_from_biguint(BigUint::from(2 as u32)))-t1-t0;
        // println!("t4 {:?}", t4.to_biguint());
        ell_coeff.push(
            [t2-t0, (Rx*Rx).mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32))), -t4]
        );
        // println!("ell_coeff_0_0 {:?}", ell_coeff[0][0].to_biguint());
        // println!("ell_coeff_0_1 {:?}", ell_coeff[0][1].to_biguint());
        // println!("ell_coeff_0_2 {:?}", ell_coeff[0][2].to_biguint());
        Rx = (t0 - t3)*Rx*Ry*Fp::get_fp_from_biguint(mod_inverse(BigUint::from(2 as u32), modulus()));
        Ry = 
        ((t0+t3)*Fp::get_fp_from_biguint(mod_inverse(BigUint::from(2 as u32), modulus()))) * 
        ((t0+t3)*Fp::get_fp_from_biguint(mod_inverse(BigUint::from(2 as u32), modulus()))) - 
        t2*t2*Fp::get_fp_from_biguint(BigUint::from(3 as u32));
        Rz = t0 * t4;
        // println!("Rx_ {:?}", Rx.to_biguint());
        // println!("Ry_ {:?}", Ry.to_biguint());
        // println!("Rz_ {:?}", Rz.to_biguint());
        if get_bls_12_381_parameter().bit(i) {
            let t0 = Ry - (Qy * Rz);
            // println!("t0__ {:?}", t0.to_biguint());
            let t1 = Rx - (Qx * Rz);
            // println!("t1__ {:?}", t1.to_biguint());
            ell_coeff.push([
                (t0 * Qx) - (t1 * Qy),
                -t0,
                t1
            ]);
            // println!("ell_coeff_1_0 {:?}", ell_coeff[1][0].to_biguint());
            // println!("ell_coeff_1_1 {:?}", ell_coeff[1][1].to_biguint());
            // println!("ell_coeff_1_2 {:?}", ell_coeff[1][2].to_biguint());
            let t2 = t1*t1;
            // println!("t2__ {:?}", t2.to_biguint());
            let t3 = t2 * t1;
            // println!("t3__ {:?}", t3.to_biguint());
            let t4 = t2* Rx;
            // println!("t4__ {:?}", t4.to_biguint());
            let t5 = t3 - (t4 * Fp::get_fp_from_biguint(BigUint::from(2 as u32))) + (t0 * t0 * Rz);
            // println!("t5__ {:?}", t5.to_biguint());
            Rx = t1 * t5;
            Ry = (t4 - t5) * t0 - (t3 * Ry);
            Rz = Rz * t3;
            // println!("Rx__ {:?}", Rx.to_biguint());
            // println!("Ry__ {:?}", Ry.to_biguint());
            // println!("Rz__ {:?}", Rz.to_biguint());
        }
        // println!("len --{:?}", ell_coeff.len());
    }
    return ell_coeff;
}


pub fn miller_loop(g1_x: Fp, g1_y: Fp, g2_x: Fp2, g2_y: Fp2, g2_z: Fp2) -> Fp12 {
    let precomputes = calc_pairing_precomp(g2_x, g2_y, g2_z);
    // for i in 0..precomputes.len() {
    //     println!("{:?} ----", i);
    //     println!("precomputes calculated 1 - {:?}", precomputes[i][0].to_biguint());
    //     println!("precomputes calculated 2 - {:?}", precomputes[i][1].to_biguint());
    //     println!("precomputes calculated 3 - {:?}", precomputes[i][2].to_biguint());
    // }
    // return Fp12::one();
    let Px = g1_x.clone();
    let Py = g1_y.clone();
    let mut f12 = Fp12::one();
    let mut j = 0;

    for i in (0..get_bls_12_381_parameter().bits()-1).rev() {
        println!("i -- {:?}", i);
        let E = precomputes[j];
        f12 = f12.multiplyBy014(E[0], E[1]*Px, E[2]*Py);
        if get_bls_12_381_parameter().bit(i) {
            j += 1;
            let F = precomputes[j];
            f12 = f12.multiplyBy014(F[0], F[1]*Px, F[2]*Py);
        }
        if i!=0{
            f12 = mul_fp_12(f12,f12);
        }
        j+=1;
    }
    f12.conjugate()
}

pub fn pairing(p_x: Fp, p_y: Fp, q_x: Fp2, q_y: Fp2, q_z: Fp2) -> Fp12 {
    let looped = miller_loop(p_x, p_y, q_x, q_y, q_z);
    looped
    // looped.final_exponentiate()
}

pub fn mod_sub(a: u32, b: u32) -> (u32, bool) {
    let mut borrow = false;
    if a<b {
        borrow = true;
    }
    let mut ans;
    if borrow {
       ans = ((borrow as u64) * (1u64 << 32) + (a as u64) - (b as u64)) as u32;
    } else {
       ans = a - b;
    }
    (ans, borrow)
}

// [TODO] handle case for when a[i] is 0 to begin with, might fuck up carries
pub fn big_sub(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    assert_eq!(a.len(), 12);
    assert_eq!(b.len(), 12);
    let mut result = Vec::<u32>::new();
    // Assuming a > b
    let (mut borrow, mut is_borrow) = mod_sub(a[0],b[0]);
    result.push(borrow);
    for i in 1..12  {
        if is_borrow {
            (borrow, is_borrow) = mod_sub(a[i]-1, b[i]);
        }else {
            (borrow, is_borrow) = mod_sub(a[i], b[i]);
        }
        result.push(borrow);
    }
    result
}


pub fn verify_bls_signatures() -> bool {
    // Public key
    // Splits into little endian
    let pk_x = BigUint::from_str("1216495682195235861952885506871698490232894470117269383940381148575524314493849307811227440691167647909822763414941").unwrap().to_u32_digits();
    let pk_y = BigUint::from_str("2153848155426317245700560287567131132765685008362732985860101000686875894603366983854567186180519945327668975076337").unwrap().to_u32_digits();
    let pk_z = BigUint::from_str("1").unwrap().to_u32_digits();
    // Hashed message in g2
    let Hm_x_1 = BigUint::from_str("2640504383352253166624742184946918613522392710628037055952404127879364455194422343335555527925815834654853618706317").unwrap().to_u32_digits();
    let Hm_x_2 = BigUint::from_str("3512267754584411844719003222712149130451230828216813699108449950001725181635151866954918805409098715392393669496763").unwrap().to_u32_digits();
    let Hm_y_1 = BigUint::from_str("1819141142055458317635768413798746444112487913647217792452244858223746035103974374419118545961357374373926748974853").unwrap().to_u32_digits();
    let Hm_y_2 = BigUint::from_str("2023172707753915325613231249141956147838197708174300845595677034762003254300804275953249871078804883738174492552197").unwrap().to_u32_digits();
    let Hm_z_1 = BigUint::from_str("2090317837686632453881173016321367129380434356038329533464948735487686003804511165163385664859654015333500347340874").unwrap().to_u32_digits();
    let Hm_z_2 = BigUint::from_str("3589273988676721566549754197317344469206294207551897598521700599244392528027952567094835689880190836504376087662460").unwrap().to_u32_digits();
    println!("pk_x::{:?}\npk_y::{:?}\nhm_x_1::{:?}\nhm_x_2::{:?}\nhm_y_1::{:?}\nhm_y_2::{:?}\nhm_z_1::{:?}\nhm_z_2::{:?}\n", pk_x, pk_y, Hm_x_1, Hm_x_2, Hm_y_1, Hm_y_2, Hm_z_1, Hm_z_2);
    // Generator
    let G_x = BigUint::from_str("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507").unwrap().to_u32_digits();
    let G_y = BigUint::from_str("1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569").unwrap().to_u32_digits();
    let G_z =  BigUint::from_str("1").unwrap().to_u32_digits();
    // Signature
    let S_x_1 = BigUint::from_str("2623971017592927791661443929103810896934774536775525535423614243457684905034147949323467412106133456094022067726851").unwrap().to_u32_digits();
    let S_x_2 = BigUint::from_str("2791552278788393998835490815906332650385266234676766868498515429583366873304026057923442494886948609285829286788356").unwrap().to_u32_digits();
    let S_y_1 = BigUint::from_str("1392880899106984160179818268515214962705329372907929072981217458923190202387659009520579695608141992620405977748755").unwrap().to_u32_digits();
    let S_y_2 = BigUint::from_str("2607207514294746608778464853061537277878553458184247374568293197687045701239874275081091959210122811260239467513958").unwrap().to_u32_digits();
    let S_z_1 = BigUint::from_str("1").unwrap().to_u32_digits();
    let S_z_2 = BigUint::from_str("0").unwrap().to_u32_digits();

    let bls_12_381_prime = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787").unwrap().to_u32_digits();

    // 1. negate Signature
    let pk_x_negate = pk_x.clone();
    let pk_y_negate = (modulus()-BigUint::new(pk_y)).to_u32_digits();
    let pk_z_negate = pk_z.clone();

    let pk_x_neg_fp = Fp::get_fp_from_biguint(BigUint::new(pk_x_negate));
    let pk_y_neg_fp = Fp::get_fp_from_biguint(BigUint::new(pk_y_negate));

    let hmx_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(Hm_x_1)), Fp::get_fp_from_biguint(BigUint::new(Hm_x_2))]);
    let hmy_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(Hm_y_1)), Fp::get_fp_from_biguint(BigUint::new(Hm_y_2))]);
    let hmz_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(Hm_z_1)), Fp::get_fp_from_biguint(BigUint::new(Hm_z_2))]);


    let sx_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(S_x_1)), Fp::get_fp_from_biguint(BigUint::new(S_x_2))]);
    let sy_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(S_y_1)), Fp::get_fp_from_biguint(BigUint::new(S_y_2))]);
    let sz_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(S_z_1)), Fp::get_fp_from_biguint(BigUint::new(S_z_2))]);

    let g_x = Fp::get_fp_from_biguint(BigUint::new(G_x));
    let g_y = Fp::get_fp_from_biguint(BigUint::new(G_y));
    // 2. P(pk_negate, Hm)
    let ePHm = pairing(pk_x_neg_fp, pk_y_neg_fp, hmx_fp2, hmy_fp2, hmz_fp2);
    ePHm.print();
    println!("ePHm::{:?}", ePHm);
    let eGS = pairing(g_x, g_y, sx_fp2, sy_fp2, sz_fp2);
    eGS.print();

    let mu = ePHm * eGS;
    mu.print();

    let mu_finaexp = mu.final_exponentiate();

    mu_finaexp.print();

    mu_finaexp == Fp12::one()
    // true
}

#[cfg(test)]   
mod tests {
    use std::str::FromStr;

    use hex::FromHex;
    use num_bigint::BigUint;

    use crate::native::{big_sub, sub_u32_slices_12};

    use super::{verify_bls_signatures, Fp, Fp12, modulus, sub_u32_slices, get_u32_vec_from_literal};

    #[test]
    pub fn test1() {
        assert!(verify_bls_signatures());
        // let x = Fp([0;12]);
        // println!("{:?}", x.get_bit(0));
        // let x: [u32; 12]=[1046962272, 2463794046, 2040554344, 1512106597, 3133001559, 2627724492, 2495709060, 1987230313, 1633322861, 1987308329, 3160603554, 114863259];
        // let x_bu = BigUint::new(x.to_vec());
        // println!("{:?}",x_bu);
    }

    #[test]
    pub fn test_final_exponentiate() {
        let aa = ["2181142506194812233868097821779361009807326315828153071050324314717744521676711650071190927260282422014627435089208",
            "3266212670671256779826008414922395966600400122723332695666308996296105595418386213353825620535446475769829785237189",
            "3280330655787598118299804758957910379684134784964426565939861302675766948066521588562898980898245868682162153155911",
            "333668007718210311816046938245689395232794221928183840372182128979685996722059498232053963662509478803385469716056",
            "1650925102445293819378017648160637800280351377141029658990698964033732511884552459036333864590686008335846481856882",
            "3925133212240632255860280854235945320282874550806663137653784505923891479863770370026712801361887427462376126696706",
            "2444089052091192833501409081021321360112867893942837175254954622703299880931587618210267154453853513743076365662283",
            "3142914221549818039420055870398197863502329018278548609868118001898418737390067291084903575823960349378631910285921",
            "1952057563719092278028425573632201081234877258097927010867141683896274170520489868686437644804596724295624637397077",
            "254131389529427774765960554324483250584297364987873642087841623909520980093766889928789173976296059957431962608694",
            "1385128161651935856764061834929068245137081648283968377947672499160305921464670953157912428887005620142387465559867",
            "101302147352745188522496764263445345397483945567997375025250825330209385517139484882425580831299520200841767383756"];


        let aa_fp12 = Fp12::from_str(aa);
        let mu_finaexp = aa_fp12.final_exponentiate();
        mu_finaexp.print();
        assert_eq!(mu_finaexp, Fp12::one())
    }

    // #[test]
    // pub fn test_big_sum() {
    //     let pk_x = BigUint::from_str("3071902358779104425805220059913391042958977442368743450008922736970201383908820407429457646333339330346464018568299").unwrap();
    //     let pk_x_u32 = pk_x.to_u32_digits();
    //     let S_x_1 = BigUint::from_str("966572263166434944599183957482752531047038993953916430862595578899059824912156165297149403978420723932172123775406").unwrap();
    //     let S_x_1_u32 = S_x_1.to_u32_digits();
    //     let res = big_sub(pk_x_u32, S_x_1_u32);
    //     assert_eq!(BigUint::new(res), pk_x-S_x_1);
    // }
    #[test]
    fn test_subu32() {
        let x: BigUint = BigUint::from_str("1").unwrap() << 381;
        let y = modulus();
        let x_u32 = get_u32_vec_from_literal(x.clone());
        let y_u32 = get_u32_vec_from_literal(y.clone());
        let (res, _carries) = sub_u32_slices_12(&x_u32, &y_u32);
        assert_eq!( x-y, BigUint::new(res.to_vec()));
    }
}
