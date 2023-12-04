// BLS Native

use std::ops::{Add, Sub, Neg, Mul, Div};

use std::{str::FromStr, vec};

use hex::FromHex;

use num_bigint::BigUint;

pub fn modulus() -> BigUint {
    BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787").unwrap()
}

pub fn get_bls_12_381_parameter() -> BigUint {
    BigUint::from_str("15132376222941642752").unwrap()
}

pub fn egcd(a: BigUint, b: BigUint) -> (BigUint, BigUint, BigUint) {
    if a == BigUint::from(0 as u32){
        (b, BigUint::from(0 as u32), BigUint::from(1 as u32))
    } else {
        let (g, y, x) = egcd(b.clone()%a.clone(), a.clone());
        (g, x - (b.clone()*(y.clone()/a.clone())), y)
    }
}

pub fn mod_inverse(a: BigUint, m: BigUint) -> BigUint {
    let (g, x, y) = egcd(a, m.clone());
    x % m
}

pub fn fp4_square(a: Fp2, b: Fp2) -> (Fp2, Fp2) {
    let a2 = a * a;
    let b2 = b * b;
    (
        b2.mul_by_nonresidue()+a2,
        ((a+b)*(a+b)) - a2 - b2
    )
}

#[derive(Clone, Copy, Debug)]
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
        Fp(x.to_u32_digits().try_into().unwrap())
    }

    pub fn get_bitlen(&self) -> u64 {
        BigUint::new(self.0.try_into().unwrap()).bits()
    }

    pub fn get_bit(&self, idx: u64) -> bool {
        BigUint::new(self.0.try_into().unwrap()).bit(idx)
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
        let x_b = BigUint::new(self.0.try_into().unwrap());
        let y_b = BigUint::new(rhs.0.try_into().unwrap());
        let z = (x_b + y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
        Fp(z.to_u32_digits().try_into().unwrap())
    }
}

impl Mul for Fp {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let x_b = BigUint::new(self.0.try_into().unwrap());
        let y_b = BigUint::new(rhs.0.try_into().unwrap());
        let z = (x_b * y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
        Fp(z.to_u32_digits().try_into().unwrap())
    }
}

impl Neg for Fp {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let X: BigUint = BigUint::new(self.0.try_into().unwrap());
        Fp((modulus()-X).to_u32_digits().try_into().unwrap())
    }
}



impl Sub for Fp {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let x_b = BigUint::new(self.0.try_into().unwrap());
        let y_b = BigUint::new(rhs.0.try_into().unwrap());
        let z = (x_b - y_b + modulus()).modpow(&BigUint::from_str("1").unwrap(), &modulus());
        Fp(z.to_u32_digits().try_into().unwrap())
    }
}

pub fn add_fp(x: Fp, y: Fp) -> Fp {
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(y.0.try_into().unwrap());
    let z = (x_b + y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    Fp(z.to_u32_digits().try_into().unwrap())
}

pub fn mul_fp(x: Fp, y: Fp) -> Fp {
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(x.0.try_into().unwrap());
    let z = (x_b * y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    Fp(z.to_u32_digits().try_into().unwrap())
}

pub fn negate_fp(x: Fp) -> Fp {
    let X: BigUint = BigUint::new(x.0.try_into().unwrap());
    Fp((modulus()-X).to_u32_digits().try_into().unwrap())
}

pub fn sub_fp(x: Fp, y: Fp) -> Fp {
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(x.0.try_into().unwrap());
    let z = (x_b - y_b + modulus()).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    Fp(z.to_u32_digits().try_into().unwrap())
}

pub fn sum_of_products(a: Vec<Fp>, b: Vec<Fp>) -> Fp{
    let acc = a.iter().zip(b.iter()).fold(Fp([0; 12]),|acc, (a_i, b_i)| {
        add_fp(mul_fp(a_i.clone(), b_i.clone()), acc)
    });
    acc
}

#[derive(Clone, Copy, Debug)]
pub struct Fp2([Fp; 2]);

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
        let factor_bu = BigUint::new(factor_fp.0.try_into().unwrap());
        let factor = Fp::get_fp_from_biguint(mod_inverse(factor_bu, modulus()));
        Fp2([
            factor * re,
            factor * (-im)
        ])
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
    let c0 = sub_fp(mul_fp(x.0[0], y.0[0]),mul_fp(x.0[1], y.0[1]));
    let c1 = add_fp(mul_fp(x.0[0], y.0[1]),mul_fp(x.0[1], y.0[0]));
    Fp2 (
        [c0, c1]
    )
}

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

#[derive(Clone, Copy, Debug)]
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
        let c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());
        Fp6([
            c0.forbenius_map(pow).0,
            (c1.forbenius_map(pow) * FP6_FROBENIUS_COEFFICIENTS_1[pow%6]).0,
            (c2.forbenius_map(pow) * FP6_FROBENIUS_COEFFICIENTS_2[pow%6]).0,
        ].concat().try_into().unwrap())
    }
}

impl Fp12 {
    pub fn forbenius_map(&self, pow: usize) -> Self {
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
        let c0c1c2 = Fp6(self.0[0..6].to_vec().try_into().unwrap()).forbenius_map(pow);
        let c0 = Fp2(c0c1c2.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(c0c1c2.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(c0c1c2.0[4..6].to_vec().try_into().unwrap());
        let coeff = FP12_FORBENIUS_COEFFICIENTS[pow % 12];
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
        for i in (0..get_bls_12_381_parameter().bits()-1).rev() {
            z = z.cyclotomicSquare();
            if get_bls_12_381_parameter().bit(i) {
                z = z * self.clone();
            }
        }
        z
    }

    pub fn final_exponentiate(&self) -> Self{
        let t0 = self.forbenius_map(6) / self.clone();
        let t1 = t0.forbenius_map(2) * t0;
        let t2 = t1.cyclotocmicExponent().conjugate();
        let t3 = t1.cyclotomicSquare().conjugate() * t2;
        let t4 = t3.cyclotocmicExponent().conjugate();
        let t5 = t4.cyclotocmicExponent().conjugate();
        let t6 = t5.cyclotocmicExponent().conjugate() * t2.cyclotomicSquare();
        let t7 = t6.cyclotocmicExponent().conjugate();
        
        let t2_t5_pow_q2 = (t2*t5).forbenius_map(2);
        let t4_t1_pow_q3 = (t4*t1).forbenius_map(3);
        let t6_t1c_pow_q1 = (t6*t1.conjugate()).forbenius_map(1);
        let t7_t3c_t1 = (t7*t3.conjugate())*(t1);
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


pub fn calc_pairing_precomp(x: Fp2, y: Fp2) -> Vec<[Fp2; 3]> {
    let Qx = x.clone();
    let Qy = y.clone();
    let Qz = Fp2::one();

    let mut Rx = Qx.clone();
    let mut Ry = Qy.clone();
    let mut Rz = Qz.clone();

    let mut ell_coeff: Vec<[Fp2; 3]> = Vec::<[Fp2; 3]>::new();

    for i in (0..get_bls_12_381_parameter().bits()-2).rev() {
        let t0 = Ry * Ry;
        let t1 = Rz * Rz;
        let t2 = t1.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32))).multiply_by_B();
        let t3 = t2.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32)));
        let t4 = Ry*Ry + Rz*Rz + (Ry * Rz).mul(Fp::get_fp_from_biguint(BigUint::from(2 as u32)))-t1-t0;
        ell_coeff.push(
            [t2-t0, (Rx*Rx).mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32))), -t4]
        );
        Rx = (t0 - t3)*Rx*Ry*Fp::get_fp_from_biguint(mod_inverse(BigUint::from(2 as u32), modulus()));
        Ry = 
        ((t0+t3)*Fp::get_fp_from_biguint(mod_inverse(BigUint::from(2 as u32), modulus()))) * 
        ((t0+t3)*Fp::get_fp_from_biguint(mod_inverse(BigUint::from(2 as u32), modulus()))) - 
        t2*t2*Fp::get_fp_from_biguint(BigUint::from(3 as u32));
        Rz = t0 * t4;
        if get_bls_12_381_parameter().bit(i) {
            let t0 = Ry - (Qy * Rz);
            let t1 = Rx - (Qx * Rz);
            ell_coeff.push([
                (t0 * Qx) - (t1 * Qy),
                -t0,
                t1
            ]);
            let t2 = t1*t1;
            let t3 = t2 * t1;
            let t4 = t2* Rx;
            let t5 = t3 - (t4 * Fp::get_fp_from_biguint(BigUint::from(3 as u32))) + (t0 * t0 * Rz);
            Rx = t1 * t5;
            Ry = (t4 - t5) * t0 - (t3 * Ry);
            Rz = Rz * t3;
        }
    }
    return ell_coeff;
}


pub fn miller_loop(g1_x: Fp, g1_y: Fp, g2_x: Fp2, g2_y: Fp2) -> Fp12 {
    let precomputes = calc_pairing_precomp(g2_x, g2_y);
    let Px = g1_x.clone();
    let Py = g1_y.clone();
    let mut f12 = Fp12::one();
    let mut j = 0;

    for i in (0..get_bls_12_381_parameter().bits()-2).rev() {

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

pub fn pairing(p_x: Fp, p_y: Fp, q_x: Fp2, q_y: Fp2) -> Fp12 {
    let looped = miller_loop(p_x, p_y, q_x, q_y);
    looped.final_exponentiate()
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
    let pk_x = BigUint::from_str("3071902358779104425805220059913391042958977442368743450008922736970201383908820407429457646333339330346464018568299").unwrap().to_u32_digits();
    let pk_y = BigUint::from_str("208729469830998646909339719617829960147637284847029296662162145937938053125975650713155855600870449370845588704920").unwrap().to_u32_digits();

    // Hashed message in g2
    let Hm_x_1 = BigUint::from_str("377525340465127240390006870673927129435673249221760063250140335517131386743242190939209933287674151299948365589984").unwrap().to_u32_digits();
    let Hm_x_2 = BigUint::from_str("1050959494132411586723873443636085717179713480840095989211192028601018716895799746178715855146873969711260353313306").unwrap().to_u32_digits();
    let Hm_y_1 = BigUint::from_str("1131267707057668367159571747448144959495496577180002964665679138922368484682635468083328267231891238196968252631379").unwrap().to_u32_digits();
    let Hm_y_2 = BigUint::from_str("3783154323541729598398766283148329593362868413141617593978449262336941595119881847879377563302954053187852058644118").unwrap().to_u32_digits();
    // Generator
    let G_x = BigUint::from_str("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507").unwrap().to_u32_digits();
    let G_y = BigUint::from_str("1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569").unwrap().to_u32_digits();

    // Signature
    let S_x_1 = BigUint::from_str("966572263166434944599183957482752531047038993953916430862595578899059824912156165297149403978420723932172123775406").unwrap().to_u32_digits();
    let S_x_2 = BigUint::from_str("842321951799503469014964953496381065608123412078137658319961132736911642409943969612292629578043499296195717122533").unwrap().to_u32_digits();
    let mut S_y_1 = BigUint::from_str("1639805997476177777241606094884612303776858264957232458415894583607376414805753804084820168641517462543804792794779").unwrap().to_u32_digits();
    let mut S_y_2 = BigUint::from_str("3855722596444217665140296300241881837775734411784092265317102637289824807772757224642216633698428180424693166393122").unwrap().to_u32_digits();

    let bls_12_381_prime = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787").unwrap().to_u32_digits();

    // 1. negate Signature
    let S_y_1 = big_sub(bls_12_381_prime.clone(), S_y_1);
    let S_y_2 = big_sub(bls_12_381_prime.clone(), S_y_2);

    // 2. Miller loop

    



//    let pairingRes = pairing(P.pointNegate(), Hm)
//    let pairingRes2 = pairing(G, S)
    true
}

#[cfg(test)]   
mod tests {
    use std::str::FromStr;

    use hex::FromHex;
    use num_bigint::BigUint;

    use crate::native::big_sub;

    use super::{verify_bls_signatures, Fp};

    #[test]
    pub fn test1() {
        // verify_bls_signatures();
        // let x = Fp([0;12]);
        // println!("{:?}", x.get_bit(0));
    }

    #[test]
    pub fn test_big_sum() {
        let pk_x = BigUint::from_str("3071902358779104425805220059913391042958977442368743450008922736970201383908820407429457646333339330346464018568299").unwrap();
        let pk_x_u32 = pk_x.to_u32_digits();
        let S_x_1 = BigUint::from_str("966572263166434944599183957482752531047038993953916430862595578899059824912156165297149403978420723932172123775406").unwrap();
        let S_x_1_u32 = S_x_1.to_u32_digits();
        let res = big_sub(pk_x_u32, S_x_1_u32);
        assert_eq!(BigUint::new(res), pk_x-S_x_1);
    }
}