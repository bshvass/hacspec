use crate::fp::*;
use hacspec_lib::*;

pub type Fp2 = (Fp, Fp); // (x, y)

// pub const ZERO: Fp2 = (fp::ONE, fp::ZERO);
// pub const ONE: Fp2 = (fp::ONE, fp::ZERO);

#[allow(non_snake_case)]
pub fn ZERO() -> Fp2 {
    (Fp::ZERO(), Fp::ZERO())
}

#[allow(non_snake_case)]
pub fn ONE() -> Fp2 {
    (Fp::ONE(), Fp::ZERO())
}

/* Arithmetic for FP2 elements */

pub fn fp2neg(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (Fp::ZERO() - n1, Fp::ZERO() - n2)
}

pub fn fp2add(n: Fp2, m: Fp2) -> Fp2 {
    //Coordinate wise
    let (n1, n2) = n;
    let (m1, m2) = m;
    (n1 + m1, n2 + m2)
}

pub fn fp2sub(n: Fp2, m: Fp2) -> Fp2 {
    fp2add(n, fp2neg(m))
}

pub fn fp2mul(n: Fp2, m: Fp2) -> Fp2 {
    //(a+bu)*(c+du) = ac + adu + bcu + bdu^2 = ac - bd + (ad + bc)u
    let (n1, n2) = n;
    let (m1, m2) = m;
    let x1 = (n1 * m1) - (n2 * m2);
    let x2 = (n1 * m2) + (n2 * m1);
    (x1, x2)
}

pub fn fp2inv(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    let t0 = n1 * n1 + (n2 * n2);
    let t1 = t0.inv();
    let x1 = n1 * t1;
    let x2 = Fp::ZERO() - (n2 * t1);
    (x1, x2)
}

pub fn fp2sqr(n: Fp2) -> Fp2 {
    fp2mul(n, n)
}

pub fn fp2from_literals(a: u128, b: u128) -> Fp2 {
    (Fp::from_literal(a), Fp::from_literal(b))
}

#[cfg(test)]
pub fn fp2from_hexes(a: &str, b: &str) -> Fp2 {
    (Fp::from_hex(a), Fp::from_hex(b))
}
