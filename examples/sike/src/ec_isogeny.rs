use hacspec_lib::*;

use crate::fp2::ONE;
use crate::fp2::*;

public_nat_mod!(
    type_name: ASc,
    type_of_canvas: AScCanvas,
    bit_size_of_field: 217, // eA
    modulo_value: "1000000000000000000000000000000000000000000000000000000" // 2^eA
);

public_nat_mod!(
    type_name: BSc,
    type_of_canvas: BScCanvas,
    bit_size_of_field: 218, // eB
    modulo_value: "2341f271773446cfc5fd681c520567bc65c783158aea3fdc1767ae3" // 3^eB
);

const MAX_ALICE: usize = 107;
const MAX_BOB: usize = 136;

const ALICE_BITS: usize = 216;
const BOB_BITS: usize = 217;

pub const EA: u128 = 216;
pub const EB: u128 = 137;

array!(AliceStrat, MAX_ALICE, usize);
array!(BobStrat, MAX_BOB, usize);

pub type Point = (Fp2, Fp2);
type MontCurve = (Fp2, Fp2); // (a,b) where a and b are parameters of the curve (in Montgomery form)

// const ASTRAT: AliceStrat = AliceStrat([
//     48, 28, 16, 8, 4, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8, 4, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2,
//     1, 1, 13, 7, 4, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 21, 12,
//     7, 4, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5, 3, 2, 1, 1, 1,
//     1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1,
// ]);

// const BSTRAT: BobStrat = BobStrat([
//     66, 33, 17, 9, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 8, 4, 2, 1, 1, 1, 2, 1,
//     1, 4, 2, 1, 1, 2, 1, 1, 16, 8, 4, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8, 4, 2, 1, 1, 2,
//     1, 1, 4, 2, 1, 1, 2, 1, 1, 32, 16, 8, 4, 3, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8, 4, 2,
//     1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 16, 8, 4, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 8, 4, 2,
//     1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1,
// ]);

#[allow(non_snake_case)]
fn INF() -> Point {
    (ZERO(), ZERO())
}

pub fn is_inf(p: Point) -> bool {
    p == INF()
}

pub fn dbl(e: MontCurve, p: Point) -> Point {
    let (a, b) = e;

    // x3 = b*(3*x1^2+2*a*x1+1)^2/(2*b*y1)^2-a-x1-x1
    // y3 = (2*x1+x1+a)*(3*x1^2+2*a*x1+1)/(2*b*y1)-b*(3*x1^2+2*a*x1+1)^3/(2*b*y1)^3-y1

    let (x1, y1) = p;

    let t2 = crate::fp2::ONE();
    let t0 = fp2sqr(x1);
    let t1 = fp2add(t0, t0);
    let t0 = fp2add(t0, t1);

    let t1 = fp2mul(x1, a);
    let t1 = fp2add(t1, t1);

    let t0 = fp2add(t0, t1);
    let t0 = fp2add(t0, t2);

    let t1 = fp2mul(b, y1);
    let t1 = fp2add(t1, t1);
    let t1 = fp2inv(t1);

    let t0 = fp2mul(t0, t1);

    let t1 = fp2sqr(t0);

    let t2 = fp2mul(b, t1);
    let t2 = fp2sub(t2, a);
    let t2 = fp2sub(t2, x1);
    let t2 = fp2sub(t2, x1);

    let t1 = fp2mul(t0, t1);
    let t1 = fp2mul(b, t1);
    let t1 = fp2add(t1, y1);

    let y1 = fp2add(x1, x1);
    let y1 = fp2add(y1, x1);
    let y1 = fp2add(y1, a);
    let y1 = fp2mul(y1, t0);
    let y1 = fp2sub(y1, t1);

    if is_inf(p) {
	p
    } else {
	(t2, y1)
    }
}

pub fn neg(p: Point) -> Point {
    let (x, y) = p;
    (x, fp2neg(y))
}

pub fn add(e: MontCurve, p: Point, q: Point) -> Point {
    // x3 = b*(y2-y1)^2/(x2-x1)^2-a-x1-x2
    // y3 = (2*x1+x2+a)*(y2-y1)/(x2-x1)-b*(y2-y1)^3/(x2-x1)^3-y1
    // y3 = ((2*x1)+x2+a) * ((y2-y1)/(x2-x1)) - b*((y2-y1)^3/(x2-x1)^3) - y1

    let (a, b) = e;

    let (x1, y1) = p;
    let (x2, y2) = q;

    let t0 = fp2sub(y2, y1);
    let t1 = fp2sub(x2, x1);
    let t1 = fp2inv(t1);
    let t0 = fp2mul(t0, t1);

    let t1 = fp2sqr(t0);

    let t2 = fp2add(x1, x1);
    let t2 = fp2add(t2, x2);
    let t2 = fp2add(t2, a);
    let t2 = fp2mul(t2, t0);

    let t0 = fp2mul(t0, t1);
    let t0 = fp2mul(b, t0);
    let t0 = fp2add(t0, y1);

    let t0 = fp2sub(t2, t0);

    let t1 = fp2mul(b, t1);
    let t1 = fp2sub(t1, a);
    let t1 = fp2sub(t1, x1);

    let x3 = fp2sub(t1, x2);

    if is_inf(p) {
	q
    } else {
	if is_inf(q) {
	    p
	} else {
	    if p == q {
		dbl(e, p)
	    } else {
		if p == neg(q) {
		    (ZERO(), ZERO())
		} else {
		    (x3, t0)
		}
	    }
	}
    }
}

pub fn a_dbl_and_add(e: MontCurve, k: ASc, p: Point) -> Point {
    let mut q = INF();

    for i in 0..ALICE_BITS {
	q = dbl(e, q);
	if k.bit(ALICE_BITS - i) {
	    q = add(e, q, p);
	}
    }
    q
}

pub fn b_dbl_and_add(e: MontCurve, k: BSc, p: Point) -> Point {
    let mut q = INF();

    for i in 0..BOB_BITS {
	q = dbl(e, q);
	if k.bit(BOB_BITS - i) {
	    q = add(e, q, p);
	}
    }
    q
}

pub fn tpl(e: MontCurve, p: Point) -> Point {
    let t = dbl(e, p);
    let r = add(e, p, t);
    r
}

pub fn dbl_k(e: MontCurve, p: Point, k: u128) -> Point {
    let mut p_mut = p;
    for _j in 0..k {
	p_mut = dbl(e, p_mut);
    }
    p_mut
}

pub fn tpl_k(e: MontCurve, p: Point, k: u128) -> Point {
    let mut p_mut = p;
    for _j in 0..k {
	p_mut = tpl(e, p_mut);
    }
    p_mut
}

// j-invariant:
// 256*(a^2-3)^3/(a^2-4);
pub fn j_inv(e: MontCurve) -> Fp2 {
    let (a, _) = e;

    let t0 = fp2sqr(a);
    let jinv = fp2from_literals(3, 0);
    let jinv = fp2sub(t0, jinv);
    let t1 = fp2sqr(jinv);
    let jinv = fp2mul(jinv, t1);
    let jinv = fp2add(jinv, jinv);
    let jinv = fp2add(jinv, jinv);
    let jinv = fp2add(jinv, jinv);
    let jinv = fp2add(jinv, jinv);
    let jinv = fp2add(jinv, jinv);
    let jinv = fp2add(jinv, jinv);
    let jinv = fp2add(jinv, jinv);
    let jinv = fp2add(jinv, jinv);

    let t1 = fp2from_literals(4, 0);
    let t0 = fp2sub(t0, t1);
    let t0 = fp2inv(t0);
    fp2mul(jinv, t0)
}

// 2-isogeny section

// eval the isogeny corresponding to the point `base` (i.e. corresponding to the kernel containing base) of order 2 on `p`
pub fn eval_2_iso(p2: Point, p: Point) -> Point {
    // x3:=(x^2*x2-x)/(x-x2);
    // y3:=y*(x^2*x2-2*x*x2^2+x2)/(x-x2)^2;

    let (x2, _) = p2;
    let (x, y) = p;

    let t1 = fp2mul(x, x2);
    let t2 = fp2mul(x, t1);
    let t3 = fp2mul(t1, x2);
    let t3 = fp2add(t3, t3);
    let t3 = fp2sub(t2, t3);
    let t3 = fp2add(t3, x2);
    let t3 = fp2mul(y, t3);
    let t2 = fp2sub(t2, x);
    let t1 = fp2sub(x, x2);
    let t1 = fp2inv(t1);
    let x3 = fp2mul(t2, t1);
    let t1 = fp2sqr(t1);
    let y3 = fp2mul(t3, t1);
    (x3, y3)
}

pub fn curve_2_iso(p2: Point, e: MontCurve) -> MontCurve {
    // a2:=2*(1-2*x2^2);
    // b2:=x2*b;

    let (x2, _) = p2;
    let (_, b) = e;

    let t1 = fp2sqr(x2);
    let t1 = fp2add(t1, t1);
    let t1 = fp2sub(ONE(), t1);
    let a2 = fp2add(t1, t1);
    let b2 = fp2mul(x2, b);
    (a2, b2)
}

#[allow(unused_assignments)]
pub fn iso_2_ea(e: MontCurve, s: Point) -> MontCurve {
    let mut e_mut = e;
    let mut s_mut = s;

    let mut t = (ZERO(), ZERO());

    for i in 1..4 {
	t = dbl_k(e_mut, s_mut, 216 - i); // compute point of order 2
	e_mut = curve_2_iso(t, e_mut); // compute codomain of the iso corresponding to s_mut

	s_mut = eval_2_iso(t, s_mut); // carry s to iso curve
    }

    e_mut
}

type MontCurveBasis = (MontCurve, Point, Point);

#[allow(unused_assignments)]
pub fn iso_2_ea_basis(e: MontCurve, s: Point, p: Point, q: Point) -> MontCurveBasis {
    let mut e_mut = e;
    let mut s_mut = s;
    let mut p_mut = p;
    let mut q_mut = q;

    let mut t = (ZERO(), ZERO());

    for i in 1..4 {
	t = dbl_k(e_mut, s_mut, 216 - i);
	e_mut = curve_2_iso(t, e_mut);

	s_mut = eval_2_iso(t, s_mut);

	p_mut = eval_2_iso(t, p_mut);
	q_mut = eval_2_iso(t, q_mut);
    }

    (e_mut, p_mut, q_mut)
}

// 3-isogeny section

pub fn eval_3_iso(p3: Point, p: Point) -> Point {
    // xx:=x*(x*x3-1)^2/(x-x3)^2;
    // yy:=y*(x*x3-1)*(x^2*x3-3*x*x3^2+x+x3)/(x-x3)^3;

    let (x3, _) = p3;
    let (x, y) = p;

    let t1 = fp2sqr(x);
    let t1 = fp2mul(t1, x3);
    let t2 = fp2sqr(x3);
    let t2 = fp2mul(x, t2);
    let t3 = fp2add(t2, t2);
    let t2 = fp2add(t2, t3);
    let t1 = fp2sub(t1, t2);
    let t1 = fp2add(t1, x);
    let t1 = fp2add(t1, x3);

    let t2 = fp2sub(x, x3);
    let t2 = fp2inv(t2);
    let t3 = fp2sqr(t2);
    let t2 = fp2mul(t2, t3);

    let t4 = fp2mul(x, x3);
    let t4 = fp2sub(t4, ONE());

    let t1 = fp2mul(t4, t1);
    let t1 = fp2mul(t1, t2);

    let t2 = fp2sqr(t4);
    let t2 = fp2mul(t2, t3);

    let iso_x = fp2mul(x, t2);
    let iso_y = fp2mul(y, t1);

    (iso_x, iso_y)
}

pub fn curve_3_iso(p3: Point, e: MontCurve) -> MontCurve {
    let (x3, _) = p3;
    let (a, b) = e;

    let t1 = fp2sqr(x3);
    let iso_b = fp2mul(b, t1);

    let t1 = fp2add(t1, t1);
    let t2 = fp2add(t1, t1);
    let t1 = fp2add(t1, t2);
    let t1 = fp2sub(t1, fp2from_literals(6, 0));
    let t2 = fp2mul(a, x3);
    let t1 = fp2sub(t2, t1);
    let iso_a = fp2mul(t1, x3);

    (iso_a, iso_b)
}

#[allow(unused_assignments)]
pub fn iso_3_eb(e: MontCurve, s: Point) -> MontCurve {
    let mut e_mut = e;
    let mut s_mut = s;

    let mut t = (ZERO(), ZERO());

    for i in 1..4 {
	t = tpl_k(e_mut, s_mut, 137 - i); // compute point of order 2
	e_mut = curve_3_iso(t, e_mut); // compute codomain of the iso corresponding to s_mut

	s_mut = eval_3_iso(t, s_mut); // carry s to iso curve
    }

    e_mut
}

#[allow(unused_assignments)]
pub fn iso_3_eb_basis(e: MontCurve, s: Point, p: Point, q: Point) -> MontCurveBasis {
    let mut e_mut = e;
    let mut s_mut = s;
    let mut p_mut = p;
    let mut q_mut = q;

    let mut t = (ZERO(), ZERO());

    for i in 1..4 {
	t = tpl_k(e_mut, s_mut, 137 - i);
	e_mut = curve_3_iso(t, e_mut);

	s_mut = eval_3_iso(t, s_mut);

	p_mut = eval_3_iso(t, p_mut);
	q_mut = eval_3_iso(t, q_mut);
    }

    (e_mut, p_mut, q_mut)
}

pub fn a_sidh_isogen(
    sk: ASc,
    e: MontCurve,
    p_a: Point,
    q_a: Point,
    p_b: Point,
    q_b: Point,
) -> MontCurveBasis {
    // S:=P2+SK_2*Q2;
    let s = a_dbl_and_add(e, sk, q_a);
    let s = add(e, p_a, s);

    iso_2_ea_basis(e, s, p_b, q_b)
}

pub fn b_sidh_isogen(
    sk: BSc,
    e: MontCurve,
    p_b: Point,
    q_b: Point,
    p_a: Point,
    q_a: Point,
) -> MontCurveBasis {
    // S:=P2+SK_2*Q2;
    let s = b_dbl_and_add(e, sk, q_b);
    let s = add(e, p_b, s);

    iso_3_eb_basis(e, s, p_a, q_a)
}

pub fn a_sidh_isoex(sk: ASc, e: MontCurveBasis) -> MontCurve {
    let (e, p, q) = e;
    let s = a_dbl_and_add(e, sk, q);
    let s = add(e, p, s);

    iso_2_ea(e, s)
}

pub fn b_sidh_isoex(sk: BSc, e: MontCurveBasis) -> MontCurve {
    let (e, p, q) = e;
    let s = b_dbl_and_add(e, sk, q);
    let s = add(e, p, s);

    iso_3_eb(e, s)
}

/** Projective implementation
 ******************************/

// i just reuse the affine point type Point for (x,z) projective points (i.e. projective points with y omitted)
// this is maybe not the best
// type PPoint = (Fp2, Fp2);

// return the affine x-coordinate of a projective point
pub fn affine_x(p: Point) -> Fp2 {
    let (x, z) = p;

    let inv = fp2inv(z);
    let x_a = fp2mul(inv, x);

    x_a
}

pub fn xdbl(p: Point, a24plus: Fp2, c24: Fp2) -> Point {
    // Doubling of a Montgomery point in projective coordinates (X:Z).
    // Input: projective Montgomery x-coordinates P = (X1:Z1), where x1=X1/Z1 and Montgomery curve constants A+2C and 4C.
    // Output: projective Montgomery x-coordinates Q = 2*P = (X2:Z2).
    let (x, z) = p;

    let t0 = fp2sub(x, z);
    let t1 = fp2add(x, z);
    let t0 = fp2sqr(t0);
    let t1 = fp2sqr(t1);
    let z = fp2mul(c24, t0);
    let x = fp2mul(t1, z);
    let t1 = fp2sub(t1, t0);
    let t0 = fp2mul(a24plus, t1);
    let z = fp2add(z, t0);
    let z = fp2mul(z, t1);

    (x, z)
}

pub fn xdbl_e(p: Point, a24plus: Fp2, c24: Fp2, e: u128) -> Point {
    // Computes [2^e](X:Z) on Montgomery curve with projective constant via e repeated doublings.
    // Input: projective Montgomery x-coordinates P = (XP:ZP), such that xP=XP/ZP and Montgomery curve constants A+2C and 4C.
    // Output: projective Montgomery x-coordinates Q <- (2^e)*P.
    let mut p_mut = p;

    for _i in 0..e {
	p_mut = xdbl(p_mut, a24plus, c24);
    }

    p_mut
}

pub fn j_inv_p(a: Fp2, c: Fp2) -> Fp2 {
    let j_inv = fp2sqr(a);
    let t1 = fp2sqr(c);

    let t0 = fp2add(t1, t1);
    let t0 = fp2sub(j_inv, t0);
    let t0 = fp2sub(t0, t1);
    let j_inv = fp2sub(t0, t1);
    let t1 = fp2sqr(t1);
    let j_inv = fp2mul(j_inv, t1);
    let t0 = fp2add(t0, t0);
    let t0 = fp2add(t0, t0);
    let t1 = fp2sqr(t0);
    let t0 = fp2mul(t0, t1);
    let t0 = fp2add(t0, t0);
    let t0 = fp2add(t0, t0);
    let j_inv = fp2inv(j_inv);
    let j_inv = fp2mul(j_inv, t0);
    j_inv
}

pub fn get_2_isog(p: Point) -> (Fp2, Fp2) {
    // Computes the corresponding 2-isogeny of a projective Montgomery point (X2:Z2) of order 2.
    // Input:  projective point of order two P = (X2:Z2).
    // Output: the 2-isogenous Montgomery curve with projective coefficients A'/C' where A'+2C' = A24plus and 4C'=C24.

    let (x, z) = p;

    let a24plus = fp2sqr(x);
    let c24 = fp2sqr(z);
    let a24plus = fp2sub(c24, a24plus);

    (a24plus, c24)
}

pub fn eval_2_isog(p: Point, q: Point) -> Point {
    // Evaluates the isogeny at the point (X:Z) in the domain of the isogeny, given a 2-isogeny phi.
    // Inputs: the projective point P = (X:Z) and the 2-isogeny kernel projetive point Q = (X2:Z2).
    // Output: the projective point P = phi(P) = (X:Z) in the codomain.

    let (q_x, q_z) = q;
    let (p_x, p_z) = p;

    let t0 = fp2add(q_x, q_z);
    let t1 = fp2sub(q_x, q_z);
    let t2 = fp2add(p_x, p_z);
    let t3 = fp2sub(p_x, p_z);

    let t0 = fp2mul(t0, t3);
    let t1 = fp2mul(t1, t2);
    let t2 = fp2add(t0, t1);
    let t3 = fp2sub(t0, t1);

    let p_x = fp2mul(p_x, t2);
    let p_z = fp2mul(p_z, t3);
    (p_x, p_z)
}

pub fn get_4_isog(p: Point) -> (Fp2, Fp2, Fp2, Fp2, Fp2) {
    // Computes the corresponding 4-isogeny of a projective Montgomery point (X4:Z4) of order 4.
    // Input:  projective point of order four P = (X4:Z4).
    // Output: the 4-isogenous Montgomery curve with projective coefficients A'/C' where A'+2C' = A24plus and
    // 4C' = C24 and the 3 coefficients that are used to evaluate the isogeny at a point in eval_4_isog().
    let (x, z) = p;

    let c1 = fp2sub(x, z);
    let c2 = fp2add(x, z);
    let c0 = fp2sqr(z);
    let c0 = fp2add(c0, c0);
    let c24 = fp2sqr(c0);
    let c0 = fp2add(c0, c0);
    let a24plus = fp2sqr(x);
    let a24plus = fp2add(a24plus, a24plus);
    let a24plus = fp2sqr(a24plus);

    (a24plus, c24, c0, c1, c2)
}

pub fn eval_4_isog(p: Point, c0: Fp2, c1: Fp2, c2: Fp2) -> Point {
    // Evaluates the isogeny at the point (X:Z) in the domain of the isogeny, given a 4-isogeny phi defined
    // by the 3 coefficients in coeff (computed in the function get_4_isog()).
    // Inputs: the coefficients defining the isogeny, and the projective point P = (X:Z).
    // Output: the projective point P = phi(P) = (X:Z) in the codomain.
    let (x, z) = p;

    let t0 = fp2add(x, z);
    let t1 = fp2sub(x, z);
    let x = fp2mul(t0, c1);
    let z = fp2mul(t1, c2);
    let t0 = fp2mul(t0, t1);
    let t0 = fp2mul(c0, t0);
    let t1 = fp2add(x, z);
    let z = fp2sub(x, z);
    let t1 = fp2sqr(t1);
    let z = fp2sqr(z);
    let x = fp2add(t1, t0);
    let t0 = fp2sub(z, t0);
    let x = fp2mul(x, t1);
    let z = fp2mul(z, t0);

    (x, z)
}

pub fn xtpl(p: Point, a24plus: Fp2, a24minus: Fp2) -> Point {
    // Tripling of a Montgomery point in projective coordinates (X:Z).
    // Input: projective Montgomery x-coordinates P = (X:Z), where x=X/Z and Montgomery curve constants A24plus = A+2C and A24minus = A-2C.
    // Output: projective Montgomery x-coordinates Q = 3*P = (X3:Z3).
    let (x, z) = p;

    let t0 = fp2sub(x, z);
    let t2 = fp2sqr(t0);
    let t1 = fp2add(x, z);
    let t3 = fp2sqr(t1);
    let t4 = fp2add(x, x);
    let t0 = fp2add(z, z);
    let t1 = fp2sqr(t4);
    let t1 = fp2sub(t1, t3);
    let t1 = fp2sub(t1, t2);
    let t5 = fp2mul(a24plus, t3);
    let t3 = fp2mul(t3, t5);
    let t6 = fp2mul(a24minus, t2);
    let t2 = fp2mul(t2, t6);
    let t3 = fp2sub(t2, t3);
    let t2 = fp2sub(t5, t6);
    let t1 = fp2mul(t1, t2);
    let t2 = fp2add(t3, t1);
    let t2 = fp2sqr(t2);
    let x = fp2mul(t4, t2);
    let t1 = fp2sub(t3, t1);
    let t1 = fp2sqr(t1);
    let z = fp2mul(t0, t1);

    (x, z)
}

pub fn xtpl_e(p: Point, a24plus: Fp2, a24minus: Fp2, e: u128) -> Point {
    // Computes [3^e](X:Z) on Montgomery curve with projective constant via e repeated triplings.
    // Input: projective Montgomery x-coordinates P = (XP:ZP), such that xP=XP/ZP and Montgomery curve constants A24plus = A+2C and A24minus = A-2C.
    // Output: projective Montgomery x-coordinates Q <- (3^e)*P.
    let mut p_mut = p;

    for _i in 0..e {
	p_mut = xtpl(p_mut, a24plus, a24minus);
    }

    p_mut
}

pub fn get_3_isog(p: Point) -> (Fp2, Fp2, Fp2, Fp2) {
    // Computes the corresponding 3-isogeny of a projective Montgomery point (X3:Z3) of order 3.
    // Input:  projective point of order three P = (X3:Z3).
    // Output: the 3-isogenous Montgomery curve with projective coefficient A'/C' where A'-2C' = A24minus and A'+2C' = A24plus.
    let (x, z) = p;

    let c0 = fp2sub(x, z);
    let t0 = fp2sqr(c0);
    let c1 = fp2add(x, z);
    let t1 = fp2sqr(c1);

    let t3 = fp2add(x, x);
    let t3 = fp2sqr(t3);

    let t2 = fp2sub(t3, t0);
    let t3 = fp2sub(t3, t1);
    let t4 = fp2add(t0, t3);
    let t4 = fp2add(t4, t4);
    let t4 = fp2add(t1, t4);
    let a24minus = fp2mul(t2, t4);

    let t4 = fp2add(t1, t2);
    let t4 = fp2add(t4, t4);
    let t4 = fp2add(t0, t4);
    let a24plus = fp2mul(t3, t4);

    (a24plus, a24minus, c0, c1)
}

pub fn eval_3_isog(p: Point, c0: Fp2, c1: Fp2) -> Point {
    // Computes the 3-isogeny R=phi(X:Z), given projective point (X3:Z3) of order 3 on a Montgomery curve and
    // a point P with 2 coefficients in coeff (computed in the function get_3_isog()).
    // Inputs: projective points P = (X3:Z3) and Q = (X:Z).
    // Output: the projective point Q <- phi(Q) = (X3:Z3).
    let (x, z) = p;

    let t0 = fp2add(x, z);
    let t1 = fp2sub(x, z);
    let t0 = fp2mul(c0, t0);
    let t1 = fp2mul(c1, t1);
    let t2 = fp2add(t0, t1);
    let t0 = fp2sub(t1, t0);
    let t2 = fp2sqr(t2);
    let t0 = fp2sqr(t0);

    let x = fp2mul(x, t2);
    let z = fp2mul(z, t0);

    (x, z)
}

pub fn inv_3_way(z1: Fp2, z2: Fp2, z3: Fp2) -> (Fp2, Fp2, Fp2){
    // 3-way simultaneous inversion
    // Input:  z1,z2,z3
    // Output: 1/z1,1/z2,1/z3 (override inputs).

    let t0 = fp2mul(z1,z2);
    let t1 = fp2mul(z3,t0);
    let t1 = fp2inv(t1);
    let t2 = fp2mul(z3,t1);
    let t3 = fp2mul(t2,z2);
    let z2 = fp2mul(t2,z1);
    let z3 = fp2mul(t0,t1);

    (t3,z2,z3)
}

pub fn get_a(x_p: Fp2, x_q: Fp2, x_r: Fp2) -> Fp2  {
    // Given the x-coordinates of P, Q, and R, returns the value A corresponding to the Montgomery curve E_A: y^2=x^3+A*x^2+x such that R=Q-P on E_A.
    // Input:  the x-coordinates xP, xQ, and xR of the points P, Q and R.
    // Output: the coefficient A corresponding to the curve E_A: y^2=x^3+A*x^2+x.

    let t1 = fp2add(x_p, x_q);
    let t0 = fp2mul(x_p, x_q);
    let a = fp2mul(x_r,t1);
    let a = fp2add(t0,a);
    let t0 = fp2mul(t0,x_r);
    let a = fp2sub(a,ONE());
    let t0 = fp2add(t0,t0);
    let t1 = fp2add(t1,x_r);
    let t0 = fp2add(t0,t0);
    let a = fp2sqr(a);
    let t0 = fp2inv(t0);
    let a = fp2mul(t0,a);
    let a = fp2sub(a,t1);
    a
}

pub fn x_dbladd(p: Point, q: Point, x_pq: Fp2, a24: Fp2) -> (Point, Point) {
    // Simultaneous doubling and differential addition.
    // Input: projective Montgomery points P=(XP:ZP) and Q=(XQ:ZQ) such that xP=XP/ZP and xQ=XQ/ZQ, affine difference xPQ=x(P-Q) and Montgomery curve constant A24=(A+2)/4.
    // Output: projective Montgomery points P <- 2*P = (X2P:Z2P) such that x(2P)=X2P/Z2P, and Q <- P+Q = (XQP:ZQP) such that = x(Q+P)=XQP/ZQP.

    let (x_p,z_p) = p;
    let (x_q,z_q) = q;

    let t0 = fp2add(x_p,z_p);
    let t1 = fp2sub(x_p,z_p);
    let x_p = fp2sqr(t0);
    let t2 = fp2sub(x_q,z_q);
    let x_q = fp2add(x_q, z_q);
    let t0 = fp2mul(t0, t2);
    let z_p = fp2sqr(t1);
    let t1 = fp2mul(t1,x_q);
    let x_p = fp2sub(x_p, z_p);
    let x_p = fp2mul(x_p, z_p);
    let x_q = fp2mul(a24, t2);
    let z_q = fp2sub(t0, t1);
    let z_p = fp2add(x_q, z_p);
    let x_q = fp2add(t0, t1);
    let z_p = fp2mul(z_p, t2);
    let z_q = fp2sqr(z_q);
    let x_q = fp2sqr(x_q);
    let z_q = fp2mul(z_q, x_pq);
    ((x_p, z_p), (x_q, z_q))
}

// FIXME: make constant time, probably will need a constant time swap on Fp and Fp2
pub fn swap_points(p: Point, q: Point, mask: u128) -> (Point, Point) {
    let mut res = (q, p);
    if mask == 0 {
	res = (p, q);
    }
    res
}

pub fn a_ladder3pt(x_p: Fp2, x_q: Fp2, x_pq: Fp2, m: ASc, a: Fp2) -> Point  {
    // Initializing constant
    let a24 = fp2from_literals(2, 0);
    let a24 = fp2add(a,a24);
    let quarter = fp2inv(fp2from_literals(4, 0));
    let a24 = fp2mul(a24,quarter);

    // Initializing points
    let mut r0 = (x_q, ONE());
    let mut r1 = (x_p, ONE());
    let mut r2 = (x_pq, ONE());

    let mut bit;
    let mut swap;
    let mut prevbit = 0;
    let mut mask;

    // Main loop
    for i in 0..ALICE_BITS {
	bit = m.bit(ALICE_BITS - i) as u128;
	swap = bit ^ prevbit;
	prevbit = bit;
	mask = 0 - swap;

	let (r1_tmp, r2_tmp) = swap_points(r1, r2, mask);
	r1 = r1_tmp;
	r2 = r2_tmp;

	let (x_r1, z_r1) = r1;
	let (r0_tmp, r2_tmp) = x_dbladd(r0, r2, x_r1, a24);

	let (x_r2, z_r2) = r2_tmp;
	let x_r2 = fp2mul(x_r2, z_r1);

	r0 = r0_tmp;
	r2 = (x_r2, z_r2);
    }
    swap = 0 ^ prevbit;
    mask = 0 - swap;

    let (r1, _) = swap_points(r1, r2, mask);
    r1
}
