/** Implementation of the SIKE algorithm -- a NIST post-quantum key-encapsulation mechanism canditate
    The implementation is from sike.org. The affine implementation
    corresponds to the 'reference' implementation and the projective to
    the 'optimized' implementation. A few optimzation were not
    implemented, though. In these cases the implementation were taken from
    the specifaction report (also available on sike.org). The optimization
    missing are: The 'deque' version of traversing the isogeny graph. Note
    also that the code is not constant time. */

use hacspec_lib::*;

/** Types
 *********/

pub const EA: usize = 216; // alices exponent
pub const EB: usize = 137; // bobs exponent

// Field (whose binary extension) the curves are defined over
// finite field of size p = 2^EA*3^EB - 1
public_nat_mod!(
    type_name: Fp,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 434,
    modulo_value: "2341F271773446CFC5FD681C520567BC65C783158AEA3FDC1767AE2FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF" // p
);

// Ring of Alices scalars
public_nat_mod!(
    type_name: ASc,
    type_of_canvas: AScCanvas,
    bit_size_of_field: 217,
    modulo_value: "1000000000000000000000000000000000000000000000000000000" // 2^EA
);

// Ring of Bobs scalars
public_nat_mod!(
    type_name: BSc,
    type_of_canvas: BScCanvas,
    bit_size_of_field: 218,
    modulo_value: "2341F271773446CFC5FD681C520567BC65C783158AEA3FDC1767AE3" // 3^EB
);

/// bit size of Alices scalar ring
pub const ALICE_BITS: usize = 217;

/// bit size of Bobs scalar ring
pub const BOB_BITS: usize = 218;

/// (x, y) = x + i*y
pub type Fp2 = (Fp, Fp);

/// (a,b) where a and b are parameters of the curve (in Montgomery form)
pub type MontCurve = (Fp2, Fp2);
pub type Point = (Fp2, Fp2);

/// basis for 2^EA/3^EB torsion on E
pub type Basis = (Point, Point);

/// basis for 2^EA/3^EB torsion on E using x-only arithmetic (x(P), x(Q), x(P-Q) where (P,Q) is a Basis)
pub type PBasis = (Fp2, Fp2, Fp2);

/** Fp2 arithmetic
 ******************/
// (copied from the bls example)


pub fn fp2zero() -> Fp2 {
    (Fp::ZERO(), Fp::ZERO())
}

pub fn fp2one() -> Fp2 {
    (Fp::ONE(), Fp::ZERO())
}

pub fn fp2neg(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (Fp::ZERO() - n1, Fp::ZERO() - n2)
}

pub fn fp2add(n: Fp2, m: Fp2) -> Fp2 {
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

/** Affine curve arithmetic
 ***************************/

/// Point at infinity
pub fn inf()-> Point {
    (fp2zero(), fp2zero())
}

pub fn is_inf(p: Point) -> bool {
    p == inf()
}

/// Point doubling
pub fn dbl(e: MontCurve, p: Point) -> Point {
    let (a, b) = e;

    // x3 = b*(3*x1^2+2*a*x1+1)^2/(2*b*y1)^2-a-x1-x1
    // y3 = (2*x1+x1+a)*(3*x1^2+2*a*x1+1)/(2*b*y1)-b*(3*x1^2+2*a*x1+1)^3/(2*b*y1)^3-y1

    let (x1, y1) = p;

    let t2 = fp2one();
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

/// Point negation
pub fn neg(p: Point) -> Point {
    let (x, y) = p;
    (x, fp2neg(y))
}

/// Point addition
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
		    (fp2zero(), fp2zero())
		} else {
		    (x3, t0)
		}
	    }
	}
    }
}

/// Point tripling
pub fn tpl(e: MontCurve, p: Point) -> Point {
    let t = dbl(e, p);
    let r = add(e, p, t);
    r
}

/// Iterated point doubling
pub fn dbl_k(e: MontCurve, p: Point, k: usize) -> Point {
    let mut p_mut = p;
    for _j in 0..k {
	p_mut = dbl(e, p_mut);
    }
    p_mut
}

/// Iterated point tripling
pub fn tpl_k(e: MontCurve, p: Point, k: usize) -> Point {
    let mut p_mut = p;
    for _j in 0..k {
	p_mut = tpl(e, p_mut);
    }
    p_mut
}

/// (Alice) Scalar multiplication
pub fn a_dbl_and_add(e: MontCurve, k: ASc, p: Point) -> Point {
    let mut q = inf();
    for i in 0..ALICE_BITS {
	q = dbl(e, q);
	if k.bit((ALICE_BITS - 1) - i) {
	    q = add(e, q, p);
	}
    }
    q
}

/// (Bob) Scalar multiplication
pub fn b_dbl_and_add(e: MontCurve, k: BSc, p: Point) -> Point {
    let mut q = inf();

    for i in 0..BOB_BITS {
	q = dbl(e, q);
	if k.bit((BOB_BITS - 1) - i) {
	    q = add(e, q, p);
	}
    }
    q
}

/// j-invariant
pub fn j_inv(e: MontCurve) -> Fp2 {
    // 256*(a^2-3)^3/(a^2-4);
    let (a, _) = e;

    let t0 = fp2sqr(a);
    let jinv = fp2from_literals(3 as u128, 0 as u128);
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

    let t1 = fp2from_literals(4 as u128, 0 as u128);
    let t0 = fp2sub(t0, t1);
    let t0 = fp2inv(t0);
    fp2mul(jinv, t0)
}


/** 2-isogeny computation
 ***************************/

/// Input: point p and point p2 of order 2
/// Output: phi(p) where phi is the 2-isogeny corresponding to p2
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

/// Input: curve e and point p2 of order 2 on e
/// Output: codomain of the 2-isogeny corresponding to p2
pub fn curve_2_iso(p2: Point, e: MontCurve) -> MontCurve {
    // a2:=2*(1-2*x2^2);
    // b2:=x2*b;

    let (x2, _) = p2;
    let (_, b) = e;

    let t1 = fp2sqr(x2);
    let t1 = fp2add(t1, t1);
    let t1 = fp2sub(fp2one(), t1);
    let a2 = fp2add(t1, t1);
    let b2 = fp2mul(x2, b);
    (a2, b2)
}

/// Input: curve e and point s of order 2^EA
/// Output: codomain of the 2^EA-isogeny corresponding to s
pub fn iso_2_ea(e: MontCurve, s: Point, ea: usize) -> MontCurve {
    let mut e_mut = e;
    let mut s_mut = s;

    let mut _t = (fp2zero(), fp2zero());

    for i in 1..(ea + 1) {
	_t = dbl_k(e_mut, s_mut, EA - i); // compute point of order 2
	e_mut = curve_2_iso(_t, e_mut);    // compute codomain of the iso corresponding to s_mut
	s_mut = eval_2_iso(_t, s_mut);     // carry s to iso curve
    }
    e_mut
}

/// Input: curve e with basis for the 3^EB torsion  and point s of order 2^EA
/// Output: codomain of the 2^EA-isogeny corresponding to s and the image of the basis points
pub fn iso_2_ea_basis(e: MontCurve, bbasis: Basis, s: Point, ea: usize) -> (MontCurve, Basis) {
    let (p, q) = bbasis;
    let mut e_mut = e;
    let mut s_mut = s;
    let mut p_mut = p;
    let mut q_mut = q;

    let mut _t = (fp2zero(), fp2zero());

    for i in 1..(ea + 1) {
	_t = dbl_k(e_mut, s_mut, EA - i);
	e_mut = curve_2_iso(_t, e_mut);
	s_mut = eval_2_iso(_t, s_mut);

	p_mut = eval_2_iso(_t, p_mut);
	q_mut = eval_2_iso(_t, q_mut);
    }
    (e_mut, (p_mut, q_mut))
}

/** 3-isogeny computation
 *************************/

/// Input: point p and point p3 of order 3
/// Output: phi(p) where phi is the 3-isogeny corresponding to p3
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
    let t4 = fp2sub(t4, fp2one());
    let t1 = fp2mul(t4, t1);
    let t1 = fp2mul(t1, t2);
    let t2 = fp2sqr(t4);
    let t2 = fp2mul(t2, t3);
    let iso_x = fp2mul(x, t2);
    let iso_y = fp2mul(y, t1);

    (iso_x, iso_y)
}

/// Input: curve e and point p3 of order 3 on e
/// Output: codomain of the 3-isogeny corresponding to p3
pub fn curve_3_iso(p3: Point, e: MontCurve) -> MontCurve {
    let (x3, _) = p3;
    let (a, b) = e;

    let t1 = fp2sqr(x3);
    let iso_b = fp2mul(b, t1);

    let t1 = fp2add(t1, t1);
    let t2 = fp2add(t1, t1);
    let t1 = fp2add(t1, t2);
    let t1 = fp2sub(t1, fp2from_literals(6 as u128, 0 as u128));
    let t2 = fp2mul(a, x3);
    let t1 = fp2sub(t2, t1);
    let iso_a = fp2mul(t1, x3);

    (iso_a, iso_b)
}

/// Input: curve e and point s of order 3^EB
/// Output: codomain of the 3^EB-isogeny corresponding to s
pub fn iso_3_eb(e: MontCurve, s: Point, eb: usize) -> MontCurve {
    let mut e_mut = e;
    let mut s_mut = s;

    let mut _t = (fp2zero(), fp2zero());
    for i in 1..(eb + 1) {
	_t = tpl_k(e_mut, s_mut, EB - i);  // compute point of order 3
	e_mut = curve_3_iso(_t, e_mut);    // compute codomain of the iso corresponding to s_mut
	s_mut = eval_3_iso(_t, s_mut);     // carry s to iso curve
    }
    e_mut
}

/// Input: curve e with basis for the 2^EA torsion  and point s of order 3^EB
/// Output: codomain of the 3^EB-isogeny corresponding to s and the image of the basis points
pub fn iso_3_eb_basis(e: MontCurve, abasis: Basis, s: Point, eb: usize) -> (MontCurve, Basis) {
    let (p, q) = abasis;
    let mut e_mut = e;
    let mut s_mut = s;
    let mut p_mut = p;
    let mut q_mut = q;

    let mut _t = (fp2zero(), fp2zero());

    for i in 1..(eb + 1) {
	_t = tpl_k(e_mut, s_mut, EB - i);
	e_mut = curve_3_iso(_t, e_mut);
	s_mut = eval_3_iso(_t, s_mut);
	p_mut = eval_3_iso(_t, p_mut);
	q_mut = eval_3_iso(_t, q_mut);
    }

    (e_mut, (p_mut, q_mut))
}

/** SIDH section
 ****************/

/// Input: (Alices) secret key sk, curve e, basis ab for the 2^EA torsion and basis bb for the 3^EB torsion
/// Output: image curve under 2^EA-isogeny with basis for 3^EB torsion
pub fn a_sidh_isogen(sk: ASc, e: MontCurve, ab: Basis, bb: Basis, ea: usize) -> (MontCurve, Basis) {
    let (p_a, q_a) = ab;
    let s = a_dbl_and_add(e, sk, q_a);
    let s = add(e, p_a, s);            // S:=PA+SK*QA;
    iso_2_ea_basis(e, bb, s, ea)
}

/// Input: (Alices) secret key sk, curve e, basis ab for the 2^EA torsion
/// Output: j-invariant of the image curve under 2^EA-isogeny (shared secret)
pub fn a_sidh_isoex(sk: ASc, e: MontCurve, ab: Basis, ea: usize) -> Fp2 {
    let (p, q) = ab;
    let s = a_dbl_and_add(e, sk, q);
    let s = add(e, p, s);

    let e = iso_2_ea(e, s, ea);
    j_inv(e)
}

/// Input: (Bobs) secret key sk, curve e, basis bb for the 3^EB torsion and basis ab for the 2^EA torsion
/// Output: image curve under 3^EB-isogeny with basis for 2^EA torsion
pub fn b_sidh_isogen(sk: BSc, e: MontCurve, bb: Basis, ab: Basis, eb: usize) -> (MontCurve, Basis) {
    // S:=P2+SK_2*Q2;
    let (p_b, q_b) = bb;
    let s = b_dbl_and_add(e, sk, q_b);
    let s = add(e, p_b, s);            // S:=PB+SK*QB;

    iso_3_eb_basis(e, ab, s, eb)
}

/// Input: (Bobs) secret key sk, curve e, basis bb for the 3^EB torsion
/// Output: j-invariant of the image curve under 3^EB-isogeny (shared secret)
pub fn b_sidh_isoex(sk: BSc, e: MontCurve, bb: Basis, eb: usize) -> Fp2 {
    let (p, q) = bb;
    let s = b_dbl_and_add(e, sk, q);
    let s = add(e, p, s);

    let e = iso_3_eb(e, s, eb);
    j_inv(e)
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

pub fn xdbl_e(p: Point, a24plus: Fp2, c24: Fp2, e: usize) -> Point {
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
    let jinv = fp2sqr(a);
    let t1 = fp2sqr(c);

    let t0 = fp2add(t1, t1);
    let t0 = fp2sub(jinv, t0);
    let t0 = fp2sub(t0, t1);
    let jinv = fp2sub(t0, t1);
    let t1 = fp2sqr(t1);
    let jinv = fp2mul(jinv, t1);
    let t0 = fp2add(t0, t0);
    let t0 = fp2add(t0, t0);
    let t1 = fp2sqr(t0);
    let t0 = fp2mul(t0, t1);
    let t0 = fp2add(t0, t0);
    let t0 = fp2add(t0, t0);
    let jinv = fp2inv(jinv);
    let jinv = fp2mul(jinv, t0);
    jinv
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

pub fn get_4_isog(p: Point) -> (Fp2, Fp2, (Fp2, Fp2, Fp2)) {
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

    (a24plus, c24, (c0, c1, c2))
}

pub fn eval_4_isog(p: Point, cs: (Fp2, Fp2, Fp2)) -> Point {
    // Evaluates the isogeny at the point (X:Z) in the domain of the isogeny, given a 4-isogeny phi defined
    // by the 3 coefficients in coeff (computed in the function get_4_isog()).
    // Inputs: the coefficients defining the isogeny, and the projective point P = (X:Z).
    // Output: the projective point P = phi(P) = (X:Z) in the codomain.
    let (x, z) = p;
    let (c0,c1,c2) = cs;

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

pub fn xtpl_e(p: Point, a24plus: Fp2, a24minus: Fp2, e: usize) -> Point {
    // Computes [3^e](X:Z) on Montgomery curve with projective constant via e repeated triplings.
    // Input: projective Montgomery x-coordinates P = (XP:ZP), such that xP=XP/ZP and Montgomery curve constants A24plus = A+2C and A24minus = A-2C.
    // Output: projective Montgomery x-coordinates Q <- (3^e)*P.
    let mut p_mut = p;

    for _i in 0..e {
	p_mut = xtpl(p_mut, a24plus, a24minus);
    }
    p_mut
}

pub fn get_3_isog(p: Point) -> (Fp2, Fp2, (Fp2, Fp2)) {
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

    (a24plus, a24minus, (c0, c1))
}

pub fn eval_3_isog(p: Point, cs: (Fp2, Fp2)) -> Point {
    // Computes the 3-isogeny R=phi(X:Z), given projective point (X3:Z3) of order 3 on a Montgomery curve and
    // a point P with 2 coefficients in coeff (computed in the function get_3_isog()).
    // Inputs: projective points P = (X3:Z3) and Q = (X:Z).
    // Output: the projective point Q <- phi(Q) = (X3:Z3).
    let (c0,c1) = cs;
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
    let a = fp2sub(a,fp2one());
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
    let t2 = fp2sub(x_p, z_p);
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
pub fn swap_points(p: Point, q: Point, mask: usize) -> (Point, Point) {
    let mut res = (q, p);
    if mask == 0 {
	res = (p, q);
    }
    res
}

// NB: This is not constant time
pub fn a_ladder3pt(x_p: Fp2, x_q: Fp2, x_pq: Fp2, m: ASc, a: Fp2) -> Point  {
    // Initializing constant
    let a24 = fp2from_literals(2 as u128, 0 as u128);
    let a24 = fp2add(a,a24);
    let quarter = fp2inv(fp2from_literals(4 as u128, 0 as u128));
    let a24 = fp2mul(a24,quarter);

    // Initializing points
    let mut r0 = (x_q, fp2one());
    let mut r1 = (x_p, fp2one());
    let mut r2 = (x_pq, fp2one());

    // Main loop
    for i in 0..ALICE_BITS {

	if m.bit(i) {
	    let (x_r2, z_r2) = r2;
	    let (r0_tmp, (x_r1,z_r1)) = x_dbladd(r0, r1, x_r2, a24);
	    let x_r1 = fp2mul(z_r2, x_r1);
	    r0 = r0_tmp;
	    r1 = (x_r1,z_r1);
	} else {
	    let (x_r1, z_r1) = r1;
	    let (r0_tmp, (x_r2, z_r2)) = x_dbladd(r0, r2, x_r1, a24);
	    let x_r2 = fp2mul(z_r1, x_r2);
	    r0 = r0_tmp;
	    r2 = (x_r2,z_r2);
	}
    }
    r1
}

pub fn b_ladder3pt(x_p: Fp2, x_q: Fp2, x_pq: Fp2, m: BSc, a: Fp2) -> Point  {
    // Initializing constant
    let a24 = fp2from_literals(2 as u128, 0 as u128);
    let a24 = fp2add(a,a24);
    let quarter = fp2inv(fp2from_literals(4 as u128, 0 as u128));
    let a24 = fp2mul(a24,quarter);

    // Initializing points
    let mut r0 = (x_q, fp2one());
    let mut r1 = (x_p, fp2one());
    let mut r2 = (x_pq, fp2one());

    // Main loop
    for i in 0..BOB_BITS {

	if m.bit(i) {
	    let (x_r2, z_r2) = r2;
	    let (r0_tmp, (x_r1,z_r1)) = x_dbladd(r0, r1, x_r2, a24);
	    let x_r1 = fp2mul(z_r2, x_r1);
	    r0 = r0_tmp;
	    r1 = (x_r1,z_r1);
	} else {
	    let (x_r1, z_r1) = r1;
	    let (r0_tmp, (x_r2, z_r2)) = x_dbladd(r0, r2, x_r1, a24);
	    let x_r2 = fp2mul(z_r1, x_r2);
	    r0 = r0_tmp;
	    r2 = (x_r2,z_r2);
	}
    }
    r1
}

pub fn jinv_from_a24plus_c24(a24plus: Fp2, c24: Fp2) -> Fp2 {
    let a24 = fp2add(a24plus, a24plus);
    let a24 = fp2sub(a24, c24);
    let a24 = fp2add(a24, a24);
    let jinv = j_inv_p(a24,c24);
    jinv
}

pub fn a_keygen(bb: PBasis, ab: PBasis, a: Fp2, a24plus: Fp2, c24: Fp2, sk: ASc, ea: usize) -> PBasis {

    let (x_pa, x_qa, x_ra) = ab;
    let (x_pb, x_qb, x_rb) = bb;

    let mut phi_p = (x_pb, fp2one());
    let mut phi_q = (x_qb, fp2one());
    let mut phi_r = (x_rb, fp2one());

    let mut a24plus = a24plus;
    let mut c24 = c24;

    let mut s = a_ladder3pt(x_pa, x_qa, x_ra, sk, a); // kernel point

    for e in 1..(ea + 1) {
	let t = xdbl_e(s, a24plus, c24, EA -  2*e); // point of order 4
	let (a24plus_tmp, c24_tmp, cs) = get_4_isog(t);
	a24plus = a24plus_tmp;
	c24 = c24_tmp;
	if e != ea {
	    s = eval_4_isog(s, cs);
	}
	phi_p = eval_4_isog(phi_p, cs);
	phi_q = eval_4_isog(phi_q, cs);
	phi_r = eval_4_isog(phi_r, cs);
    }


    let (x_p, z_p) = phi_p;
    let (x_q, z_q) = phi_q;
    let (x_r, z_r) = phi_r;
    let (z_p_inv, z_q_inv, z_r_inv) = inv_3_way(z_p, z_q, z_r);
    let x_p = fp2mul(x_p, z_p_inv);
    let x_q = fp2mul(x_q, z_q_inv);
    let x_r = fp2mul(x_r, z_r_inv);

    (x_p, x_q, x_r)
}

pub fn a_sharedkey(ab: PBasis, sk: ASc, ea: usize) -> Fp2 {

    let (x_phi_pa, x_phi_qa, x_phi_ra) = ab;

    let a = get_a(x_phi_pa, x_phi_qa, x_phi_ra);
    let mut a24plus = fp2add(a,fp2from_literals(2 as u128, 0 as u128));
    let mut c24 = fp2from_literals(4 as u128, 0 as u128);

    let mut s = a_ladder3pt(x_phi_pa, x_phi_qa, x_phi_ra, sk, a); // kernel point

    for e in 1..(ea + 1) {
	let t = xdbl_e(s, a24plus, c24, EA -  2*e);               // point of order 4
	let (a24plus_tmp, c24_tmp, cs) = get_4_isog(t);
	a24plus = a24plus_tmp;
	c24 = c24_tmp;
	if e != ea {
	    s = eval_4_isog(s, cs);
	}
    }
    jinv_from_a24plus_c24(a24plus, c24)
}

pub fn jinv_from_a24minusplus(a24plus: Fp2, a24minus: Fp2) -> Fp2 {
    let a24 = fp2add(a24plus, a24minus);
    let a24 = fp2add(a24, a24);
    let c24 = fp2sub(a24plus, a24minus);
    let jinv = j_inv_p(a24,c24);
    jinv
}

pub fn b_keygen(ab: PBasis, bb: PBasis, a: Fp2, a24plus: Fp2, a24minus: Fp2, sk: BSc, eb: usize) -> PBasis {

    let (x_pa, x_qa, x_ra) = ab;
    let (x_pb, x_qb, x_rb) = bb;

    let mut phi_p = (x_pa, fp2one());
    let mut phi_q = (x_qa, fp2one());
    let mut phi_r = (x_ra, fp2one());

    let mut a24plus = a24plus;
    let mut a24minus = a24minus;

    let mut s = b_ladder3pt(x_pb, x_qb, x_rb, sk, a);    // kernel point

    for e in 1..(eb + 1) {
	let t = xtpl_e(s, a24plus, a24minus, EB -  e);        // point of order 3
	let (a24plus_tmp, a24minus_tmp, cs) = get_3_isog(t);
	a24plus = a24plus_tmp;
	a24minus = a24minus_tmp;
	if e != eb {
	    s = eval_3_isog(s, cs);
	}
	phi_p = eval_3_isog(phi_p, cs);
	phi_q = eval_3_isog(phi_q, cs);
	phi_r = eval_3_isog(phi_r, cs);
    }

    let (x_p, z_p) = phi_p;
    let (x_q, z_q) = phi_q;
    let (x_r, z_r) = phi_r;
    let (z_p_inv, z_q_inv, z_r_inv) = inv_3_way(z_p, z_q, z_r);
    let x_p = fp2mul(x_p, z_p_inv);
    let x_q = fp2mul(x_q, z_q_inv);
    let x_r = fp2mul(x_r, z_r_inv);

    (x_p, x_q, x_r)
}

pub fn b_sharedkey(bb: PBasis, sk: BSc, eb: usize) -> Fp2 {

    let (x_phi_pb, x_phi_qb, x_phi_rb) = bb;

    let a = get_a(x_phi_pb, x_phi_qb, x_phi_rb);
    let mut a24plus = fp2add(a,fp2from_literals(2 as u128, 0 as u128));
    let mut a24minus = fp2sub(a,fp2from_literals(2 as u128, 0 as u128));

    let mut s = b_ladder3pt(x_phi_pb, x_phi_qb, x_phi_rb, sk, a); // kernel point

    for e in 1..(eb + 1) {
	let t = xtpl_e(s, a24plus, a24minus, EB -  e);               // point of order 3
	let (a24plus_tmp, a24minus_tmp, cs) = get_3_isog(t);
	a24plus = a24plus_tmp;
	a24minus = a24minus_tmp;
	if e != eb {
	    s = eval_3_isog(s, cs);
	}
    }
    jinv_from_a24minusplus(a24plus, a24minus)
}
