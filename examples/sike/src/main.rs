use hacspec_lib::*;

public_nat_mod!(
    type_name: Fp,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 434,
    modulo_value: "2341F271773446CFC5FD681C520567BC65C783158AEA3FDC1767AE2FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"
);

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

type Fp2 = (Fp, Fp);	// (x, y)
type Point = (Fp2, Fp2);
type MontCurve = (Fp2, Fp2); // (a,b) where a and b are parameters of the curve (in Montgomery form)

const A: u128 = 6;
const B: u128 = 1;
const C: u128 = 1;

#[allow(dead_code)]
const EA: u128 = 216;
#[allow(dead_code)]
const EB: u128 = 137;

const XPA0: &str = "3CCFC5E1F050030363E6920A0F7A4C6C71E63DE63A0E6475AF621995705F7C84500CB2BB61E950E19EAB8661D25C4A50ED279646CB48";
const XPA1: &str = "1AD1C1CAE7840EDDA6D8A924520F60E573D3B9DFAC6D189941CB22326D284A8816CC4249410FE80D68047D823C97D705246F869E3EA50";
const YPA0: &str = "1AB066B84949582E3F66688452B9255E72A017C45B148D719D9A63CDB7BE6F48C812E33B68161D5AB3A0A36906F04A6A6957E6F4FB2E0";
const YPA1: &str = "FD87F67EA576CE97FF65BF9F4F7688C4C752DCE9F8BD2B36AD66E04249AAF8337C01E6E4E1A844267BA1A1887B433729E1DD90C7DD2F";
const XQA0: &str = "C7461738340EFCF09CE388F666EB38F7F3AFD42DC0B664D9F461F31AA2EDC6B4AB71BD42F4D7C058E13F64B237EF7DDD2ABC0DEB0C6C";
const XQA1: &str = "25DE37157F50D75D320DD0682AB4A67E471586FBC2D31AA32E6957FA2B2614C4CD40A1E27283EAAF4272AE517847197432E2D61C85F5";
const YQA0: &str = "1D407B70B01E4AEE172EDF491F4EF32144F03F5E054CEF9FDE5A35EFA3642A11817905ED0D4F193F31124264924A5F64EFE14B6EC97E5";
const YQA1: &str = "E7DEC8C32F50A4E735A839DCDB89FE0763A184C525F7B7D0EBC0E84E9D83E9AC53A572A25D19E1464B509D97272AE761657B4765B3D6";
const XPB0: &str = "8664865EA7D816F03B31E223C26D406A2C6CD0C3D667466056AAE85895EC37368BFC009DFAFCB3D97E639F65E9E45F46573B0637B7A9";
const XPB1: &str = "0";
const YPB0: &str = "6AE515593E73976091978DFBD70BDA0DD6BCAEEBFDD4FB1E748DDD9ED3FDCF679726C67A3B2CC12B39805B32B612E058A4280764443B";
const YPB1: &str = "0";
const XQB0: &str = "12E84D7652558E694BF84C1FBDAAF99B83B4266C32EC65B10457BCAF94C63EB063681E8B1E7398C0B241C19B9665FDB9E1406DA3D3846";
const XQB1: &str = "0";
const YQB0: &str = "0";
const YQB1: &str = "EBAAA6C731271673BEECE467FD5ED9CC29AB564BDED7BDEAA86DD1E0FDDF399EDCC9B49C829EF53C7D7A35C3A0745D73C424FB4A5FD2";

/* Arithmetic for FP2 elements */
pub fn fp2fromfp(n: Fp) -> Fp2 {
    (n, Fp::ZERO())
}

pub fn fp2zero() -> Fp2 {
    fp2fromfp(Fp::ZERO())
}

pub fn fp2one() -> Fp2 {
    fp2fromfp(Fp::ONE())
}

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

pub fn fp2conjugate(n: Fp2) -> Fp2 {
    let (n1, n2) = n;
    (n1, Fp::ZERO() - n2)
}

pub fn inf() -> Point {
    (fp2zero(), fp2zero())
}

pub fn is_inf(p: Point) -> bool {
    p == inf()
}

pub fn dbl(e: MontCurve, p: Point) -> Point {
    let (a, b) = e;

    // x3 = b*(3*x1^2+2*a*x1+1)^2/(2*b*y1)^2-a-x1-x1
    // y3 = (2*x1+x1+a)*(3*x1^2+2*a*x1+1)/(2*b*y1)-b*(3*x1^2+2*a*x1+1)^3/(2*b*y1)^3-y1

    let (x1,y1) = p;

    let t2 = fp2fromfp(Fp::ONE());
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

fn neg(p: Point) -> Point {
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

    let t2 = fp2add(x1,x1);
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

    if is_inf(p)  {
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

pub fn a_dbl_and_add(e: MontCurve, k: ASc, p: Point) -> Point {

    let msb = 217;
    let mut q = inf();

    for i in 0..msb {
	q = dbl(e,q);
	if k.bit((msb - 1) - i) {
	    q = add(e,q,p);
	}
    }
    q
}

pub fn b_dbl_and_add(e: MontCurve, k: BSc, p: Point) -> Point {

    let msb = 218;
    let mut q = inf();

    for i in 0..msb {
	q = dbl(e,q);
	if k.bit((msb - 1) - i) {
	    q = add(e,q,p);
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
	p_mut = dbl(e,p_mut);
    }
    p_mut
}

pub fn tpl_k(e: MontCurve, p: Point, k: u128) -> Point {
    let mut p_mut = p;
    for _j in 0..k {
	p_mut = tpl(e,p_mut);
    }
    p_mut
}

// j-invariant:
// 256*(a^2-3)^3/(a^2-4);
pub fn j_inv(e: MontCurve) -> Fp2 {
    let (a, _) = e;

    let t0 = fp2sqr(a);
    let jinv = fp2fromfp(Fp::from_literal(3));
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

    let t1 = fp2fromfp(Fp::from_literal(4));
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
    let t3 = fp2mul(t1,x2);
    let t3 = fp2add(t3,t3);
    let t3 = fp2sub(t2,t3);
    let t3 = fp2add(t3,x2);
    let t3 = fp2mul(y, t3);
    let t2 = fp2sub(t2, x);
    let t1 = fp2sub(x, x2);
    let t1 = fp2inv(t1);
    let x3 = fp2mul(t2, t1);
    let t1 = fp2sqr(t1);
    let y3 = fp2mul(t3,t1);
    (x3,y3)
}

pub fn curve_2_iso(p2: Point, e: MontCurve) -> MontCurve {

    // a2:=2*(1-2*x2^2);
    // b2:=x2*b;

    let (x2, _) = p2;
    let (_, b) = e;

    let t1 = fp2sqr(x2);
    let t1 = fp2add(t1,t1);
    let t1 = fp2sub(fp2fromfp(Fp::ONE()), t1);
    let a2 = fp2add(t1,t1);
    let b2 = fp2mul(x2,b);
    (a2, b2)
}

#[allow(unused_assignments)]
pub fn iso_2_ea(e: MontCurve, s: Point) -> MontCurve {
    let mut e_mut = e;
    let mut s_mut = s;

    let mut t = (fp2zero(), fp2zero());

    for i in 1..4 {
	t = dbl_k(e_mut, s_mut, 216 - i); // compute point of order 2
	e_mut = curve_2_iso(t, e_mut);    // compute codomain of the iso corresponding to s_mut

	s_mut = eval_2_iso(t, s_mut);     // carry s to iso curve
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

    let mut t = (fp2zero(), fp2zero());

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
    let t1 = fp2mul(t1,x3);
    let t2 = fp2sqr(x3);
    let t2 = fp2mul(x, t2);
    let t3 = fp2add(t2,t2);
    let t2 = fp2add(t2,t3);
    let t1 = fp2sub(t1,t2);
    let t1 = fp2add(t1,x);
    let t1 = fp2add(t1,x3);

    let t2 = fp2sub(x,x3);
    let t2 = fp2inv(t2);
    let t3 = fp2sqr(t2);
    let t2 = fp2mul(t2,t3);

    let t4 = fp2mul(x,x3);
    let t4 = fp2sub(t4,fp2fromfp(Fp::ONE()));

    let t1 = fp2mul(t4,t1);
    let t1 = fp2mul(t1,t2);

    let t2 = fp2sqr(t4);
    let t2 = fp2mul(t2,t3);

    let iso_x = fp2mul(x,t2);
    let iso_y = fp2mul(y,t1);

    (iso_x,iso_y)
}

pub fn curve_3_iso(p3: Point, e: MontCurve) -> MontCurve {
    let (x3, _) = p3;
    let (a,b) = e;

    let t1 = fp2sqr(x3);
    let iso_b = fp2mul(b,t1);

    let t1 = fp2add(t1,t1);
    let t2 = fp2add(t1,t1);
    let t1 = fp2add(t1,t2);
    let t1 = fp2sub(t1,fp2fromfp(Fp::from_literal(6)));
    let t2 = fp2mul(a,x3);
    let t1 = fp2sub(t2,t1);
    let iso_a = fp2mul(t1,x3);

    (iso_a, iso_b)
}

#[allow(unused_assignments)]
pub fn iso_3_eb(e: MontCurve, s: Point) -> MontCurve {
    let mut e_mut = e;
    let mut s_mut = s;

    let mut t = (fp2zero(), fp2zero());

    for i in 1..4 {
	t = tpl_k(e_mut, s_mut, 137 - i); // compute point of order 2
	e_mut = curve_3_iso(t, e_mut);    // compute codomain of the iso corresponding to s_mut

	s_mut = eval_3_iso(t, s_mut);     // carry s to iso curve
    }

    e_mut
}

#[allow(unused_assignments)]
pub fn iso_3_eb_basis(e: MontCurve, s: Point, p: Point, q: Point) -> MontCurveBasis {
    let mut e_mut = e;
    let mut s_mut = s;
    let mut p_mut = p;
    let mut q_mut = q;

    let mut t = (fp2zero(), fp2zero());

    for i in 1..4 {
	t = tpl_k(e_mut, s_mut, 137 - i);
	e_mut = curve_3_iso(t, e_mut);

	s_mut = eval_3_iso(t, s_mut);

	p_mut = eval_3_iso(t, p_mut);
	q_mut = eval_3_iso(t, q_mut);
    }

    (e_mut, p_mut, q_mut)
}

pub fn a_sidh_isogen(sk: ASc, e: MontCurve, p_a: Point, q_a: Point, p_b: Point, q_b: Point) -> MontCurveBasis {
    // S:=P2+SK_2*Q2;
    let s = a_dbl_and_add(e,sk,q_a);
    let s = add(e,p_a,s);

    iso_2_ea_basis(e,s,p_b,q_b)
}

pub fn b_sidh_isogen(sk: BSc, e: MontCurve, p_b: Point, q_b: Point, p_a: Point, q_a: Point) -> MontCurveBasis {
    // S:=P2+SK_2*Q2;
    let s = b_dbl_and_add(e,sk,q_b);
    let s = add(e,p_b,s);

    iso_3_eb_basis(e,s,p_a,q_a)
}

pub fn a_sidh_isoex(sk: ASc, e: MontCurveBasis) -> MontCurve {
    let (e,p,q) = e;
    let s = a_dbl_and_add(e,sk,q);
    let s = add(e,p,s);

    iso_2_ea(e,s)
}

pub fn b_sidh_isoex(sk: BSc, e: MontCurveBasis) -> MontCurve {
    let (e,p,q) = e;
    let s = b_dbl_and_add(e,sk,q);
    let s = add(e,p,s);

    iso_3_eb(e,s)
}

/** Projective implementation
 ******************************/

// i just reuse the affine point type Point for (x,z) projective points (i.e. projective points with y omitted)
// this is maybe not the best
// type PPoint = (Fp2, Fp2);

pub fn _a24(a: Fp2, c: Fp2) -> Fp2 {
    let a24 = fp2add(c,c);
    fp2add(a,a24)
}

pub fn _c24(c: Fp2) -> Fp2 {
    let c24 = fp2add(c,c);
    fp2add(c24, c24)
}

pub fn xdbl(p: Point, a24: Fp2, c24: Fp2) -> Point {
    let (x,z) = p;

    let t0 = fp2sub(x,z);
    let t1 = fp2add(x,z);
    let t0 = fp2sqr(t0);
    let t1 = fp2sqr(t1);
    let z  = fp2mul(c24,t0);
    let x  = fp2mul(t1,z);
    let t1 = fp2sub(t1,t0);
    let t0 = fp2mul(a24,t1);
    let z  = fp2add(z,t0);
    let z  = fp2mul(z,t1);

    (x,z)
}

pub fn xdbl_e(p: Point, a24: Fp2, c24: Fp2, e: u128) -> Point {
    let mut p_mut = p;

    for _i in 0..e {
	p_mut = xdbl(p_mut, a24, c24);
    }

    p_mut
}

pub fn j_inv_p(a: Fp2, c: Fp2) -> Fp2 {
    let j_inv = fp2sqr(a);
    let t1 = fp2sqr(c);

    let t0 = fp2add(t1,t1);
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
    let (x,z) = p;

    // a = 2*(z^2 - 2*x^2)
    // c = z^2

    let a = fp2sqr(x);
    let a = fp2add(a,a); // why do I have to add this line
    let c = fp2sqr(z);
    let a = fp2sub(c,a);
    let a = fp2add(a,a); // why do I have to add this line

    (a,c)
}

pub fn eval_2_isog(p: Point, q: Point) -> Point {
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

// test projective double against affine double
#[cfg(test)]
#[test]
fn test_xdbl() {
    let pxz = ((Fp::from_hex(XPA0), Fp::from_hex(XPA1)), fp2one());
    let p = ((Fp::from_hex(XPA0), Fp::from_hex(XPA1)), (Fp::from_hex(YPA0), Fp::from_hex(YPA1)));
    let a = fp2fromfp(Fp::from_literal(A));
    let b = fp2fromfp(Fp::from_literal(B));
    let c = fp2fromfp(Fp::from_literal(C));

    let a24 = _a24(a, c);
    let c24 = _c24(c);
    let dbl_xp = xdbl(pxz,a24,c24);
    let z_inv = fp2inv(dbl_xp.1);
    let x = fp2mul(dbl_xp.0, z_inv);

    let dbl_p = dbl((a,b), p);

    assert_eq!(x, dbl_p.0)
}

// test projective iterated double against affine version
#[cfg(test)]
#[test]
fn test_xdbl_e() {
    let pxz = ((Fp::from_hex(XPA0), Fp::from_hex(XPA1)), fp2one());
    let p = ((Fp::from_hex(XPA0), Fp::from_hex(XPA1)), (Fp::from_hex(YPA0), Fp::from_hex(YPA1)));
    let a = fp2fromfp(Fp::from_literal(A));
    let b = fp2fromfp(Fp::from_literal(B));
    let c = fp2fromfp(Fp::from_literal(C));

    let a24 = _a24(a, c);
    let c24 = _c24(c);
    let dbl_xp = xdbl_e(pxz,a24,c24, EA - 1);
    let z_inv = fp2inv(dbl_xp.1);
    let x = fp2mul(dbl_xp.0, z_inv);

    let dbl_p = dbl_k((a,b), p, EA - 1);

    assert_eq!(x, dbl_p.0);
}

#[cfg(test)]
#[test]
fn test_j_inv() {
    let a = fp2fromfp(Fp::from_literal(A));
    let b = fp2fromfp(Fp::from_literal(B));
    let c = fp2fromfp(Fp::from_literal(C));

    let jinv_p = j_inv_p(a,c);
    let jinv   = j_inv((a,b));

    assert_eq!(jinv_p, jinv)
}

//

#[cfg(test)]
#[test]
fn test_get_2_isog() {
    let pxz = ((Fp::from_hex(XPA0), Fp::from_hex(XPA1)), fp2one());
    let p = ((Fp::from_hex(XPA0), Fp::from_hex(XPA1)), (Fp::from_hex(YPA0), Fp::from_hex(YPA1)));
    let a = fp2fromfp(Fp::from_literal(A));
    let b = fp2fromfp(Fp::from_literal(B));
    let c = fp2fromfp(Fp::from_literal(C));

    let dbl_p = dbl_k((a,b), p, EA - 1);

    let a24    = _a24(a, c);
    let c24    = _c24(c);
    let dbl_xp = xdbl_e(pxz,a24,c24, EA - 1);

    let (iso_a, iso_b) = curve_2_iso(dbl_p, (a,b));
    let (a, c) = get_2_isog(dbl_xp);

    let jinv   = j_inv((iso_a,iso_b));
    let jinv_p = j_inv_p(a,c);

    assert_eq!(jinv, jinv_p)
}


#[allow(dead_code)]
pub fn main() {


    let pxz = ((Fp::from_hex(XPA0), Fp::from_hex(XPA1)), fp2one());
    let p = ((Fp::from_hex(XPA0), Fp::from_hex(XPA1)), (Fp::from_hex(YPA0), Fp::from_hex(YPA1)));
    let a = fp2fromfp(Fp::from_literal(A));
    let b = fp2fromfp(Fp::from_literal(B));
    let c = fp2fromfp(Fp::from_literal(C));

    let dbl_p = dbl_k((a,b), p, EA - 1);

    let a24    = _a24(a, c);
    let c24    = _c24(c);
    let dbl_xp = xdbl_e(pxz,a24,c24, EA - 1);

    println!("{:?}", dbl_xp);

    // let (iso_a, iso_b) = curve_2_iso(dbl_p, (a,b));
    let (a, c) = get_2_isog(dbl_xp);
    println!("{:?}", (a, c));

    // let jinv   = j_inv((iso_a,iso_b));
    // println!("{:?}", jinv);

    let jinv_p = j_inv_p(a,c);
    println!("{:?}", jinv_p);

    // let _inf = (fp2zero(), fp2zero());

    // let k_a = ASc::from_literal(57);
    // let k_b = BSc::from_literal(1234);

    // println!("p_a: {:?}", p_a);
    // println!("q_a: {:?}", q_a);
    // println!("k_a: {:?}", k_a);
    // println!("p_b: {:?}", p_b);
    // println!("q_b: {:?}", q_b);
    // println!("k_b: {:?}", k_b);
    // let p_a = ((Fp::from_hex(XPA0),
    //		Fp::from_hex(XPA1)),
    //	       (Fp::from_hex(YPA0),
    //		Fp::from_hex(YPA1)));
    // let q_a = ((Fp::from_hex(XQA0),
    //		Fp::from_hex(XQA1)),
    //	       (Fp::from_hex(YQA0),
    //		Fp::from_hex(YQA1)));

    // let p_b = ((Fp::from_hex(XPB0),
    //		Fp::from_hex(XPB1)),
    //	       (Fp::from_hex(YPB0),
    //		Fp::from_hex(YPB1)));
    // let q_b = ((Fp::from_hex(XQB0),
    //		Fp::from_hex(XQB1)),
    //	       (Fp::from_hex(YQB0),
    //		Fp::from_hex(YQB1)));

    // let e = (fp2fromfp(Fp::from_literal(A)), fp2fromfp(Fp::from_literal(B)));
    // let _c = fp2fromfp(Fp::from_literal(C));



    // let pk_a = a_sidh_isogen(k_a, e, p_a, q_a, p_b, q_b);
    // let pk_b = b_sidh_isogen(k_b, e, p_b, q_b, p_a, q_a);

    // let shared_key_a = a_sidh_isoex(k_a, pk_b);
    // let shared_key_b = b_sidh_isoex(k_b, pk_a);

    // let q_a3 = tpl(e, q_a);
    // println!{"3 * s_a: {:?}", q_a3};

    // let s_a = a_dbl_and_add(e, k_a, q_a);
    // let s_a = add(e, s_a, p_a);

    // println!("s_a = p_a + k_a * q_a:");
    // println!("{:?}", s_a.0.1);
    // println!("{:?}", s_a.0.0);
    // println!("{:?}", s_a.1.1);
    // println!("{:?}", s_a.1.0);

    // let s_b = b_dbl_and_add(e, k_b, q_b);
    // let s_b = add(e, s_b, p_b);

    // println!("s_b = p_b + k_b * q_b:");
    // println!("{:?}", s_b.0.1);
    // println!("{:?}", s_b.0.0);
    // println!("{:?}", s_b.1.1);
    // println!("{:?}", s_b.1.0);

    // let pk_a = iso_2_ea_basis(e, s_a, p_b, q_b);
    // println!{"pk_a:"}
    // println!("{:?}", pk_a.0);
    // println!("{:?}", pk_a.1);
    // println!("{:?}", pk_a.2);

    // let pk_b = iso_3_eb_basis(e, s_b, p_a, q_a);
    // println!{"pk_b:"}
    // println!("{:?}", pk_b.0);
    // println!("{:?}", pk_b.1);
    // println!("{:?}", pk_b.2);

    // let s_a = a_dbl_and_add(pk_b.0,k_a,pk_b.2);
    // let s_a = add(pk_b.0,pk_b.1,s_a);
    // let shared_key_a = iso_2_ea(pk_b.0, s_a);

    // println!{"shared_key_a:"}
    // println!("{:?}", shared_key_a);

    // let s_b = b_dbl_and_add(pk_a.0,k_b,pk_a.2);
    // let s_b = add(pk_a.0,pk_a.1,s_b);
    // let shared_key_b = iso_3_eb(pk_a.0, s_b);

    // println!{"shared_key_b:"}
    // println!("{:?}", shared_key_b);

    // println!("j invariant:");
    // println!("{:?}", j_inv(e));

    // let q_ax12 = a_dbl_and_add(e, ASc::from_literal(12), q_a);
    // println!("12 times q_a:");
    // println!("{:?}", q_ax12.0.1);
    // println!("{:?}", q_ax12.0.0);
    // println!("{:?}", q_ax12.1.1);
    // println!("{:?}", q_ax12.1.0);

    // let s = add(e,p_a,q_ax12);
    // println!("p_a + 12 times q_a:");
    // println!("{:?}", s.0.1);
    // println!("{:?}", s.0.0);
    // println!("{:?}", s.1.1);
    // println!("{:?}", s.1.0);


    // let s2 = dbl_k(e,s,215);
    // println!("s2:");
    // println!("{:?}", s2.0.1);
    // println!("{:?}", s2.0.0);
    // println!("{:?}", s2.1.1);
    // println!("{:?}", s2.1.0);

    // let e2 = curve_2_iso(s2, e);
    // println!("e2:");
    // println!("{:?}", e2.0);
    // println!("{:?}", e2.1);

    // println!("j invariant of e2:");
    // println!("{:?}", j_inv(e2));

    // let iso_s = eval_2_iso(s2,s);
    // println!("iso_s:");
    // println!("{:?}", iso_s.0.1);
    // println!("{:?}", iso_s.0.0);
    // println!("{:?}", iso_s.1.1);
    // println!("{:?}", iso_s.1.0);

    // let e2 = iso_2_ea(e,s);

    // println!("s2:");
    // println!("{:?}", s2.0.1);
    // println!("{:?}", s2.0.0);
    // println!("{:?}", s2.1.1);
    // println!("{:?}", s2.1.0);

    // println!("e2:");
    // println!("{:?}", e2.0);
    // println!("{:?}", e2.1);
}
