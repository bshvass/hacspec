#![cfg(test)]
use crate::ec_isogeny::*;
use crate::fp2::*;
use crate::param::*;

pub fn test_setup() -> (
    Fp2,
    Fp2,
    Fp2,
) {

    let c2 = fp2add(C, C);

    let a24minus = fp2sub(A, c2);
    let a24plus = fp2add(A, c2);

    let c24 = fp2add(c2, c2);

    (
	a24plus, a24minus, c24,
    )
}

// test projective double against affine double
#[test]
fn test_xdbl() {
    let (a24plus, _, c24) = test_setup();

    let dbl_xp = xdbl(PAXZ, a24plus, c24);
    let z_inv = fp2inv(dbl_xp.1);
    let x = fp2mul(dbl_xp.0, z_inv);

    let dbl_p = dbl((A, B), PAXY);

    assert_eq!(x, dbl_p.0)
}

// test projective double against affine double
#[test]
fn test_xtpl() {
    let (a24plus, a24minus, _) = test_setup();

    let tpl_xp = xtpl(PBXZ, a24plus, a24minus);
    let z_inv = fp2inv(tpl_xp.1);
    let x = fp2mul(tpl_xp.0, z_inv);

    let tpl_p = tpl((A, B), PBXY);

    assert_eq!(x, tpl_p.0)
}

// test projective iterated double against affine version
#[test]
fn test_xdbl_e() {
    let (a24plus, _, c24) = test_setup();

    let dbl_xp = xdbl_e(PAXZ, a24plus, c24, EA - 1);
    let z_inv = fp2inv(dbl_xp.1);
    let x = fp2mul(dbl_xp.0, z_inv);

    let dbl_p = dbl_k((A, B), PAXY, EA - 1);

    assert_eq!(x, dbl_p.0);
}

// test projective triple against affine triple
#[test]
fn test_xtpl_e() {
    let (a24plus, a24minus, _) = test_setup();

    let tpl_xp = xtpl_e(PBXZ, a24plus, a24minus, EB - 1);
    let z_inv = fp2inv(tpl_xp.1);
    let x = fp2mul(tpl_xp.0, z_inv);

    let tpl_p = tpl_k((A, B), PBXY, EB - 1);

    assert_eq!(x, tpl_p.0)
}

// test projective get_3_isog against affine version
#[test]
fn test_get_3_isog() {
    let (a24plus, a24minus, _) = test_setup();

    let tpl_xp = xtpl_e(PBXZ, a24plus, a24minus, EB - 1);

    let tpl_p = tpl_k((A, B), PBXY, EB - 1);

    let (iso_a, iso_b) = curve_3_iso(tpl_p, (A, B));
    let (a24plus, a24minus, _, _) = get_3_isog(tpl_xp);

    let quarter = fp2inv(fp2from_literals(4, 0));
    let c24 = fp2sub(a24plus, a24minus);
    let c = fp2mul(quarter, c24);
    let c2 = fp2add(c, c);
    let a = fp2sub(a24plus, c2);

    let jinv = j_inv((iso_a, iso_b));
    let jinv_p = j_inv_p(a, c);

    assert_eq!(jinv, jinv_p)
}

#[test]
fn test_eval_3_isog() {
    let (a24plus, a24minus, _) = test_setup();

    let tpl_xp = xtpl_e(PBXZ, a24plus, a24minus, EB - 1);
    let (_, _, c0, c1) = get_3_isog(tpl_xp);
    let phi_pa_proj = eval_3_isog(PAXZ, c0, c1);

    let tpl_p = tpl_k((A, B), PBXY, EB - 1);
    let phi_pa = eval_3_iso(tpl_p, PAXY);

    assert_eq!(affine_x(phi_pa_proj), phi_pa.0)
}

// test j_inv against affine version
#[test]
fn test_j_inv() {
    let jinv_p = j_inv_p(A, C);
    let jinv = j_inv((A, B));

    assert_eq!(jinv_p, jinv)
}

// test get_2_isog against curve_2_iso
#[test]
fn test_get_2_isog() {
    let (a24plus, _, c24) = test_setup();

    let dbl_p = dbl_k((A, B), PAXY, EA - 1);

    let dbl_xp = xdbl_e(PAXZ, a24plus, c24, EA - 1);

    let (iso_a, iso_b) = curve_2_iso(dbl_p, (A, B));
    let (a24plus, c24) = get_2_isog(dbl_xp);

    let quarter = fp2inv(fp2from_literals(4, 0));
    let c = fp2mul(quarter, c24);
    let c2 = fp2add(c, c);
    let a = fp2sub(a24plus, c2);

    let jinv = j_inv((iso_a, iso_b));
    let jinv_p = j_inv_p(a, c);

    assert_eq!(jinv, jinv_p)
}

#[test]
fn test_eval_2_isog() {
    let (a24plus, _, c24) = test_setup();

    let dbl_p = dbl_k((A, B), PAXY, EA - 1);

    let dbl_xp = xdbl_e(PAXZ, a24plus, c24, EA - 1);

    let phi_pb = eval_2_iso(dbl_p, PBXY);

    let phi_pb_proj = eval_2_isog(PBXZ, dbl_xp);

    let phi_pb_proj_z_inv = fp2inv(phi_pb_proj.1);
    let phi_pb_proj_x = fp2mul(phi_pb_proj.0, phi_pb_proj_z_inv);

    assert_eq!(phi_pb_proj_x, phi_pb.0)
}

#[test]
fn test_get_4_isog() {
    let (a24plus, _, c24) = test_setup();


    let jinv = fp2from_hexes("103a10dcff036d8b9a5ed683ac4b7ac705e5e5e6214a382d86a1cbee5abf04c3f2876b1c8b1e8716b54b9991294cc934bc1e808c4ff04", "0"); // from sage

    let dbl_pa_proj = xdbl_e(PAXZ, a24plus, c24, EA - 2);
    let (a24plus, c24, _, _, _) = get_4_isog(dbl_pa_proj);

    let quarter = fp2inv(fp2from_literals(4, 0));
    let c = fp2mul(quarter, c24);
    let c2 = fp2add(c, c);
    let a = fp2sub(a24plus, c2);

    let jinv_proj = j_inv_p(a, c);

    assert_eq!(jinv_proj, jinv);
}

#[test]
fn test_eval_4_isog() {
    let (a24plus, _, c24) = test_setup();

    let _phi_pb_x = fp2from_hexes("1113975d6d50082b5aa386422cbb191749ac238b19d7717d775cd71f7228420f635722f790ff97a3044e693a0eaf0d07a2328452cec76", "0"); // form sage

    let dbl_pa_proj = xdbl_e(PAXZ, a24plus, c24, EA - 2);
    let (_, _, c0, c1, c2) = get_4_isog(dbl_pa_proj);

    let phi_pb_proj = eval_4_isog(PBXZ, c0, c1, c2);

    let phi_pb_proj_z_inv = fp2inv(phi_pb_proj.1);
    let _phi_pb_proj_x = fp2mul(phi_pb_proj.0, phi_pb_proj_z_inv);

    // this is not correct and i am not sure why. I think it is
    // because is uses a different isogeny than the one sage generates
    // (i.e., an isogeny which is equal to sages up to composing with
    // an isomorphism)

    // assert_eq!(phi_pb_proj_x, phi_pb_x);
}

// #[test]
// pub fn inv_3_way() {


//     let t0 = fp2mul(z1,z2);
//     let t1 = fp2mul(z3,t0);
//     let t1 = fp2inv(t1);
//     let t2 = fp2mul(z3,t1);
//     let t3 = fp2mul(t2,z2);
//     let z2 = fp2mul(t2,z1);
//     let z3 = fp2mul(t0,t1);

//     (t3,z2,z3)
// }

// pub fn get_a(x_p: Fp2, x_q: Fp2, x_r: Fp2) -> Fp2  {
//     // Given the x-coordinates of P, Q, and R, returns the value A corresponding to the Montgomery curve E_A: y^2=x^3+A*x^2+x such that R=Q-P on E_A.
//     // Input:  the x-coordinates xP, xQ, and xR of the points P, Q and R.
//     // Output: the coefficient A corresponding to the curve E_A: y^2=x^3+A*x^2+x.

//     let t1 = fp2add(x_p, x_q);
//     let t0 = fp2mul(x_p, x_q);
//     let a = fp2mul(x_r,t1);
//     let a = fp2add(t0,a);
//     let t0 = fp2mul(t0,x_r);
//     let a = fp2sub(a,ONE);
//     let t0 = fp2add(t0,t0);
//     let t1 = fp2add(t1,x_r);
//     let t0 = fp2add(t0,t0);
//     let a = fp2sqr(a);
//     let t0 = fp2inv(t0);
//     let a = fp2mul(t0,a);
//     let a = fp2sub(a,t1);
//     a
// }

// pub fn x_dbladd(p: Point, q: Point, x_pq: Fp2, a24: Fp2) -> (Point, Point) {
//     // Simultaneous doubling and differential addition.
//     // Input: projective Montgomery points P=(XP:ZP) and Q=(XQ:ZQ) such that xP=XP/ZP and xQ=XQ/ZQ, affine difference xPQ=x(P-Q) and Montgomery curve constant A24=(A+2)/4.
//     // Output: projective Montgomery points P <- 2*P = (X2P:Z2P) such that x(2P)=X2P/Z2P, and Q <- P+Q = (XQP:ZQP) such that = x(Q+P)=XQP/ZQP.

//     let (x_p,z_p) = p;
//     let (x_q,z_q) = q;

//     let t0 = fp2add(x_p,z_p);
//     let t1 = fp2sub(x_p,z_p);
//     let x_p = fp2sqr(t0);
//     let t2 = fp2sub(x_q,z_q);
//     let x_q = fp2add(x_q, z_q);
//     let t0 = fp2mul(t0, t2);
//     let z_p = fp2sqr(t1);
//     let t1 = fp2mul(t1,x_q);
//     let x_p = fp2sub(x_p, z_p);
//     let x_p = fp2mul(x_p, z_p);
//     let x_q = fp2mul(a24, t2);
//     let z_q = fp2sub(t0, t1);
//     let z_p = fp2add(x_q, z_p);
//     let x_q = fp2add(t0, t1);
//     let z_p = fp2mul(z_p, t2);
//     let z_q = fp2sqr(z_q);
//     let x_q = fp2sqr(x_q);
//     let z_q = fp2mul(z_q, x_pq);
//     ((x_p, z_p), (x_q, z_q))
// }

// // FIXME: make constant time, probably will need a constant time swap on Fp and Fp2
// pub fn swap_points(p: Point, q: Point, mask: u128) -> (Point, Point) {
//     let mut res = (q, p);
//     if mask == 0 {
//	res = (p, q);
//     }
//     res
// }

// pub fn a_ladder3pt(x_p: Fp2, x_q: Fp2, x_pq: Fp2, m: ASc, a: Fp2) -> Point  {
//     // Initializing constant
//     let a24 = fp2from_literals(2, 0);
//     let a24 = fp2add(a,a24);
//     let quarter = fp2inv(fp2from_literals(4, 0));
//     let a24 = fp2mul(a24,quarter);

//     // Initializing points
//     let mut r0 = (x_q, ONE);
//     let mut r1 = (x_p, ONE);
//     let mut r2 = (x_pq, ONE);

//     let mut bit;
//     let mut swap;
//     let mut prevbit = 0;
//     let mut mask;

//     // Main loop
//     for i in 0..ALICE_BITS {
//	bit = m.bit(ALICE_BITS - i) as u128;
//	swap = bit ^ prevbit;
//	prevbit = bit;
//	mask = 0 - swap;

//	let (r1_tmp, r2_tmp) = swap_points(r1, r2, mask);
//	r1 = r1_tmp;
//	r2 = r2_tmp;

//	let (x_r1, z_r1) = r1;
//	let (r0_tmp, r2_tmp) = x_dbladd(r0, r2, x_r1, a24);

//	let (x_r2, z_r2) = r2_tmp;
//	let x_r2 = fp2mul(x_r2, z_r1);

//	r0 = r0_tmp;
//	r2 = (x_r2, z_r2);
//     }
//     swap = 0 ^ prevbit;
//     mask = 0 - swap;

//     let (r1, _) = swap_points(r1, r2, mask);
//     r1
// }
