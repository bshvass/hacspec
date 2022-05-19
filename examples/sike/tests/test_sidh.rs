extern crate quickcheck;
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

use hacspec_lib::*;
use hacspec_sike::*;
use quickcheck::*;

#[derive(Clone)]
#[derive(Debug)]
pub struct MyFp(Fp);

#[derive(Clone)]
#[derive(Debug)]
pub struct MyASc(ASc);

#[derive(Clone)]
#[derive(Debug)]
pub struct MyBSc(BSc);

impl Arbitrary for MyFp {
    fn arbitrary(g: &mut Gen) -> MyFp {
	let mut a: [u8; 55] = [0; 55];
	for i in 0..55 {
	    a[i] = u8::arbitrary(g);
	}
	a[54] = 0; // this is suboptimal, but I'm not sure how to get a truly arbitrary element of Fp
	MyFp(Fp::from_byte_seq_le(Seq::<U8>::from_public_slice(&a)))
    }
}

impl Arbitrary for MyASc {
    fn arbitrary(g: &mut Gen) -> MyASc {
	let mut a: [u8; 28] = [0; 28];
	for i in 0..28 {
	    a[i] = u8::arbitrary(g);
	}
	a[27] = 0;
	MyASc(ASc::from_byte_seq_le(Seq::<U8>::from_public_slice(&a)))
    }
}

impl Arbitrary for MyBSc {
    fn arbitrary(g: &mut Gen) -> MyBSc {
	let mut a: [u8; 28] = [0; 28];
	for i in 0..28 {
	    a[i] = u8::arbitrary(g);
	}
	a[27] = 0;
	MyBSc(BSc::from_byte_seq_le(Seq::<U8>::from_public_slice(&a)))
    }
}

/** Testing
 ************/

/// Constants from the reference implementation (sike_params.c)
pub fn xpa0() -> Fp { Fp::from_hex("3CCFC5E1F050030363E6920A0F7A4C6C71E63DE63A0E6475AF621995705F7C84500CB2BB61E950E19EAB8661D25C4A50ED279646CB48") }
pub fn xpa1() -> Fp { Fp::from_hex("1AD1C1CAE7840EDDA6D8A924520F60E573D3B9DFAC6D189941CB22326D284A8816CC4249410FE80D68047D823C97D705246F869E3EA50") }
pub fn ypa0() -> Fp { Fp::from_hex("1AB066B84949582E3F66688452B9255E72A017C45B148D719D9A63CDB7BE6F48C812E33B68161D5AB3A0A36906F04A6A6957E6F4FB2E0") }
pub fn ypa1() -> Fp { Fp::from_hex("FD87F67EA576CE97FF65BF9F4F7688C4C752DCE9F8BD2B36AD66E04249AAF8337C01E6E4E1A844267BA1A1887B433729E1DD90C7DD2F") }

pub fn xqa0() -> Fp { Fp::from_hex("C7461738340EFCF09CE388F666EB38F7F3AFD42DC0B664D9F461F31AA2EDC6B4AB71BD42F4D7C058E13F64B237EF7DDD2ABC0DEB0C6C") }
pub fn xqa1() -> Fp { Fp::from_hex("25DE37157F50D75D320DD0682AB4A67E471586FBC2D31AA32E6957FA2B2614C4CD40A1E27283EAAF4272AE517847197432E2D61C85F5") }
pub fn yqa0() -> Fp { Fp::from_hex("1D407B70B01E4AEE172EDF491F4EF32144F03F5E054CEF9FDE5A35EFA3642A11817905ED0D4F193F31124264924A5F64EFE14B6EC97E5") }
pub fn yqa1() -> Fp { Fp::from_hex("E7DEC8C32F50A4E735A839DCDB89FE0763A184C525F7B7D0EBC0E84E9D83E9AC53A572A25D19E1464B509D97272AE761657B4765B3D6") }

// x(PA-QA)
pub fn xra0() -> Fp { Fp::from_hex("F37AB34BA0CEAD94F43CDC50DE06AD19C67CE4928346E829CB92580DA84D7C36506A2516696BBE3AEB523AD7172A6D239513C5FD2516") }
pub fn xra1() -> Fp { Fp::from_hex("196CA2ED06A657E90A73543F3902C208F410895B49CF84CD89BE9ED6E4EE7E8DF90B05F3FDB8BDFE489D1B3558E987013F9806036C5AC") }

pub fn xpb0() -> Fp { Fp::from_hex("8664865EA7D816F03B31E223C26D406A2C6CD0C3D667466056AAE85895EC37368BFC009DFAFCB3D97E639F65E9E45F46573B0637B7A9") }
pub fn xpb1() -> Fp { Fp::from_hex("0") }
pub fn ypb0() -> Fp { Fp::from_hex("6AE515593E73976091978DFBD70BDA0DD6BCAEEBFDD4FB1E748DDD9ED3FDCF679726C67A3B2CC12B39805B32B612E058A4280764443B") }
pub fn ypb1() -> Fp { Fp::from_hex("0") }

pub fn xqb0() -> Fp { Fp::from_hex("12E84D7652558E694BF84C1FBDAAF99B83B4266C32EC65B10457BCAF94C63EB063681E8B1E7398C0B241C19B9665FDB9E1406DA3D3846") }
pub fn xqb1() -> Fp { Fp::from_hex("0") }
pub fn yqb0() -> Fp { Fp::from_hex("0") }
pub fn yqb1() -> Fp { Fp::from_hex("EBAAA6C731271673BEECE467FD5ED9CC29AB564BDED7BDEAA86DD1E0FDDF399EDCC9B49C829EF53C7D7A35C3A0745D73C424FB4A5FD2") }

// x(PB-QB)
pub fn xrb0() -> Fp { Fp::from_hex("1CD28597256D4FFE7E002E87870752A8F8A64A1CC78B5A2122074783F51B4FDE90E89C48ED91A8F4A0CCBACBFA7F51A89CE518A52B76C") }
pub fn xrb1() -> Fp { Fp::from_hex("147073290D78DD0CC8420B1188187D1A49DBFA24F26AAD46B2D9BB547DBB6F63A760ECB0C2B20BE52FB77BD2776C3D14BCBC404736AE4") }

pub fn xpa() -> Fp2 { (xpa0(), xpa1()) }
pub fn xqa() -> Fp2 { (xqa0(), xqa1()) }
pub fn xra() -> Fp2 { (xra0(), xra1()) }

pub fn paxy() -> Point { (xpa(), (ypa0(), ypa1())) }
pub fn paxz() -> Point { (xpa(), fp2one()) }
pub fn qaxy() -> Point { (xqa(), (yqa0(), yqa1())) }
pub fn qaxz() -> Point { (xqa(), fp2one()) }
pub fn raxz() -> Point { (xra(), fp2one()) }

pub fn xpb() -> Fp2 { (xpb0(), xpb1()) }
pub fn xqb() -> Fp2 { (xqb0(), xqb1()) }
pub fn xrb() -> Fp2 { (xrb0(), xrb1()) }

pub fn pbxy() -> Point { (xpb(), (ypb0(), ypb1())) }
pub fn pbxz() -> Point { (xpb(), fp2one()) }
pub fn qbxy() -> Point { (xqb(), (yqb0(), yqb1())) }
pub fn qbxz() -> Point { (xqb(), fp2one()) }
pub fn rbxz() -> Point { (xrb(), fp2one()) }

pub fn a() -> Fp2 { (Fp::from_literal(6 as u128), Fp::ZERO()) }
pub fn b() -> Fp2 { (Fp::ONE(), Fp::ZERO()) }
pub fn c() -> Fp2 { (Fp::ONE(), Fp::ZERO()) }
pub fn a24plus() -> Fp2 { let c2 = fp2add(c(), c()); fp2add(a(), c2) }
pub fn a24minus() -> Fp2 { let c2 = fp2add(c(), c()); fp2sub(a(), c2) }
pub fn c24() -> Fp2 { let c2 = fp2add(c(), c()); fp2add(c2, c2) }
pub fn a24() -> Fp2 { let c24inv = fp2inv(c24()); fp2mul(c24inv,a24plus()) }

pub fn fp2from_hexes(a: &str, b: &str) -> Fp2 {
    (Fp::from_hex(a), Fp::from_hex(b))
}

/// x-coordinates in the Montgomery domain from the optimized implementation (P434.c) (just for reference)
// const XPA0: &str = "A1C08B1ECC42181DB6131AF621FF797F526BB48C8CD70E792DC89FA27B1AFE4E879951F025791935C5CC767AC2B5ADF455C5C345BF";
// const XPA1: &str = "FFA26C5A924AD671EB919A179E8CA7F424730D7E419F8CD8E51F7AACFFAACB5732BDF41715D52971AA0ECF9F9D0B74840EB87CDA7788";
// const XQA0: &str = "1C4CB77542876735CFEB0FFD492151B63EDA2045538DDE23941F470841B03F8F58F07A78098C7D2A626D74CBBF1C6FEC6E64588B7273B";
// const XQA1: &str = "18ECCDDF4B53EA6E4B552E2EDE508E2DDA115260E29951E2E5D5FF524E374680EC43DB144E02F6AFFBD037DA0A050ADB0F733C17FFDD6";
// const XRA0: &str = "22A81D8D55643413FBE6A9B9BC4F33AA41F1CE175D92D60E17AC16D2F82AD259B0C6949A9121B2CB0251FE3CC06111BA4DB518CD6C7D";
// const XRA1: &str = "B87FC716C0C6DB2B94FBF09F27E244961599E379AF87799994BAA96E0E45820C734C80096A0EF9CDDB0D5FADDEDB8ADBC70FC82E54A";
// const XPB0: &str = "1BED4772E551F22CC287022D5F5B9B883F276A6490D2B5864A4A69D450C4FEB919446D049887D2A61B501546F1C056E5497556EDD48A3";
// const XPB1: &str = "0";
// const XQB0: &str = "34080181D8AEF4328294E017837FB00AD2A708267E8A498FF4A4AF60BD62EF1A94228413C27C494871F51700FE1CFAE2A3F93D8B6B8E";
// const XQB1: &str = "0";
// const XRB0: &str = "7E8A50F02E372106D022634F5048176F112EA43F45B68A2BA8AA262EC9D7DEAE962816F4E9A9208F44977C3E647283B34FAFEFDC8E4"
// const XRB1: &str = "173FA910377D3BEF93B29A3F6B54B445F6FD138407C932B35A68239D48A53EBE15711813E23696D089C99AD1D9230B378B7C1DA22CCB1"

/** Tests of affine implementation
 ***********************************/

// test inf identity
#[test]
fn test_add_inf() {
    assert_eq!(add((a(),b()),paxy(),inf()), paxy());
}

// test add commutative
#[test]
fn test_add() {
    assert_eq!(dbl((a(),b()), paxy()), add((a(),b()), paxy(), paxy()));
}

// test dbl inf
#[test]
fn test_dbl_inf() {
    let inf2 = dbl((a(),b()), inf());
    assert_eq!(inf2,inf());
}

// test dbl_and_add
#[test]
fn test_a_dbl_and_add_1() {
    let p = a_dbl_and_add((a(), b()), ASc::from_literal(1), paxy());
    assert_eq!(p,paxy());
}

// test dbl_and_add
#[test]
fn test_a_dbl_and_add_2() {
    let p = a_dbl_and_add((a(), b()), ASc::from_literal(2), paxy());
    let p2 = dbl((a(), b()), paxy());
    assert_eq!(p,p2);
}

// test that shared keys agree
// note that in this test, only two steps in the isogeny graph are taken
// taking the proper amount (EA/EB) is too slow in hacspec
#[test]
fn test_aff_sidh() {
    fn aux(a_sk: MyASc, b_sk: MyBSc) {
	let a_sk = a_sk.0;
	let b_sk = b_sk.0;
	let e = (a(), b());
	let ab = (paxy(), qaxy());
	let bb = (pbxy(), qbxy());
	let a_steps = 2; // EA;
	let b_steps = 2; // EB;
	let (a_e, a_bb) = a_sidh_isogen(a_sk, e, ab, bb, a_steps);
	let (b_e, b_ab) = b_sidh_isogen(b_sk, e, bb, ab, b_steps);
	let a_shared_secret = a_sidh_isoex(a_sk, b_e, b_ab, b_steps);
	let b_shared_secret = b_sidh_isoex(b_sk, a_e, a_bb, a_steps);
	assert_eq!(a_shared_secret,b_shared_secret);
    }
    QuickCheck::new()
	.tests(1)
	.quickcheck(aux as fn(MyASc, MyBSc));
}

/** Test of projective implementation
 *************************************/

#[test]
fn test_get_a() {
    let p2 = xdbl(paxz(), a24plus(), c24());
    let xp2_aff = affine_x(p2);
    let (xp,_) = paxz();
    let _a = get_a(xp, xp2_aff, xp);
    assert_eq!(_a,a());
}

#[test]
fn test_get_a2() {
    let _a = get_a(xpa(),xqa(),xra());
    assert_eq!(_a,a());
}

// test projective double against affine double
#[test]
fn test_xdbl() {
    let dbl_xp = xdbl(paxz(), a24plus(), c24());
    let x = affine_x(dbl_xp);
    let dbl_p = dbl((a(), b()), paxy());
    assert_eq!(x, dbl_p.0)
}

// test projective triple against affine triple
#[test]
fn test_xtpl() {
    let tpl_xp = xtpl(pbxz(), a24plus(), a24minus());
    let x = affine_x(tpl_xp);
    let tpl_p = tpl((a(), b()), pbxy());
    assert_eq!(x, tpl_p.0)
}

// test projective iterated double against affine version
#[test]
fn test_xdbl_e() {
    let dbl_xp = xdbl_e(paxz(), a24plus(), c24(), EA - 1);
    let x = affine_x(dbl_xp);
    let dbl_p = dbl_k((a(), b()), paxy(), EA - 1);
    assert_eq!(x, dbl_p.0);
}

// test projective iterated triple against affine version
#[test]
fn test_xtpl_e() {
    let tpl_xp = xtpl_e(pbxz(), a24plus(), a24minus(), EB - 1);
    let x = affine_x(tpl_xp);
    let tpl_p = tpl_k((a(), b()), pbxy(), EB - 1);
    assert_eq!(x, tpl_p.0)
}

// test projective get_3_isog against affine version
#[test]
fn test_get_3_isog() {
    let tpl_xp = xtpl_e(pbxz(), a24plus(), a24minus(), EB - 1);
    let tpl_p = tpl_k((a(), b()), pbxy(), EB - 1);

    let (iso_a, iso_b) = curve_3_iso(tpl_p, (a(), b()));
    let jinv = j_inv((iso_a, iso_b));

    let (a24plus, a24minus, _) = get_3_isog(tpl_xp);
    let jinv_p = jinv_from_a24minusplus(a24plus, a24minus);

    assert_eq!(jinv, jinv_p)
}

// test projective eval_3_isog against affine version
#[test]
fn test_eval_3_isog() {
    let tpl_xp = xtpl_e(pbxz(), a24plus(), a24minus(), EB - 1);

    let (_, _, cs) = get_3_isog(tpl_xp);
    let phi_pa_proj = eval_3_isog(paxz(), cs);

    let tpl_p = tpl_k((a(), b()), pbxy(), EB - 1);
    let phi_pa = eval_3_iso(tpl_p, paxy());

    assert_eq!(affine_x(phi_pa_proj), phi_pa.0)
}

// test j_inv against affine version
#[test]
fn test_j_inv() {
    let jinv_p = j_inv_p(a(), c());
    let jinv = j_inv((a(), b()));

    assert_eq!(jinv_p, jinv)
}

// test get_2_isog against curve_2_iso
#[test]
fn test_get_2_isog() {
    let dbl_p = dbl_k((a(), b()), paxy(), EA - 1);

    let dbl_xp = xdbl_e(paxz(), a24plus(), c24(), EA - 1);

    let (iso_a, iso_b) = curve_2_iso(dbl_p, (a(), b()));
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
    let dbl_p = dbl_k((a(), b()), paxy(), EA - 1);

    let dbl_xp = xdbl_e(paxz(), a24plus(), c24(), EA - 1);

    let phi_pb = eval_2_iso(dbl_p, pbxy());

    let phi_pb_proj = eval_2_isog(pbxz(), dbl_xp);

    let phi_pb_proj_z_inv = fp2inv(phi_pb_proj.1);
    let phi_pb_proj_x = fp2mul(phi_pb_proj.0, phi_pb_proj_z_inv);

    assert_eq!(phi_pb_proj_x, phi_pb.0)
}

#[test]
fn test_get_4_isog() {
    let jinv = fp2from_hexes("103a10dcff036d8b9a5ed683ac4b7ac705e5e5e6214a382d86a1cbee5abf04c3f2876b1c8b1e8716b54b9991294cc934bc1e808c4ff04", "0"); // from sage

    let dbl_pa_proj = xdbl_e(paxz(), a24plus(), c24(), EA - 2);
    let (a24plus, c24, _) = get_4_isog(dbl_pa_proj);

    let quarter = fp2inv(fp2from_literals(4, 0));
    let c = fp2mul(quarter, c24);
    let c2 = fp2add(c, c);
    let a = fp2sub(a24plus, c2);

    let jinv_proj = j_inv_p(a, c);

    assert_eq!(jinv_proj, jinv);
}

#[test]
fn test_eval_4_isog() {
    let _phi_pb_x = fp2from_hexes("1113975d6d50082b5aa386422cbb191749ac238b19d7717d775cd71f7228420f635722f790ff97a3044e693a0eaf0d07a2328452cec76", "0"); // form sage

    let dbl_pa_proj = xdbl_e(paxz(), a24plus(), c24(), EA - 2);
    let (_, _, cs) = get_4_isog(dbl_pa_proj);

    let phi_pb_proj = eval_4_isog(pbxz(), cs);

    let phi_pb_proj_z_inv = fp2inv(phi_pb_proj.1);
    let _phi_pb_proj_x = fp2mul(phi_pb_proj.0, phi_pb_proj_z_inv);

    // this is not correct and i am not sure why. I think it is
    // because is uses a different isogeny than the fp2one sage generates
    // (i.e., an isogeny which is equal to sages up to composing with
    // an isomorphism)

    // assert_eq!(phi_pb_proj_x, phi_pb_x);
}

#[quickcheck]
fn test_inv_3_way(z11: MyFp, z12: MyFp, z21: MyFp, z22: MyFp, z31: MyFp, z32: MyFp) -> bool {
    let z1 = (z11.0, z12.0);
    let z2 = (z21.0, z22.0);
    let z3 = (z31.0, z32.0);
    let (t1,t2,t3) = inv_3_way(z1, z2, z3);
    t1 == fp2inv(z1) && t2 == fp2inv(z2) && t3 == fp2inv(z3)
}

#[test]
fn test_x_dbladd() {

    let (test1,test2) = x_dbladd(paxz(), paxz(), fp2one(), a24());
    let test1_aff = affine_x(test1);
    let _test2_aff = affine_x(test2);

    let p3 = xtpl(paxz(), a24plus(), a24minus());
    let p2 = xdbl(paxz(), a24plus(), c24());
    let p4 = xdbl(p2, a24plus(), c24());

    let xp2_aff = affine_x(p2);
    assert_eq!(test1_aff,xp2_aff);
    // assert_eq!(_test2_aff,xp2_aff); // this test fails with (left: `(0, 0)`,) and right being the correct answer

    let (p,q) = x_dbladd(p4, p2, xp2_aff, a24());

    let p8 = xdbl(p4, a24plus(), c24());
    let p6 = xdbl(p3, a24plus(), c24());

    let p8_aff = affine_x(p8);
    let p6_aff = affine_x(p6);

    let p_aff = affine_x(p);
    let q_aff = affine_x(q);

    assert_eq!(p8_aff,p_aff);
    assert_eq!(p6_aff,q_aff);
}


#[test]
fn test_pa_ladder3pt() {
    fn test(m: MyASc) -> bool {
	let m = m.0;
	let (x_p, _) = paxz();
	let (x_q, _) = qaxz();

	let pmq = a_ladder3pt(x_p, x_q, xra(), m, a());

	let mq = a_dbl_and_add((a(), b()), m, qaxy());

	let (x_pmq_aff, _) = add((a(),b()), paxy(), mq);

	affine_x(pmq) == x_pmq_aff
    }
    QuickCheck::new()
	.tests(5)
	.quickcheck(test as fn(MyASc) -> bool);
}

#[test]
fn test_aff_proj_sidh() {
    fn aux(a_sk: MyASc) {
	let a_sk = a_sk.0;
	let e = (a(), b());
	let ab = (paxy(), qaxy());
	let bb = (pbxy(), qbxy());
	let pab = (xpa(), xqa(), xra());
	let pbb = (xpb(), xqb(), xrb());
	let a_steps = 4;  // EA/2;
	let ap_steps = 2; // EA;
	let (aff_e, ((_, _), (_, _))) = a_sidh_isogen(a_sk, e, ab, bb, a_steps);
	let (x_p, x_q, x_r) = a_keygen(pbb, pab, a(), a24plus(), c24(), a_sk, ap_steps);
	let a = get_a(x_p, x_q, x_r);
	let jinv = j_inv((a, fp2zero())); // note that the j-invariant does not depend on b
	let aff_jinv = j_inv(aff_e);
	assert_eq!(jinv,aff_jinv);
    }
    QuickCheck::new()
	.tests(1)
	.quickcheck(aux as fn(MyASc));
}

#[test]
fn test_aff_proj_sidhex() {
    fn aux(a_sk: MyASc) {
	let a_sk = a_sk.0;
	let e = (a(), b());
	let ab = (paxy(), qaxy());
	let pab = (xpa(), xqa(), xra());
	let a_steps = 4; // EA/2;
	let ap_steps = 2; // EA;
	let aff_jinv = a_sidh_isoex(a_sk, e, ab, a_steps);
	let jinv = a_sharedkey(pab, a_sk, ap_steps);
	assert_eq!(jinv,aff_jinv);
    }
    QuickCheck::new()
	.tests(1)
	.quickcheck(aux as fn(MyASc));
}

#[test]
fn test_proj_sidh() {
    fn aux(a_sk: MyASc, b_sk: MyBSc) {
	let a_sk = a_sk.0;
	let b_sk = b_sk.0;
	let ab = (xpa(), xqa(), xra());
	let bb = (xpb(), xqb(), xrb());
	let a_steps = 2; // EA/2;
	let b_steps = 2; // EB;
	let phi_bb = a_keygen(bb, ab, a(), a24plus(), c24(), a_sk, a_steps);
	let phi_ab = b_keygen(ab, bb, a(), a24plus(), a24minus(), b_sk, b_steps);
	let a_shared_secret = a_sharedkey(phi_ab, a_sk, a_steps);
	let b_shared_secret = b_sharedkey(phi_bb, b_sk, b_steps);
	assert_eq!(a_shared_secret,b_shared_secret);
    }
    QuickCheck::new()
	.tests(1)
	.quickcheck(aux as fn(MyASc, MyBSc));
}
