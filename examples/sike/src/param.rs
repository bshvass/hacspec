#![cfg(test)]
use crate::fp::*;
use crate::fp;
use crate::fp2::*;
use crate::fp2;
use crate::ec_isogeny::*;

pub const PAX: Fp2 = (XPA0, XPA1);
pub const PAY: Fp2 = (YPA0, YPA1);
pub const QAX: Fp2 = (XQA0, XQA1);
pub const QAY: Fp2 = (YQA0, YQA1);
pub const PBX: Fp2 = (XPB0, XPB1);
pub const PBY: Fp2 = (YPB0, YPB1);
pub const QBX: Fp2 = (XQB0, XQB1);
pub const QBY: Fp2 = (YQB0, YQB1);

pub const A: Fp2 = (fp::A, ZERO);
pub const B: Fp2 = (fp::B, ZERO);
pub const C: Fp2 = (fp::C, ZERO);

pub const PAXY: Point = (PAX, PAY);
pub const PAXZ: Point = (PAX, fp2::ONE());
pub const PBXY: Point = (PBX, PBY);
pub const PBXZ: Point = (PBX, fp2::ONE());
pub const QAXY: Point = (QAX, QAY);
pub const QAXZ: Point = (QAX, fp2::ONE());
pub const QBXY: Point = (QBX, QBY);
pub const QBXZ: Point = (QBX, fp2::ONE());
