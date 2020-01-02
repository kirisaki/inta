// Copyright (c) 2013-2019 Masahide Kashiwagi
// Released under the MIT license
// https://github.com/mskashi/kv/blob/master/LICENSE.txt

extern crate libc;

use std::ptr;
use std::ops;
use libc::c_int;
use num_traits::float::Float;
use num_traits::identities::Zero;

const FE_TONEAREST: c_int = 0;
const FE_DOWNWARD:  c_int = 0x400;
const FE_UPWARD:    c_int = 0x800;

extern {
    fn fesetround(rdir: c_int) -> c_int;
}



#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Interval<F: Float> {
    pub inf: F,
    pub sup: F,
}

impl<F: Float> Interval<F> {
    pub fn new(x: F) -> Self {
        Self { inf: x, sup: x }
    }
    pub fn from(x: F) -> Self {
        Self { inf: x, sup: Float::infinity() }
    }
    pub fn to(self, y: F) -> Self {
        Self { inf: self.inf, sup: y }
    }
    pub fn sqrt(self) -> Self {
        if self.inf < Zero::zero() {
            panic!("sqrt doesn't take negative number");
        };
        let mut inf = Zero::zero();
        let p = &mut inf as *mut F;
        let mut sup = Zero::zero();
        let q = &mut sup as *mut F;
        unsafe {
            fesetround(FE_DOWNWARD);
            ptr::write_volatile(p, self.inf.sqrt());
            fesetround(FE_UPWARD);
            ptr::write_volatile(q, self.sup.sqrt());
            fesetround(FE_TONEAREST);
        }
        Self { inf, sup }
    }
}

impl<F> ops::Add for Interval<F>
where
    F: Float,
{
    type Output = Interval<F>;
    fn add(self, other: Self) -> Interval<F> {
        let mut inf = Zero::zero();
        let p = &mut inf as *mut F;
        let mut sup = Zero::zero();
        let q = &mut sup as *mut F;
        unsafe {
            fesetround(FE_DOWNWARD);
            ptr::write_volatile(p, self.inf + other.inf);
            fesetround(FE_UPWARD);
            ptr::write_volatile(q, self.sup + other.sup);
            fesetround(FE_TONEAREST);
        }
        Self { inf, sup }
    }
}

impl <F> ops::AddAssign for Interval<F>
where
    F: Float {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

impl<F> ops::Sub for Interval<F>
where
    F: Float,
{
    type Output = Interval<F>;
    fn sub(self, other: Self) -> Interval<F> {
        let mut inf = Zero::zero();
        let p = &mut inf as *mut F;
        let mut sup = Zero::zero();
        let q = &mut sup as *mut F;
        unsafe {
            fesetround(FE_DOWNWARD);
            ptr::write_volatile(p, self.inf - other.sup);
            fesetround(FE_UPWARD);
            ptr::write_volatile(q, self.sup - other.inf);
            fesetround(FE_TONEAREST);
        }
        Self { inf, sup }
    }
}

impl <F> ops::SubAssign for Interval<F>
where
    F: Float {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

impl<F> ops::Mul for Interval<F>
where
    F: Float,
{
    type Output = Interval<F>;
    fn mul(self, other: Self) -> Interval<F> {
        let mut inf = Zero::zero();
        let p = &mut inf as *mut F;
        let mut sup = Zero::zero();
        let q = &mut sup as *mut F;
        unsafe {
            if self.inf >= F::zero() {
                if other.inf >= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf * other.inf);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup * other.sup);
                } else if other.sup <= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.sup * other.inf);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup * other.inf);
                } else {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.sup * other.inf);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup * other.sup);
                }
            } else if self.sup <= F::zero() {
                if other.inf >= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf * other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup * other.inf);
                } else if other.sup <= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.sup * other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.inf * other.inf);
                } else {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf * other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.inf * other.inf);
                }
            } else {
                if other.inf >= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf * other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup * other.sup);
                } else if other.sup <= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.sup * other.inf);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.inf * other.inf);
                } else {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf * other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.inf * other.inf);
                }
            }
            fesetround(FE_TONEAREST);
        }
        Self { inf, sup }
    }
}

impl <F> ops::MulAssign for Interval<F>
where
    F: Float {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl<F> ops::Div for Interval<F>
where
    F: Float,
{
    type Output = Interval<F>;
    fn div(self, other: Self) -> Interval<F> {
        let mut inf = Zero::zero();
        let p = &mut inf as *mut F;
        let mut sup = Zero::zero();
        let q = &mut sup as *mut F;
        unsafe {
            if self.inf > F::zero() {
                if other.inf >= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf / other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup / other.inf);
                } else if other.sup <= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf / other.inf);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup / other.sup);
                } else {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf / other.inf);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup / other.inf);
                }
            } else if self.sup < F::zero() {
                if other.inf >= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.sup / other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.inf / other.inf);
                } else if other.sup <= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.sup / other.inf);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.inf / other.sup);
                } else {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.sup / other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.inf / other.sup);
                }
            } else {
                fesetround(FE_TONEAREST);
                panic!("divided zero");
            }
            fesetround(FE_TONEAREST);
        }
        Self { inf, sup }
    }
}

impl <F> ops::DivAssign for Interval<F>
where
    F: Float {
    fn div_assign(&mut self, other: Self) {
        *self = *self / other;
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn add_interval() {
        let a = Interval::from(-1.0).to(1.0);
        let b = Interval::from(-2.0).to(2.0);
        assert_eq!(a + b, Interval::from(-3.0).to(3.0));
    }
    #[test]
    fn sub_interval() {
        let a = Interval::from(-1.0).to(1.0);
        let b = Interval::from(-2.0).to(2.0);
        assert_eq!(a - b, Interval::from(-3.0).to(3.0));
    }
    #[test]
    fn mul_interval() {
        let a = Interval::from(-1.0).to(1.0);
        let b = Interval::from(-2.0).to(2.0);
        assert_eq!(a * b, b * a);
    }
}
