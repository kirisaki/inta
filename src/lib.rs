// Copyright (c) 2013-2019 Masahide Kashiwagi
// Released under the MIT license
// https://github.com/mskashi/kv/blob/master/LICENSE.txt

extern crate libc;

use std::ptr;
use std::convert::TryInto;
use std::ops;
use std::fmt::Debug;
use std::cmp::Ordering;
use libc::{c_int, c_double, c_float};
use num_traits::float::Float;
use num_traits::identities::Zero;

const FE_TONEAREST: c_int = 0;
const FE_DOWNWARD:  c_int = 0x400;
const FE_UPWARD:    c_int = 0x800;

extern "C" {
    fn fesetround(rdir: c_int) -> c_int;
    fn frexp(x: c_double, exp: *mut c_int) -> c_double;
    fn frexpf(x: c_float, exp: *mut c_int) -> c_float;
}

#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Interval<F: Float + FloatExp + Debug> {
    pub inf: F,
    pub sup: F,
}

impl<F: Float + FloatExp + Debug> Interval<F> {
    pub fn new(x: F) -> Self {
        Self { inf: x, sup: x }
    }
    pub fn from(x: F) -> Self {
        Self { inf: x, sup: Float::infinity() }
    }
    pub fn to(self, y: F) -> Self {
        Self { inf: self.inf, sup: y }
    }
    pub fn norm(self) -> F {
        if self.inf >= F::zero() {
            self.sup
        } else if self.sup <= F::zero() {
            -self.inf
        } else if self.sup > -self.inf {
            self.sup
        } else {
            -self.inf
        }
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
    pub fn hull(self, other: Self) -> Self {
        let inf = if self.inf > other.inf { other.inf } else { self.inf };
        let sup = if self.sup < other.sup { other.sup } else { self.sup };
        Self { inf, sup }
    }
    fn exp_point(x: F) -> Self {
        if x == F::infinity() {
            return Self { inf: F::max_value(), sup: F::infinity() };
        } else if x == - F::infinity() {
            return Self { inf: F::zero(), sup: F::min_positive_value() };
        };

        let mut x_i;
        let mut x_f;
        if x.is_sign_positive() {
            x_i = x.floor();
            x_f = x - x_i;
            if x_f >= F::one() / (F::one() + F::one()) {
                x_f = x_f - F::one();
                x_i = x_i + F::one();
            }
        } else {
            x_i = -((-x).floor());
            x_f = x - x_i;
            if x_f <= - F::one() / (F::one() + F::one()) {
                x_f = x_f + F::one();
                x_i = x_i - F::one();
            }
        }

        let mut r = Self::new(F::one());
        let mut y = F::one();
        let mut i = F::one();
        let remainder = Interval {
            inf: F::one()/(F::exp(F::one()).sqrt()),
            sup: F::exp(F::one()).sqrt(),
        };
        loop {
            y = y * x_f;
            y = y / i;
            if y * remainder.sup < F::epsilon(){
                r = r + Self::new(y) * remainder;
                break;
            } else {
                r = r + Self::new(y);
            };
            i = i + F::one();
        };

        if x_i.is_sign_positive() {
            r = r * Self::new(x_i.exp());
        } else {
            r = r / Self::new((-x_i).exp());
        }

        r
    }
    pub fn exp(self) -> Self {
        Self {
            inf: Self::exp_point(self.inf).inf,
            sup: Self::exp_point(self.sup).sup,
        }
    }
    fn ln_point(x: F, round: Round) -> F {
        if x == F::infinity() {
            return match round {
                Round::Upward => F::infinity(),
                Round::Downward => F::max_value(),
            };
        } else if x == F::zero() {
            return match round {
                Round::Upward => -F::max_value(),
                Round::Downward => -F::infinity(),
            };
        };

        let one = F::one();
        let two = F::one() + F::one();
        let four = two + two;
        let sqrt2 = Interval::new(two).sqrt();
        let (mut x_f, mut x_i) = x.frexp();
        while x_f > four * two.sqrt() - four {
            x_f = x_f * (one / two);
            x_i = x_i + one;
        };
        while x_f > four - two * two.sqrt() {
            x_f = match round {
                Round::Upward => (Interval::new(x_f) / sqrt2).sup,
                Round::Downward => (Interval::new(x_f) / sqrt2).inf,
            };
            x_i = x_i + one / two
        };
        while x_f < two - two.sqrt() {
            x_f = x_f * two;
            x_i = x_i - one;
        };
        while x_f < two * two.sqrt() - two {
            x_f = match round {
                Round::Upward => (Interval::new(x_f) * sqrt2).sup,
                Round::Downward => (Interval::new(x_f) * sqrt2).inf,
            };
            x_i = x_i - one / two;
        };
        let x_fm1 = Interval::new(x_f - one);
        let cinv = Interval::new(one) / Interval::new(x_f).hull(Interval::new(one));
        let mut r = Interval::new(F::zero());
        let mut xn = Interval::new(-one);
        let mut xn2 = Interval::new(-one);
        let mut i = one;
        loop {
            xn = - xn * x_fm1;
            xn2 = - xn2 * cinv * x_fm1;
            let tmp = xn2 / Interval::new(i);
            if tmp.norm() < F::epsilon() {
                r = r + tmp;
                break;
            } else {
                r = r + xn / Interval::new(i);
            };
            i = i + one;
        };

        r = r + Interval::new(F::ln(two) * x_i);

        match round {
            Round::Upward => r.sup,
            Round::Downward => r.inf,
        }
    }
    pub fn ln(self) -> Self {
        if self.inf < F::zero() {
            panic!("ln doesn't take negative value");
        };
        Interval::from(
            Self::ln_point(self.inf, Round::Downward),
        ).to(
            Self::ln_point(self.sup, Round::Upward),
        )
    }
}

enum Round {
    Upward,
    Downward,
}

impl<F> PartialOrd for Interval<F>
where
    F: Float + FloatExp + Debug,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering>{
        self.sup.partial_cmp(&other.inf)
    }
}

impl<F> ops::Add for Interval<F>
where
    F: Float + FloatExp + Debug,
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
    F: Float + FloatExp + Debug {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

impl <F> ops::Neg for Interval<F>
where
    F: Float + FloatExp + Debug {
    type Output = Self;
    fn neg(self) -> Self {
        Interval::new(-F::one()) * self
    }
}

impl<F> ops::Sub for Interval<F>
where
    F: Float + FloatExp + Debug + Debug,
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
    F: Float + FloatExp + Debug {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

impl<F> ops::Mul for Interval<F>
where
    F: Float + FloatExp + Debug,
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
    F: Float + FloatExp + Debug {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl<F> ops::Div for Interval<F>
where
    F: Float + FloatExp + Debug,
{
    type Output = Interval<F>;
    fn div(self, other: Self) -> Interval<F> {
        let mut inf = Zero::zero();
        let p = &mut inf as *mut F;
        let mut sup = Zero::zero();
        let q = &mut sup as *mut F;
        unsafe {
            if other.inf > F::zero() {
                if self.inf >= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.inf / other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.sup / other.inf);
                } else if self.sup <= F::zero() {
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
            } else if other.sup < F::zero() {
                if self.inf >= F::zero() {
                    fesetround(FE_DOWNWARD);
                    ptr::write_volatile(p, self.sup / other.sup);
                    fesetround(FE_UPWARD);
                    ptr::write_volatile(q, self.inf / other.inf);
                } else if self.sup <= F::zero() {
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
    F: Float + FloatExp + Debug {
    fn div_assign(&mut self, other: Self) {
        *self = *self / other;
    }
}

pub trait FloatExp: Sized {
    fn frexp(self) -> (Self, Self);
}
impl FloatExp for f64 {
    fn frexp(self) -> (Self, Self) {
        let mut exp: c_int = 0;
        let res = unsafe { frexp(self, &mut exp) };
        (res, From::from(exp))
    }
}
impl FloatExp for f32 {
    fn frexp(self) -> (Self, Self) {
        let mut exp: c_int = 0;
        let res = unsafe { frexpf(self, &mut exp) };
        let exp_: i16 = exp.try_into().unwrap();
        (res, From::from(exp_))
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
    #[test]
    fn div_interval() {
        let a = Interval::from(2.0).to(4.0);
        let b = Interval::from(1.0).to(2.0);
        let c = Interval::from(1.0).to(4.0);
        assert_eq!(a / b, c);
    }
    #[test]
    fn hull_interval() {
        let a = Interval::from(-2.0).to(1.0);
        let b = Interval::from(-1.0).to(2.0);
        let c = Interval::from(-2.0).to(2.0);
        assert_eq!(a.hull(b), c);
    }
    #[test]
    fn exp_interval() {
        let expect = Interval::from((-1.0).exp()).to(1.0.exp());
        let result = (Interval::from(-1.0).to(1.0)).exp();
        assert_eq!(expect, result);
    }
    /*
    #[test]
    fn log_interval() {
        let expect = Interval::from(2.0.ln()).to(3.0.ln());
        let result = (Interval::from(2.0).to(3.0)).ln();
        assert_eq!(expect, result);
    }
    */
}
