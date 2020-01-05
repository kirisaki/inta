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
    pub fn mid(self) -> F {
        let f_1 = F::one();
        let f_0_5 = f_1 / (f_1 + f_1);
   		  if self.inf.abs() > f_1 && self.sup.abs() > f_1 {
			      self.inf * f_0_5 + self.sup * f_0_5
		    } else {
			      (self.inf + self.sup) * f_0_5
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
    pub fn intersect(self, other: Self) -> Self {
		    let inf = if self.inf > other.inf{
            self.inf
        } else {
		        other.inf
        };
        let sup = if self.sup < other.sup {
            self.sup
        } else {
            other.sup
        };

        Self{ inf, sup }
    }
    pub fn contains(self, other: Self) -> bool{
        self.inf <= other.inf && other.sup <= self.sup
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
    fn sin_origin(self) -> Self {
        let mut r:Self = Self::new(F::zero());
        let mut y:Self = Self::new(F::one());
        let mut i:F = F::one();
        loop {
            y = y * self;
            y = y / Self::new(i);
            if y.norm() < F::epsilon() {
                r = r + y * Self::from(-F::one()).to(F::one());
                break;
            } else {
                if i % (F::one() + F::one()) != F::zero() {
                    if i % (F::one() + F::one() + F::one() + F::one()) == F::one() {
                        r = r + y;
                    } else {
                        r = r - y;
                    }
                }
            }
            i = i + F::one()
        }

        r
    }
    fn sin_point(self) -> Self {
		    let pi = Self::pi();
		    let mpi = pi.mid();
        let f_1 = F::one();
        let f_2 = f_1 + f_1;
        let f_3 = f_1 + f_2;
        let f_4 = f_2 + f_2;
        let f_0_25 = f_1 / f_4;
        let f_0_5 = f_1 / f_2;
        let f_0_75 = f_3 / f_4;

		    if self.inf >= mpi {
			      (self - pi * Self::new(f_2)).sin_point()
		    } else if self.sup <= -mpi * f_0_75 {
			      -Self::sin_origin(self + pi)
		    } else if self.sup <= -mpi * f_0_5 {
			      -Self::cos_origin(-pi * Self::new(f_0_5) - self)
		    } else if self.sup <= -mpi * f_0_25 {
			      -Self::cos_origin(self + pi * Self::new(f_0_25))
		    } else if self.sup <= F::zero() {
			      -Self::sin_origin(-self)
		    } else if self.sup <= mpi * f_0_25 {
			      Self::sin_origin(self)
		    } else if self.sup <= mpi * f_0_5 {
			      Self::cos_origin(pi * Self::new(f_0_5) - self)
		    } else if self.sup <= mpi * f_0_75 {
			      Self::cos_origin(self - pi * Self::new(f_0_5))
		    } else {
		        Self::sin_origin(pi - self)
        }
    }
    pub fn sin(self) -> Self {
        let f_1 = F::one();
        let f_2 = f_1 + f_1;
        let f_0_5 = f_1 / f_2;
        let f_1_5 = (f_1 + f_2) / f_2;
        let f_2_5 = (f_1 + f_2+ f_2) / f_2;

		    if self.inf.abs() == F::infinity() || self.sup.abs() == F::infinity() {
			      return Self{ inf: -f_1, sup: f_1 };
		    };

        let mut i = self;
        let pi = Self::pi();
        let pi2 = pi * Self::new(F::one() + F::one());

		    while i.inf <= -pi.sup || i.inf >= pi.inf {
			      let n = (i.inf / pi2.inf + f_0_5).floor();
			      i = i -  Self::new(n) * pi2;
		    };

		    if (Self::new(i.sup) - Self::new(i.inf)).inf >= pi2.sup {
			      return Interval::from(-f_1).to(f_1);
		    };

        let mut r = Self::new(i.inf).sin_point().hull(Self::new(i.sup).sin_point());
        if (pi * Self::new(f_0_5)).contains(i) || (pi * Self::new(f_2_5)).contains(i) {
            r = r.hull(Self::new(f_1));
        } else if (pi * Self::new(f_0_5)).contains(i) || (pi * Self::new(f_1_5)).contains(i) {
            r = r.hull(Self::new(-f_1));
        };

        r.intersect(Self{ inf: -f_1, sup: f_1 })
    }
    fn cos_origin(self) -> Self {
        let mut r:Self = Self::new(F::one());
        let mut y:Self = Self::new(F::one());
        let mut i:F = F::one();
        loop {
            y = y * self;
            y = y / Self::new(i);
            if y.norm() < F::epsilon() {
                r = r + y * Self::from(-F::one()).to(F::one());
                break;
            } else {
                if i % (F::one() + F::one()) == F::zero() {
                    if i % (F::one() + F::one() + F::one() + F::one()) == F::zero() {
                        r = r + y;
                    } else {
                        r = r - y;
                    }
                }
            }
            i = i + F::one()
        }

        r
    }
    fn cos_point(self) -> Self {
		    let pi = Self::pi();
		    let mpi = pi.mid();
        let f_1 = F::one();
        let f_2 = f_1 + f_1;
        let f_3 = f_1 + f_2;
        let f_4 = f_2 + f_2;
        let f_0_25 = f_1 / f_4;
        let f_0_5 = f_1 / f_2;
        let f_0_75 = f_3 / f_4;

		    if self.inf >= mpi {
			      (self - pi * Self::new(f_2)).cos_point()
		    } else if self.sup <= -mpi * f_0_75 {
			      -Self::cos_origin(self - pi)
		    } else if self.sup <= -mpi * f_0_5 {
			      -Self::sin_origin(-pi * Self::new(f_0_5) - self)
		    } else if self.sup <= -mpi * f_0_25 {
			      -Self::sin_origin(self + pi * Self::new(f_0_25))
		    } else if self.sup <= F::zero() {
			      -Self::cos_origin(-self)
		    } else if self.sup <= mpi * f_0_25 {
			      Self::cos_origin(self)
		    } else if self.sup <= mpi * f_0_5 {
			      Self::sin_origin(pi * Self::new(f_0_5) - self)
		    } else if self.sup <= mpi * f_0_75 {
			      Self::sin_origin(self - pi * Self::new(f_0_5))
		    } else {
		        Self::cos_origin(pi - self)
        }
    }
    pub fn cos(self) -> Self {
        let f_0 = F::zero();
        let f_1 = F::one();
        let f_2 = f_1 + f_1;
        let f_3 = f_2 + f_1;
        let f_0_5 = f_1 / f_2;

		    if self.inf.abs() == F::infinity() || self.sup.abs() == F::infinity() {
			      return Self{ inf: -f_1, sup: f_1 };
		    };

        let mut i = self;
        let pi = Self::pi();
        let pi2 = pi * Self::new(F::one() + F::one());

		    while i.inf <= -pi.sup || i.inf >= pi.inf {
			      let n = (i.inf / pi2.inf + f_0_5).floor();
			      i = i -  Self::new(n) * pi2;
		    };

		    if (Self::new(i.sup) - Self::new(i.inf)).inf >= pi2.sup {
			      return Interval::from(-f_1).to(f_1);
		    };

        let mut r = Self::new(i.inf).cos_point().hull(Self::new(i.sup).cos_point());
        if (Self::new(f_0)).contains(i) || (pi * Self::new(f_2)).contains(i) {
            r = r.hull(Self::new(f_1));
        } else if (-pi).contains(i) || pi.contains(i) || (pi * Self::new(f_3)).contains(i) {
            r = r.hull(Self::new(-f_1));
        };

        r.intersect(Self{ inf: -f_1, sup: f_1 })
    }
    fn tan_point(x: F) -> Self {
        Self::sin_point(Self::new(x)) / Self::cos_point(Self::new(x))
    }
    pub fn tan(self) -> Self {
		    if self.inf.abs() == F::infinity() || self.sup.abs() == F::infinity() {
			      return Self::new(-F::infinity()).hull(Self::new(F::infinity()));
		    };

        let mut i = self;
        let pi = Self::pi();
        let pih = pi / Self::new(F::one() + F::one());
		    while i.inf <= -pih.sup || i.inf >= pih.sup {
			      let n = ((i.inf / pi.inf) + (F::one() / (F::one() + F::one()))).floor();
			      i = i - Self::new(n) * pi;
		    }

		    if i.sup >= pih.sup {
			      Self::from(-F::infinity()).to(F::infinity())
		    } else {
            Self::from(Self::tan_point(i.inf).inf).to(Self::tan_point(i.sup).sup)
        }
    }
    fn atan_origin(self) -> Self {
        let mut r = Self::new(F::zero());
        let mut y = Self::new(F::one());
        let mut i = F::one();
        loop {
            y = y * self;
            let tmp = y * Self::from(-F::one()).to(F::one()) / Self::new(i);
            if tmp.norm() < F::epsilon() {
                r = r + tmp;
                break;
            } else {
                if i % (F::one() + F::one()) != F::zero() {
                    if i % (F::one() + F::one() + F::one() + F::one()) == F::one() {
                        r = r + y / Self::new(i)
                    } else {
                        r = r - y / Self::new(i)
                    }
                }
            }
            i = i + F::one();
        }

        r
    }
    pub fn pi() -> Self {
        let f_1 = Self::new(F::one());
        let f_2 = f_1 + f_1;
        let f_4 = f_2 + f_2;
        let f_5 = f_4 + f_1;
        let f_16 = f_4 * f_4;
        let f_239 = f_16 * f_16 - f_16 - f_1;

        f_16 * (f_1 / f_5).atan_origin() - f_4 * (f_1 / f_239).atan_origin()
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
    #[test]
    fn log_interval() {
        let expect = Interval::from(2.0.ln()).to(3.0.ln());
        let result = (Interval::from(2.0).to(3.0)).ln();
        assert!(result.contains(expect));
    }
    #[test]
    fn sin_interval() {
        let a = (Interval::from(0.0).to(3.14 / 4.0)).sin();
        let b = Interval { inf: -0.0, sup: 0.7068251811053664 };
        assert_eq!(a, b);
    }
    #[test]
    fn cos_interval() {
        let a = (Interval::from(3.14 / 4.0).to(3.14 / 2.0)).cos();
        let b = Interval { inf: 0.000796326710730088, sup: 0.7073882691672001 };
        assert_eq!(a, b);
    }
    #[test]
    fn cos_tan() {
        let a = (Interval::from(3.14 / 12.0).to(3.14 / 6.0)).tan();
        let b = Interval { inf: 0.26780694740780925, sup: 0.5769964003928736 };
        assert_eq!(a, b);
    }
}
