// Copyright (c) Onyeka Obi
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use {
    core::ops::{Add, Div, Mul, Neg, Sub},
    derive_more::From,
    generic_array::{
        typenum::{
            operator_aliases::{Add1, Maximum},
            Diff, Max, Sum, B1,
        },
        ArrayLength, GenericArray,
    },
};

pub trait Field
where
    Self: Copy
        + Add<Self, Output = Self>
        + Mul<Self, Output = Self>
        + Neg<Output = Self>
        + Sub<Self, Output = Self>
        + Div<Self, Output = Self>,
{
    const ONE: Self;
    const ZERO: Self;
    fn equals(&self, lhs: Self) -> bool;
}

macro_rules! impl_field {
    ($type:ty) => {
        impl Field for $type {
            const ONE: $type = 1;
            const ZERO: $type = 0;
            fn equals(&self, lhs: $type) -> bool {
                *self == lhs
            }
        }
    };
    ($($type:ty),+) => {
        $(impl_field!($type);)+
    }
}

impl_field!(isize, i8, i16, i32, i64);

#[derive(Clone, Debug, Default, From, PartialEq)]
pub struct Polynomial<F: Field, N: ArrayLength<F> + Add<B1>>(GenericArray<F, Add1<N>>)
where
    Add1<N>: ArrayLength<F>;

impl<F: Field, N: ArrayLength<F> + Add<B1>> Polynomial<F, N>
where
    Add1<N>: ArrayLength<F>,
{
    pub fn deg(&self) -> usize {
        self.0
            .iter()
            .enumerate()
            .rev()
            .find(|(_, a)| !a.equals(F::ZERO))
            .map(|(idx, _)| idx)
            .unwrap_or(0)
    }

    pub fn leading_coefficient(&self) -> F {
        *self
            .0
            .iter()
            .enumerate()
            .find(|(index, _)| *index == self.deg())
            .map(|(_, value)| value)
            .unwrap_or(&F::ZERO)
    }
}

impl<F: Field, N: ArrayLength<F> + Add<B1>> Neg for Polynomial<F, N>
where
    Add1<N>: ArrayLength<F>,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        GenericArray::from(self.0.iter().map(|a| -*a).collect()).into()
    }
}

impl<F: Field, N: ArrayLength<F> + Add<B1> + Max<M>, M: ArrayLength<F> + Add<B1>>
    Add<Polynomial<F, M>> for Polynomial<F, N>
where
    Add1<N>: ArrayLength<F>,
    Add1<M>: ArrayLength<F>,
    Maximum<N, M>: ArrayLength<F> + Add<B1>,
    Add1<Maximum<N, M>>: ArrayLength<F>,
{
    type Output = Polynomial<F, Maximum<N, M>>;

    fn add(self, rhs: Polynomial<F, M>) -> Self::Output {
        GenericArray::from(
            (0..=usize::max(N::USIZE, M::USIZE))
                .map(|i| *self.0.get(i).unwrap_or(&F::ZERO) + *rhs.0.get(i).unwrap_or(&F::ZERO))
                .collect(),
        )
        .into()
    }
}

impl<F: Field, N: ArrayLength<F> + Add<B1> + Max<M>, M: ArrayLength<F> + Add<B1>>
    Sub<Polynomial<F, M>> for Polynomial<F, N>
where
    Add1<N>: ArrayLength<F>,
    Add1<M>: ArrayLength<F>,
    Maximum<N, M>: ArrayLength<F> + Add<B1>,
    Add1<Maximum<N, M>>: ArrayLength<F>,
{
    type Output = Polynomial<F, Maximum<N, M>>;

    fn sub(self, rhs: Polynomial<F, M>) -> Self::Output {
        GenericArray::from(
            (0..=usize::max(N::USIZE, M::USIZE))
                .map(|i| *self.0.get(i).unwrap_or(&F::ZERO) - *rhs.0.get(i).unwrap_or(&F::ZERO))
                .collect(),
        )
        .into()
    }
}

impl<F: Field, N: ArrayLength<F> + Add<M> + Add<B1>, M: ArrayLength<F> + Add<B1>>
    Mul<Polynomial<F, M>> for Polynomial<F, N>
where
    Add1<N>: ArrayLength<F>,
    Add1<M>: ArrayLength<F>,
    Sum<N, M>: ArrayLength<F> + Add<B1>,
    Add1<Sum<N, M>>: ArrayLength<F>,
{
    type Output = Polynomial<F, Sum<N, M>>;

    fn mul(self, rhs: Polynomial<F, M>) -> Self::Output {
        use std::iter::repeat;
        self.0
            .iter()
            .enumerate()
            .flat_map(|(i, p)| rhs.0.iter().enumerate().map(move |(j, q)| (i + j, *p * *q)))
            .fold(
                GenericArray::from(repeat(F::ZERO).take(N::USIZE + M::USIZE + 1).collect()),
                |acc, (k, c)| {
                    GenericArray::from(
                        acc.iter()
                            .enumerate()
                            .map(|(i, &v)| if i == k { v + c } else { v })
                            .collect(),
                    )
                },
            )
            .into()
    }
}

impl<
        F: Field + PartialEq,
        N: ArrayLength<F> + Add<B1> + Sub<M> + Max<Sum<Diff<N, M>, M>, Output = N>,
        M: ArrayLength<F> + Add<B1>,
    > Div<Polynomial<F, M>> for Polynomial<F, N>
where
    Add1<N>: ArrayLength<F>,
    Add1<M>: ArrayLength<F>,
    Diff<N, M>: ArrayLength<F> + Add<B1> + Add<M> + Max<Output = Diff<N, M>> + Add<Diff<N, M>>,
    Add1<Diff<N, M>>: ArrayLength<F>,
    Sum<Diff<N, M>, M>: ArrayLength<F> + Add<B1>,
    Add1<Sum<Diff<N, M>, M>>: ArrayLength<F>,
    Maximum<N, Sum<Diff<N, M>, M>>: ArrayLength<F> + Add<B1>,
    Add1<Maximum<N, Sum<Diff<N, M>, M>>>: ArrayLength<F>,
{
    type Output = Result<Polynomial<F, Diff<N, M>>, ()>;

    fn div(self, rhs: Polynomial<F, M>) -> Self::Output {
        let (self_degree, rhs_degree) = (self.deg(), rhs.deg());
        match () {
            _ if self_degree < rhs_degree => {
                Ok(GenericArray::from((0..=N::USIZE - M::USIZE).map(|_| F::ZERO).collect()).into())
            }
            _ if self_degree == 0 && *rhs.0.first().unwrap_or(&F::ZERO) == F::ZERO => Err(()),
            _ if self_degree == 0 => Ok(Polynomial::from(GenericArray::from(
                (0..=N::USIZE - M::USIZE)
                    .map(|index| {
                        if index == 0 {
                            *self.0.first().unwrap_or(&F::ZERO) / *rhs.0.first().unwrap_or(&F::ZERO)
                        } else {
                            F::ZERO
                        }
                    })
                    .collect(),
            ))),
            _ => {
                let first_quotient = Polynomial::<F, Diff<N, M>>::from(GenericArray::from(
                    (0..=N::USIZE - M::USIZE)
                        .map(|index| {
                            if index == self.deg() - rhs.deg() {
                                self.leading_coefficient() / rhs.leading_coefficient()
                            } else {
                                F::ZERO
                            }
                        })
                        .collect(),
                ));
                let remainder = self - first_quotient.clone() * rhs.clone();
                (remainder / rhs).map(|second_quotient| first_quotient + second_quotient)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::Polynomial,
        generic_array::{
            typenum::consts::{U0, U1, U2, U3, U4},
            GenericArray,
        },
    };

    #[test]
    fn test_add() {
        // Test adding two polynomials with isize coefficients for N = 2
        let poly1 = Polynomial::<isize, U2>::from(GenericArray::from([1, 2, 3]));
        let poly2 = Polynomial::<isize, U2>::from(GenericArray::from([4, 5, 6]));
        let expected_result = Polynomial::<isize, U2>::from(GenericArray::from([5, 7, 9]));
        assert_eq!(poly1 + poly2, expected_result);

        // Test adding two polynomials with isize coefficients for N = 0
        let poly1 = Polynomial::<isize, U0>::from(GenericArray::from([1]));
        let poly2 = Polynomial::<isize, U0>::from(GenericArray::from([2]));
        let expected_result = Polynomial::<isize, U0>::from(GenericArray::from([3]));
        assert_eq!(poly1 + poly2, expected_result);

        // Test adding two polynomials with isize coefficients for N = 3
        let poly1 = Polynomial::<isize, U3>::from(GenericArray::from([1, 2, 3, 4]));
        let poly2 = Polynomial::<isize, U3>::from(GenericArray::from([5, 6, 7, 8]));
        let expected_result = Polynomial::<isize, U3>::from(GenericArray::from([6, 8, 10, 12]));
        assert_eq!(poly1 + poly2, expected_result);

        // Test adding two polynomials with isize coefficients for N = 3 and N = 4, respectively
        let poly1 = Polynomial::<isize, U3>::from(GenericArray::from([1, 2, 3, 4]));
        let poly2 = Polynomial::<isize, U4>::from(GenericArray::from([5, 6, 7, 8, 6]));
        let expected_result = Polynomial::<isize, U4>::from(GenericArray::from([6, 8, 10, 12, 6]));
        assert_eq!(poly1 + poly2, expected_result);
    }

    #[test]
    fn test_sub() {
        // Test subtracting two polynomials with isize coefficients for N = 2
        let poly1 = Polynomial::<isize, U2>::from(GenericArray::from([1, 2, 3]));
        let poly2 = Polynomial::<isize, U2>::from(GenericArray::from([4, 5, 6]));
        let expected_result = Polynomial::<isize, U2>::from(GenericArray::from([-3, -3, -3]));
        assert_eq!(poly1 - poly2, expected_result);

        // Test subtracting two polynomials with isize coefficients for N = 0
        let poly1 = Polynomial::<isize, U0>::from(GenericArray::from([1]));
        let poly2 = Polynomial::<isize, U0>::from(GenericArray::from([2]));
        let expected_result = Polynomial::<isize, U0>::from(GenericArray::from([-1]));
        assert_eq!(poly1 - poly2, expected_result);

        // Test subtracting two polynomials with isize coefficients for N = 3
        let poly1 = Polynomial::<isize, U3>::from(GenericArray::from([1, 2, 3, 4]));
        let poly2 = Polynomial::<isize, U3>::from(GenericArray::from([5, 6, 7, 8]));
        let expected_result = Polynomial::<isize, U3>::from(GenericArray::from([-4, -4, -4, -4]));
        assert_eq!(poly1 - poly2, expected_result);

        // Test subtracting two polynomials with isize coefficients for N = 3 and N = 2, respectively
        let poly1 = Polynomial::<isize, U3>::from(GenericArray::from([1, 2, 3, 4]));
        let poly2 = Polynomial::<isize, U2>::from(GenericArray::from([5, 6, 7]));
        let expected_result = Polynomial::<isize, U3>::from(GenericArray::from([-4, -4, -4, 4]));
        assert_eq!(poly1 - poly2, expected_result);
    }

    #[test]
    fn test_neg() {
        let poly = Polynomial::<isize, U3>::from(GenericArray::from([1, 2, 3, 4]));
        let expected_result = Polynomial::<isize, U3>::from(GenericArray::from([-1, -2, -3, -4]));
        assert_eq!(-poly, expected_result);
    }

    #[test]
    fn test_mul() {
        let p1 = Polynomial::<isize, U3>::from(GenericArray::from([2, 3, 4, 5]));
        let p2 = Polynomial::<isize, U2>::from(GenericArray::from([7, 6, 5]));
        let expected = Polynomial::from(GenericArray::from([14, 33, 56, 74, 50, 25]));
        assert_eq!(p1 * p2, expected);

        let p1 = Polynomial::<isize, U2>::from(GenericArray::from([1, 2, 3]));
        let p2 = Polynomial::<isize, U2>::from(GenericArray::from([4, 5, 6]));
        let expected = Polynomial::from(GenericArray::from([4, 13, 28, 27, 18]));
        assert_eq!(p1 * p2, expected);

        let p1 = Polynomial::<isize, U0>::from(GenericArray::from([3]));
        let p2 = Polynomial::<isize, U1>::from(GenericArray::from([3, 1]));
        let expected = Polynomial::from(GenericArray::from([9, 3]));
        assert_eq!(p1 * p2, expected);

        let p1 = Polynomial::<isize, U2>::from(GenericArray::from([1, 2, 2]));
        let p2 = Polynomial::<isize, U1>::from(GenericArray::from([-1, 1]));
        let expected = Polynomial::from(GenericArray::from([-1, -1, 0, 2]));
        assert_eq!(p1 * p2, expected);
    }

    #[test]
    fn test_div() {
        let p1 = Polynomial::<isize, U3>::from(GenericArray::from([-1, -1, 0, 2]));
        let p2 = Polynomial::<isize, U1>::from(GenericArray::from([-1, 1]));
        let expected = Polynomial::from(GenericArray::from([1, 2, 2]));
        assert_eq!((p1 / p2).unwrap(), expected);

        let p1 = Polynomial::<isize, U4>::from(GenericArray::from([4, 13, 28, 27, 18]));
        let p2 = Polynomial::<isize, U2>::from(GenericArray::from([4, 5, 6]));
        let expected = Polynomial::from(GenericArray::from([1, 2, 3]));
        assert_eq!((p1 / p2).unwrap(), expected);
    }
}
