// Copyright (c) Onyeka Obi
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

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

#[test]
fn test_evaluate() {
    // Create a polynomial 3x^3 + 2x^2 + x + 1
    let poly = Polynomial::<isize, U3>::from(GenericArray::from([1, 1, 2, 3]));

    // Check that the result is correct
    assert_eq!(poly.evaluate(2), 35);
}
