# SPDX-License-Identifier: LGPL-2.1-or-later
# See Notices.txt for copyright information

from algebraics import RealAlgebraicNumber
import unittest
import math


class TestRealAlgebraicNumber(unittest.TestCase):
    def test_construct(self):
        self.assertEqual(repr(RealAlgebraicNumber()),
                         "<RealAlgebraicNumber { minimal_polynomial: 0 + 1*X, "
                         "interval: DyadicFractionInterval { "
                         "lower_bound_numer: 0, upper_bound_numer: 0, "
                         "log2_denom: 0 } }>")
        self.assertEqual(repr(RealAlgebraicNumber(42)),
                         "<RealAlgebraicNumber { "
                         "minimal_polynomial: -42 + 1*X, "
                         "interval: DyadicFractionInterval { "
                         "lower_bound_numer: 42, upper_bound_numer: 42, "
                         "log2_denom: 0 } }>")
        self.assertEqual(repr(RealAlgebraicNumber(-5)),
                         "<RealAlgebraicNumber { "
                         "minimal_polynomial: 5 + 1*X, "
                         "interval: DyadicFractionInterval { "
                         "lower_bound_numer: -5, upper_bound_numer: -5, "
                         "log2_denom: 0 } }>")
        self.assertEqual(repr(RealAlgebraicNumber(RealAlgebraicNumber(-5))),
                         "<RealAlgebraicNumber { "
                         "minimal_polynomial: 5 + 1*X, "
                         "interval: DyadicFractionInterval { "
                         "lower_bound_numer: -5, upper_bound_numer: -5, "
                         "log2_denom: 0 } }>")

    def test_trunc(self):
        self.assertEqual(math.trunc(RealAlgebraicNumber(123)), 123)
        self.assertEqual(math.trunc(RealAlgebraicNumber(123) / 10), 12)
        self.assertEqual(math.trunc(RealAlgebraicNumber(128) / 10), 12)
        self.assertEqual(math.trunc(RealAlgebraicNumber(123)
                                    ** (RealAlgebraicNumber(1) / 2)), 11)
        self.assertEqual(math.trunc(RealAlgebraicNumber(-123)), -123)
        self.assertEqual(math.trunc(RealAlgebraicNumber(-123) / 10), -12)
        self.assertEqual(math.trunc(RealAlgebraicNumber(-128) / 10), -12)
        self.assertEqual(math.trunc(-(RealAlgebraicNumber(123)
                                      ** (RealAlgebraicNumber(1) / 2))), -11)

    def test_floor(self):
        self.assertEqual(math.floor(RealAlgebraicNumber(123)), 123)
        self.assertEqual(math.floor(RealAlgebraicNumber(123) / 10), 12)
        self.assertEqual(math.floor(RealAlgebraicNumber(128) / 10), 12)
        self.assertEqual(math.floor(RealAlgebraicNumber(123)
                                    ** (RealAlgebraicNumber(1) / 2)), 11)
        self.assertEqual(math.floor(RealAlgebraicNumber(-123)), -123)
        self.assertEqual(math.floor(RealAlgebraicNumber(-123) / 10), -13)
        self.assertEqual(math.floor(RealAlgebraicNumber(-128) / 10), -13)
        self.assertEqual(math.floor(-(RealAlgebraicNumber(123)
                                      ** (RealAlgebraicNumber(1) / 2))), -12)

    def test_ceil(self):
        self.assertEqual(math.ceil(RealAlgebraicNumber(123)), 123)
        self.assertEqual(math.ceil(RealAlgebraicNumber(123) / 10), 13)
        self.assertEqual(math.ceil(RealAlgebraicNumber(128) / 10), 13)
        self.assertEqual(math.ceil(RealAlgebraicNumber(123)
                                   ** (RealAlgebraicNumber(1) / 2)), 12)
        self.assertEqual(math.ceil(RealAlgebraicNumber(-123)), -123)
        self.assertEqual(math.ceil(RealAlgebraicNumber(-123) / 10), -12)
        self.assertEqual(math.ceil(RealAlgebraicNumber(-128) / 10), -12)
        self.assertEqual(math.ceil(-(RealAlgebraicNumber(123)
                                     ** (RealAlgebraicNumber(1) / 2))), -11)

    def test_to_integer(self):
        self.assertEqual(RealAlgebraicNumber(123).to_integer(), 123)
        self.assertEqual((RealAlgebraicNumber(123) / 10).to_integer(), None)
        self.assertEqual((RealAlgebraicNumber(128) / 10).to_integer(), None)
        self.assertEqual((RealAlgebraicNumber(123)
                          ** (RealAlgebraicNumber(1) / 2)).to_integer(), None)
        self.assertEqual(RealAlgebraicNumber(-123).to_integer(), -123)
        self.assertEqual((RealAlgebraicNumber(-123) / 10).to_integer(), None)
        self.assertEqual((RealAlgebraicNumber(-128) / 10).to_integer(), None)
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 2))
                          ).to_integer(), None)

    def test_to_rational(self):
        self.assertEqual(RealAlgebraicNumber(123).to_rational(), (123, 1))
        self.assertEqual((RealAlgebraicNumber(123) / 10).to_rational(),
                         (123, 10))
        self.assertEqual((RealAlgebraicNumber(128) / 10).to_rational(),
                         (64, 5))
        self.assertEqual((RealAlgebraicNumber(123)
                          ** (RealAlgebraicNumber(1) / 2)).to_rational(), None)
        self.assertEqual(RealAlgebraicNumber(-123).to_rational(), (-123, 1))
        self.assertEqual((RealAlgebraicNumber(-123) / 10).to_rational(),
                         (-123, 10))
        self.assertEqual((RealAlgebraicNumber(-128) / 10).to_rational(),
                         (-64, 5))
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 2))
                          ).to_rational(), None)

    def test_minimal_polynomial(self):
        self.assertEqual(RealAlgebraicNumber(123).minimal_polynomial,
                         [-123, 1])
        self.assertEqual((RealAlgebraicNumber(123) / 10).minimal_polynomial,
                         [-123, 10])
        self.assertEqual((RealAlgebraicNumber(128) / 10).minimal_polynomial,
                         [-64, 5])
        self.assertEqual((RealAlgebraicNumber(123)
                          ** (RealAlgebraicNumber(1) / 2)).minimal_polynomial,
                         [-123, 0, 1])
        self.assertEqual(RealAlgebraicNumber(-123).minimal_polynomial,
                         [123, 1])
        self.assertEqual((RealAlgebraicNumber(-123) / 10).minimal_polynomial,
                         [123, 10])
        self.assertEqual((RealAlgebraicNumber(-128) / 10).minimal_polynomial,
                         [64, 5])
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 2))
                          ).minimal_polynomial,
                         [-123, 0, 1])

    def test_degree(self):
        self.assertEqual(RealAlgebraicNumber(123).degree, 1)
        self.assertEqual((RealAlgebraicNumber(123) / 10).degree, 1)
        self.assertEqual((RealAlgebraicNumber(128) / 10).degree, 1)
        self.assertEqual((RealAlgebraicNumber(123)
                          ** (RealAlgebraicNumber(1) / 2)).degree, 2)
        self.assertEqual(RealAlgebraicNumber(-123).degree, 1)
        self.assertEqual((RealAlgebraicNumber(-123) / 10).degree, 1)
        self.assertEqual((RealAlgebraicNumber(-128) / 10).degree, 1)
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 2))
                          ).degree, 2)
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 3))
                          ).degree, 3)
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 4))
                          ).degree, 4)

    def test_is_integer(self):
        self.assertEqual(RealAlgebraicNumber(123).is_integer(), True)
        self.assertEqual((RealAlgebraicNumber(123) / 10).is_integer(), False)
        self.assertEqual((RealAlgebraicNumber(128) / 10).is_integer(), False)
        self.assertEqual((RealAlgebraicNumber(123)
                          ** (RealAlgebraicNumber(1) / 2)).is_integer(), False)
        self.assertEqual(RealAlgebraicNumber(-123).is_integer(), True)
        self.assertEqual((RealAlgebraicNumber(-123) / 10).is_integer(), False)
        self.assertEqual((RealAlgebraicNumber(-128) / 10).is_integer(), False)
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 2))
                          ).is_integer(), False)

    def test_is_rational(self):
        self.assertEqual(RealAlgebraicNumber(123).is_rational(), True)
        self.assertEqual((RealAlgebraicNumber(123) / 10).is_rational(), True)
        self.assertEqual((RealAlgebraicNumber(128) / 10).is_rational(), True)
        self.assertEqual((RealAlgebraicNumber(123)
                          ** (RealAlgebraicNumber(1) / 2)).is_rational(),
                         False)
        self.assertEqual(RealAlgebraicNumber(-123).is_rational(), True)
        self.assertEqual((RealAlgebraicNumber(-123) / 10).is_rational(), True)
        self.assertEqual((RealAlgebraicNumber(-128) / 10).is_rational(), True)
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 2))
                          ).is_rational(), False)

    def test_recip(self):
        self.assertEqual(RealAlgebraicNumber(123).recip().minimal_polynomial,
                         [-1, 123])
        self.assertEqual((RealAlgebraicNumber(123) / 10
                          ).recip().minimal_polynomial,
                         [-10, 123])
        self.assertEqual((RealAlgebraicNumber(128) / 10
                          ).recip().minimal_polynomial,
                         [-5, 64])
        self.assertEqual((-(RealAlgebraicNumber(123)
                            ** (RealAlgebraicNumber(1) / 2))
                          ).recip().minimal_polynomial,
                         [1, 0, -123])

    def test_recip_zero(self):
        with self.assertRaises(ZeroDivisionError):
            RealAlgebraicNumber(0).recip()

    def test_add(self):
        self.assertEqual(RealAlgebraicNumber(1) + 2, 3)
        self.assertEqual(1 + RealAlgebraicNumber(2), 3)
        self.assertEqual(RealAlgebraicNumber(1) + RealAlgebraicNumber(2), 3)

    def test_sub(self):
        self.assertEqual(RealAlgebraicNumber(1) - 2, -1)
        self.assertEqual(1 - RealAlgebraicNumber(2), -1)
        self.assertEqual(RealAlgebraicNumber(1) - RealAlgebraicNumber(2), -1)

    def test_mul(self):
        self.assertEqual(RealAlgebraicNumber(1) * 2, 2)
        self.assertEqual(1 * RealAlgebraicNumber(2), 2)
        self.assertEqual(RealAlgebraicNumber(1) * RealAlgebraicNumber(2), 2)

    def test_div(self):
        self.assertEqual(RealAlgebraicNumber(1) / 2,
                         RealAlgebraicNumber(1) / 2)
        self.assertEqual(1 / RealAlgebraicNumber(2),
                         RealAlgebraicNumber(1) / 2)
        self.assertEqual(RealAlgebraicNumber(1) / RealAlgebraicNumber(2),
                         RealAlgebraicNumber(1) / 2)

    def test_div_zero(self):
        with self.assertRaises(ZeroDivisionError):
            RealAlgebraicNumber(1) / 0
        with self.assertRaises(ZeroDivisionError):
            RealAlgebraicNumber(-1) / 0
        with self.assertRaises(ZeroDivisionError):
            RealAlgebraicNumber(0) / 0

    def test_pow(self):
        self.assertEqual(RealAlgebraicNumber(1) ** 2, 1)
        self.assertEqual(1 ** RealAlgebraicNumber(2), 1)
        self.assertEqual(RealAlgebraicNumber(1) ** RealAlgebraicNumber(2), 1)

    def test_neg(self):
        self.assertEqual(-RealAlgebraicNumber(1), -1)
        self.assertEqual(-RealAlgebraicNumber(-2), 2)

    def test_abs(self):
        self.assertEqual(abs(RealAlgebraicNumber(1)), 1)
        self.assertEqual(abs(RealAlgebraicNumber(-2)), 2)

    def test_floor_ceil_log2(self):
        with self.assertRaises(ValueError):
            RealAlgebraicNumber(0).floor_log2()
        with self.assertRaises(ValueError):
            RealAlgebraicNumber(0).ceil_log2()
        with self.assertRaises(ValueError):
            RealAlgebraicNumber(-1).floor_log2()
        with self.assertRaises(ValueError):
            RealAlgebraicNumber(-1).ceil_log2()
        self.assertEqual(RealAlgebraicNumber(1).floor_log2(), 0)
        self.assertEqual(RealAlgebraicNumber(1).ceil_log2(), 0)
        self.assertEqual(RealAlgebraicNumber(2).floor_log2(), 1)
        self.assertEqual(RealAlgebraicNumber(2).ceil_log2(), 1)
        self.assertEqual(RealAlgebraicNumber(3).floor_log2(), 1)
        self.assertEqual(RealAlgebraicNumber(3).ceil_log2(), 2)
        self.assertEqual(RealAlgebraicNumber(4).floor_log2(), 2)
        self.assertEqual(RealAlgebraicNumber(4).ceil_log2(), 2)
        self.assertEqual((RealAlgebraicNumber(1) / 4).floor_log2(), -2)
        self.assertEqual((RealAlgebraicNumber(1) / 4).ceil_log2(), -2)
        self.assertEqual((RealAlgebraicNumber(1) / 3).floor_log2(), -2)
        self.assertEqual((RealAlgebraicNumber(1) / 3).ceil_log2(), -1)


if __name__ == '__main__':
    unittest.main()
