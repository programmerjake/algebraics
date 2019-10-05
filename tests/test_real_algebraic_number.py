# SPDX-License-Identifier: LGPL-2.1-or-later
# See Notices.txt for copyright information

from algebraics import RealAlgebraicNumber
import unittest


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

    # FIXME: add more tests


if __name__ == '__main__':
    unittest.main()
