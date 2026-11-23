"""Check finite DGS bounds and the Part 236 probability. No CVP instances are run."""
from fractions import Fraction
from math import log2

from mpmath import iv

from wall1_selfdual_envelope import ball_gain, split_bounds


def main():
    d, rows, tail, q = 638, 127, 511, 3329
    levels, mean, samples = 36, 2**753, 2**754
    assert mean // (2**d * 8**levels) == 128
    iv.dps = 50
    beta = iv.pi**2 * 2**levels / (647*q**2 * iv.ln(1298) * iv.ln(2))
    assert beta > 16
    assert iv.exp(iv.mpf(2*d)/(2**16-1)) < iv.mpf(16)/15

    # Part 140, Lemma 4.3b, with K >= 2000, rounding bases upward.
    g = 8 * (Fraction(1, 4)**1999 + Fraction(3, 4)**3999)
    assert levels * mean * g < Fraction(1, 2**830)
    assert Fraction(3, 4)**2000 < Fraction(1, 2**800)
    assert iv.exp(-120) < iv.mpf(2)**-172
    assert sum(Fraction(1, 2**b) for b in (830, 800, 172, 169)) < Fraction(1, 2**168)

    sampler = 8192*d + 32*rows*tail + 64*d + 512
    per_call = (2**42 + samples*sampler + 2*samples*(64*d+128)
                + levels*(8*2**d+128) + 2**21)
    total = 4*per_call + 2**24
    space = 4*(d+10)*samples + 2**640 + 2**30
    # Integer comparisons certify the displayed exponents rounded up to .001.
    assert per_call**1000 < 2**776825 and total**1000 < 2**778825
    assert space < 2**766
    _, _, cutoff = ball_gain(d, rows, 1)
    geometric, groups, held, _ = split_bounds(rows, 1, cutoff)
    assert (cutoff, groups, held) == (954, 4, 4)
    recovery = geometric - Fraction(groups, 2**168)
    assert recovery > Fraction(6431620941663886, 10**16)
    print(f"final inverse temperature in bits {beta}")
    print(f"log2 work per call {log2(per_call):.9f}, four calls + validation {log2(total):.9f}")
    print(f"log2 space in words {log2(space):.9f}")
    print("per-call failure < 2^-168, recovery > 0.6431620941663886")


if __name__ == "__main__":
    main()
