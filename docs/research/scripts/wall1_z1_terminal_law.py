"""Exact inequalities for the two-window example and Haar budget comparisons."""

from fractions import Fraction as F


def verify_geometry():
    q = 3329
    a2 = F(1352**2, 3)
    v, x, y, c = 29, 28, F(111, 4), F(139, 5)
    w2 = 1 + c**2

    # The only old contenders for the first shortest line project to
    # zero or a signed coordinate axis of the rectangular binary quotient.
    assert y < x < v < 2 * y
    assert x**2 + y**2 > v**2
    assert y**2 + F(v, 2)**2 > v**2
    # Parent planes of projection rank one, index >= 2, and index one.
    assert (v * y)**2 > a2 and (2 * x * y)**2 > a2
    assert (x * y)**2 + F(v, 2)**2 * (x**2 + y**2) > a2
    # In the parent and first retained state every hit has two basis
    # vectors shorter than 33, by binary reduction and the minimum.
    assert 4 * a2 < 3 * y**2 * 33**2
    assert 33 < 100 < q
    assert x * y == 777 and 777**2 < a2
    assert 26 < y < c
    assert y**2 < w2 < x**2
    assert F('778.9034')**2 < x**2 * w2 < F('778.9035')**2 < a2
    assert (q * c)**2 > x**2 * w2

    # Direct checks of every fresh layer within the relevant length.
    for scale, cap in [(100, v), (c, x)]:
        for h in range(1, int(cap) + 1):
            centered = (h + q // 2) % q - q // 2
            assert h*h + (scale * centered)**2 == h*h * (1 + scale**2)


def verify_budgets():
    q, budget = 3329, F('7.1275e-11')
    e = F('9.971193576034e-63')  # rounded benchmark, Part 190
    lower, upper = F('2.00059e-58'), F('2.07179e-58')  # Part 192
    assert F('9.5612') < q**15 * e / budget < F('9.5614')
    # Check exponents with integer powers, avoiding logarithm roundoff.
    for h, thousandths in [(e, 14721), (lower, 13500), (upper, 13495)]:
        power = (budget / h)**1000
        assert q**thousandths < power < q**(thousandths + 1)
    assert 191834 < q**15 * lower / budget
    assert q**15 * upper / budget < 198663
    assert F('7.6330e-11') - F('5.055e-12') == budget


if __name__ == "__main__":
    verify_geometry()
    verify_budgets()
    print("Two-window inequalities and both Haar budget comparisons passed.")
