"""Exact checks for exponent choice and the seeded multiplicative budget."""
from fractions import Fraction as F


def main():
    delta = F(7,25)
    checked = 0
    for a in range(1,7):
        P = F(a,25)
        for b in range(a,26):
            p0 = F(b,25)
            for c in range(b,26):
                p1 = F(c,25)
                ratios = []
                for k in (1,2,4,12,24):
                    upper = min(F(1),p0*p1/delta * min(F(1),p0/delta)**(k-1))
                    ratios.append(upper/(P/delta)**k)
                assert all(x<=y for x,y in zip(ratios,ratios[1:]))
                checked += 1
    D = F('1.9704509e-12')
    end = D*F('1.0017')**390
    assert end < F('3.821716e-12') < F('3.922e-12')
    # A genuine separation of sufficient premises within the shrinking regime.
    P,p0,p1 = F(1,20),F(1,10),F(1,5)
    assert p0*p1 < P
    assert p0**24*p1 > P**24
    print(f'Passed {checked} exact relative-drift exponent comparisons.')
    print('Exact390-step budget: D*(1.0017)^390 < 3.821716e-12 < 3.922e-12.')
    print('First-moment sufficient premise can hold while the24th-power premise fails.')


if __name__ == '__main__':
    main()
