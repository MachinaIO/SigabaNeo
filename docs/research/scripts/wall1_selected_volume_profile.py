"""All-stage integer-section volume floors with a bounded exception.

Reuses the established Hermite determinant recurrence and coordinate-minor
lemma. This does not estimate void probabilities on the complementary event.
"""
from math import comb

from wall1_hermite_budget import log_floors, iv


def certified_profile():
    floors = log_floors()
    logq, log2 = iv.ln(3329), iv.ln(2)
    rows = []
    for f in range(21, 407):
        numerator = 2*comb(505+f, f)
        k = next(k for k in range(min(f, 400)-1, -1, -1)
                 if numerator*10**30 < 3329**((400-k)*(f-k)))
        s = k+1
        # Every smaller candidate d is rejected by an outward interval.
        for d in range(401):
            h = max(0, s+d-400)
            residual = d*logq-floors[f]-h*log2/2
            if residual > 0:
                break
            assert residual < 0, 'Undecided interval; increase precision'
        else:
            raise AssertionError('No compatible quotient rank')
        rows.append((f, s, d, h))
    assert len(rows) == 386
    return rows


def main():
    rows = certified_profile()
    expected = {
        21: (21, 380, 1), 100: (100, 307, 7),
        200: (200, 230, 30), 300: (300, 168, 68),
        375: (373, 130, 103), 395: (388, 120, 108),
        400: (391, 118, 109), 404: (393, 116, 109),
        406: (394, 115, 109),
    }
    assert all(h >= 1 for _, _, _, h in rows)
    for f, s, d, h in rows:
        if f in expected:
            assert (s, d, h) == expected[f]
            print(f'f={f}: coordinate rank>={s}, quotient rank>={d}, section volume^2>=2^{h}')
    print('Passed all 386 exact rank-union comparisons and interval rank exclusions.')
    print('Joint exceptional probability < 386*10^-30 = 3.86e-28.')
    print('Only bounded indicators/potentials can be charged by this probability alone.')
    theta_screen()


def theta_screen():
    """Screen the two-coordinate-basis improvement, not the full void bound."""
    def theta(t):
        partial = 1+2*sum(iv.exp(-j*j*t) for j in range(1, 5))
        tail = 2*iv.exp(-25*t)/(1-iv.exp(-11*t))
        return iv.mpf([partial.a, (partial+tail).b])

    for radius, lower, upper in (
        ('30.5', '3.52366e-14', '3.52367e-14'),
        ('35.15', '2.31653e-19', '2.31654e-19'),
        ('40', '1.50539e-25', '1.50540e-25'),
    ):
        dual_parameter = 2*iv.pi**2*iv.mpf(radius)**2/505
        saving = 1-(theta(2*dual_parameter)/theta(dual_parameter))**109
        assert iv.mpf(lower) < saving < iv.mpf(upper)
        print(f'Theta-envelope relative saving at r=505, h=109, R={radius}:', saving)


if __name__ == '__main__':
    main()
