"""Screen deterministic raw reference balls under hypothetical early SVP caps.

The caps are assumptions for this diagnostic, not proved history events.
This computes no conditional distribution of a selected lattice.
"""
from mpmath import iv

iv.dps = 70
I = iv.mpf


def main():
    q = I(3329)
    volume = [I(1), I(2)]
    for n in range(2, 520):
        volume.append(2*iv.pi*volume[n-2]/n)
    for c, mean_ceiling, void_floor, normalized_floor in (
        ('1.1', '16.504778', '6.7930e-8', '2.4260e-7'),
        ('1.05', '26.304356', '3.7684e-12', '1.3458e-11'),
    ):
        log_d = 400*iv.ln(q)
        for _ in range(15):
            period = log_d-iv.ln(q)
            cap = I(505)/506*log_d-iv.ln(I(c))+iv.ln(volume[506])/506
            log_d = I([max(period.a, cap.a), max(period.b, cap.b)])
        # Precisely the existing raw-reference convention with an improved floor.
        radius_sq = I('1.21')*iv.exp(2*(log_d-iv.ln(volume[506]))/506)-2
        mean_upper = 2*volume[519]*(radius_sq+I(519)/4)**(I(519)/2)/q**400
        atom_upper = 2*volume[400]*(radius_sq+100)**200/q**400
        assert 0 < atom_upper < I('1e-298') < 1
        lower = iv.exp(-mean_upper/(1-atom_upper))
        assert mean_upper < I(mean_ceiling)
        assert lower > I(void_floor)
        assert lower/I('.280') > I(normalized_floor) > I('3.922e-12')
        print('Hypothetical all-step cap c=', c)
        print('Determinant-floor gain over q^385:', iv.exp(log_d-385*iv.ln(q)))
        print('Reference mean upper:', mean_upper)
        print('Independent-reference void lower:', lower)
        print('Normalized reference lower:', lower/I('.280'))
    print('Both raw-reference bootstraps remain insufficient; no BKZ failure lower bound.')


if __name__ == '__main__':
    main()
