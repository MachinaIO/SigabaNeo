"""Fully reduced basis certificate for independent uniform plain-LWE shapes."""
from bisect import bisect_left
from math import comb

import mpmath as mp

from wall1_prefix import cost, volume_log

Q = 3329
FAIL_LOG = 64 * mp.log(2)


def log_mgf(eta, tilt):
    return mp.log(sum(comb(2 * eta, eta + j) * mp.exp(tilt * j*j)
                      for j in range(-eta, eta+1)) / 4**eta)


def gap_rows(n, eta):
    # Each tilt gives a rigorous Chernoff bound. Choose the best of the grid.
    tilts = [(mp.mpf(j)/100, log_mgf(eta, mp.mpf(j)/100)) for j in range(1, 51)]
    for m in range(1, n+1):
        d = n+m+1
        radius = min(mp.exp((m*mp.log(Q)-volume_log(d)-FAIL_LOG)/d)-mp.sqrt(d)/2,
                     (1-mp.mpf('1e-50'))*Q/mp.sqrt(1+eta**2))
        if radius <= 0:
            continue
        squared = min(((d-1)*psi+FAIL_LOG)/tilt for tilt, psi in tilts)
        norm = mp.sqrt(1+min((d-1)*eta**2, mp.floor(squared)))
        if norm < radius:
            yield d, mp.log(radius/norm), radius, norm


def certificate(n, eta):
    rows = list(gap_rows(n, eta))
    ceiling = max(gap for _, gap, _, _ in rows)
    # Removing the beta cap lowers the recurrence, giving a necessary test.
    profile = [mp.mpf(0)]
    sums = [mp.mpf(0), mp.mpf(0)]
    while profile[-1] < ceiling:
        k = len(profile)
        value = min((h*cost(h)+sums[k]-sums[k-h+1])/(h-1)
                    for h in range(2, k+2))
        profile.append(value)
        sums.append(sums[-1]+value)
    candidates = []
    for d, gap, radius, norm in rows:
        k = bisect_left(profile, gap)-1
        beta = max(2, d-k)
        candidates.append((beta, d, radius, norm))
    beta, d, radius, norm = min(candidates)
    assert beta >= d-beta+1  # The winning unrestricted recurrence is admissible.
    return beta, d-n-1, d, radius, norm, mp.sqrt(mp.mpf(d)/beta)


def gsa_threshold(n, eta, projected):
    """Use the estimator's tau=sigma embedding and sample/dimension cap."""
    from lwemodel import fx, reduction

    sigma = mp.sqrt(mp.mpf(eta)/2)
    lq = mp.log(Q)
    a = (n+1)*lq-mp.log(sigma)
    for beta in range(40, 2*n+1):
        slope = mp.log(2)*reduction.log2_delta(beta)/fx.ONE
        # Margin as a function of d has derivative a/d²-slope-c/d.
        c = mp.mpf(0) if projected else mp.mpf('0.5')
        peak = 2*a/(c+mp.sqrt(c*c+4*a*slope))
        lower = max(n+2, beta)
        for d in sorted({max(lower, min(2*n, int(peak)+i)) for i in (0, 1)}):
            height = lq-a/d+(2*beta-d-1)*slope
            if height >= mp.log(sigma)+mp.log(beta if projected else d)/2:
                return beta, d, mp.sqrt(mp.mpf(d)/beta)


if __name__ == '__main__':
    for n, eta in [(512, 3), (768, 2), (1024, 2)]:
        print(n, *(mp.nstr(x, 12) for x in certificate(n, eta)))
        for projected in (True, False):
            print("GSA", projected, *(mp.nstr(x, 12) for x in gsa_threshold(n, eta, projected)))
