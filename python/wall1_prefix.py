"""Reproduce the Haar terminal-profile table with mpmath."""
from functools import cache

import mpmath as mp

mp.mp.dps = 70


@cache
def volume_log(d):
    return d * mp.log(mp.pi) / 2 - mp.loggamma(1 + mp.mpf(d) / 2)


@cache
def zeta_log(d):
    return mp.log(mp.zeta(d)) if d > 1 else mp.mpf(0)


@cache
def count_log(n, j):
    return mp.log(mp.binomial(n, j) / n) + sum(
        volume_log(n+1-i) - volume_log(i) + zeta_log(i) - zeta_log(n+1-i)
        for i in range(1, j+1)
    )


@cache
def cost(d):
    # Exact Hermite constants in dimensions 2 through 8, then Blichfeldt.
    powers = {2: mp.mpf(4)/3, 3: 2, 4: 4, 5: 8, 6: mp.mpf(64)/3, 7: 64, 8: 256}
    if d in powers:
        return mp.log(powers[d]) / (2*d)
    return mp.log(2/mp.pi)/2 + mp.loggamma(2 + mp.mpf(d)/2)/d


def envelope(n, beta):
    u = [mp.mpf(0)] * (n+1)
    for j in range(n-1, 0, -1):
        u[j-1] = max((d*u[j] - u[j+d-1] - d*cost(d))/(d-1)
                     for d in range(2, min(beta, n-j+1)+1))
    return [x - (n-i)*u[0]/n for i, x in enumerate(u)]


def row(n, beta):
    k = n-beta
    log_x = envelope(n, beta)[k]
    eps = mp.mpf('0.01')
    if k:
        first = (mp.log(eps)-count_log(n, k+1))/n - log_x
        second = (mp.log(eps*(n+1)/n)-count_log(n,k)-count_log(beta,1)
                  -(n+1)*log_x)/beta
        log_r = max(first, second)
    else:
        log_r = (mp.log(eps)-count_log(n,1))/n
    log_delta = (mp.log(beta/(2*mp.pi*mp.e)) + mp.log(mp.pi*beta)/beta)/(2*(beta-1))
    log_gsa = (n-2*k-1)*log_delta
    # Compare g_0 to g_k by reducing the truncated basis through index k.
    suffix = [mp.mpf(0)] * (k+2)
    for i in range(k-1, -1, -1):
        offset = min((suffix[i+1]-suffix[i+d]+d*cost(d))/(d-1)
                     for d in range(2, min(beta, k+1-i)+1))
        suffix[i] = suffix[i+1]+offset
    propagated = (mp.log(eps)-count_log(n,1))/n - (suffix[0]-suffix[1])
    return [x/mp.log(2) for x in (log_x, log_r, log_gsa, log_gsa-log_r, propagated)]


if __name__ == '__main__':
    for n in (200, 400, 700):
        for beta in (50, 100, 200, 400):
            cells = [mp.nstr(x, 8) for x in row(n, beta)] if beta <= n else ['—']*5
            print('|', ' | '.join(map(str, [n, beta, *cells])), '|')
