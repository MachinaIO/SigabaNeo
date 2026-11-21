"""PrimalHybrid under GSA, MATZOV and the fixed-weight guessing model.

Use the estimator's local search for block size and rank. Refine an eight-interval
grid over guessed dimension and Hamming weight, optimizing weight for each block size.
"""
from functools import lru_cache
from math import comb

from . import fx
from . import num_primal as num
from .params import LWE
from .reduction import log2_delta, matzov_bits
from .usvp import MAX_BETA, cost_gsa, log2_xi


def estimate(params: LWE, mitm: bool, plain: bool = False):
    p = params.normalize()
    if min(p.Xs.stddev, p.Xe.stddev, p.q, p.n) <= 0:
        return None
    m = p.m
    if m is not None and p.Xs.stddev <= p.Xe.stddev:
        m += p.n
    upper = min(MAX_BETA, m) if m is not None else MAX_BETA
    baseline_beta, baseline = num.local_minimum(
        40, max(45, upper), 5, lambda beta: cost_gsa(beta, p, m))
    max_beta = upper if baseline is None else baseline_beta
    log_q, log_xi = fx.log2_nat(p.q), log2_xi(p)
    log_sigma = fx.log2(p.Xe.stddev)
    weight = p.Xs.hamming_weight()
    bounds = p.Xs.bounds or (0, 0)  # as Lean: `bounds.getD (0, 0)`

    @lru_cache(None)
    def cost_zeta(zeta):
        remaining = p.n - zeta
        # Upstream resize preserves the infinite bounds of ND.DiscreteGaussian(sigma).
        # Only the all-zero guess has a finite search space for this constructor.
        gaussian = p.Xs.kind == "gauss"
        if gaussian and weight > remaining:
            return None
        log_den = fx.log2_nat(comb(p.n, zeta))
        weights = []
        space = hits = 0
        max_weight = 0 if gaussian else min(zeta, weight)
        for w in range(max(0, weight - remaining), max_weight + 1):
            space += comb(zeta, w) * (bounds[1] - bounds[0]) ** w
            hits += comb(weight, w) * comb(p.n - weight, zeta - w)
            guesses = fx.log2_nat(space) // (2 if mitm else 1)
            weights.append((guesses, fx.log2_nat(hits) - log_den))

        def rank(beta):
            squared = fx.div(remaining * (log_q - log_xi), log2_delta(beta))
            d = fx.ceil(fx.sqrt(squared))
            return max(beta, min(d, m - zeta) if m is not None else d)

        def cost_at(beta, d):
            if d < beta or (m is not None and beta > m - zeta):
                return None
            delta = log2_delta(beta)
            avg = log_q - remaining * (log_q - log_xi) // d - log_sigma
            red = matzov_bits(beta, d)
            if mitm:
                lift = d
                svp = 2 * fx.log2_nat(d)
            else:
                lo, hi = 0, min(d, 1754) if d > 4096 else d
                while lo < hi:
                    k = (lo + hi + 1) // 2
                    if avg - (d - k) * delta < num.threshold(k):
                        lo = k
                    else:
                        hi = k - 1
                eta = lo + 1
                if eta > d:
                    return None
                lift = d - eta
                svp = fx.log2_add(matzov_bits(eta + 1, eta + 1), 2 * fx.log2_nat(max(lift, 1)))

            first = avg + (d - 1) * delta
            log_prob = num.profile(lift, first, 2 * delta, False)
            if mitm and zeta:
                log_prob += num.profile(d, first, 2 * delta, True)

            def guess(i):
                guesses, log_hit = weights[i]
                return fx.log2_add(red, svp + guesses) + num.repetitions(log_prob + log_hit)

            return num.minimize(0, len(weights) - 1, guess)[1]

        beta, cost = num.local_minimum(40, max_beta + 2, 2, lambda b: cost_at(b, rank(b)))
        if plain and cost is not None:
            return num.local_minimum(remaining, rank(beta) + 1, 1, lambda d: cost_at(beta, d))[1]
        return cost

    return cost_zeta(0) if plain else num.minimize(0, p.n - 1, cost_zeta)[1]


def cost_bdd(params: LWE):
    return estimate(params, False)


def cost_mitm(params: LWE):
    return estimate(params, True)
