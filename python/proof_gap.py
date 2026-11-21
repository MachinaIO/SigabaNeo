"""Stage-1 numbers of docs/PROOF_GAP.md: the block size and cost of the primal attack on Kyber
when the GSA is replaced by the proven BKZ approximation factor ||b_1|| <= gamma^((d-1)/(beta-1))
lambda_1 (lambda_2 still from the Gaussian heuristic). Costs use RC.MATZOV (python/lwemodel).

  python3 proof_gap.py
"""

import math

from lwemodel import fx, reduction

GAMMA = {
    "1+b/4 (Minkowski)": lambda b: math.log(1 + b / 4),
    "Blichfeldt": lambda b: math.log(2 / math.pi) + 2 / b * math.lgamma(2 + b / 2),
    "heuristic b/(2 pi e)": lambda b: math.log(b / (2 * math.pi * math.e)),
}
KYBER = [("Kyber512", 512, 3), ("Kyber768", 768, 2), ("Kyber1024", 1024, 2)]
Q = 3329


def smallest_beta(n, sigma, log_gamma, max_beta=8000):
    lq = math.log(Q)
    for beta in range(40, max_beta):
        for mp in range(1, n + 1, 4):
            d = mp + n + 1
            lvol = (mp * lq + math.log(sigma)) / d
            target = math.log(sigma * math.sqrt(d))
            gh = 0.5 * math.log(d / (2 * math.pi * math.e)) + lvol
            if (d - 1) / (beta - 1) * log_gamma(beta) + target < gh:
                return beta, d
    return None


if __name__ == "__main__":
    for name, n, eta in KYBER:
        sigma = math.sqrt(eta / 2)
        print(name)
        for label, lg in GAMMA.items():
            beta, d = smallest_beta(n, sigma, lg)
            print(f"  {label}: beta={beta} cost={reduction.matzov_bits(beta, d) / fx.ONE:.1f}")
