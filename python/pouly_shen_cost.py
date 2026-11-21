"""Pouly–Shen provable dual attack (ePrint 2023/1508, fixed version, Section 4.4 and Table 1):
component-wise reimplementation of their cost formula, plus the polynomial factors they omit.

This is an independent reimplementation from the paper text and the formulas in their public
estimator (gitlab.inria.fr/apouly/dual-attack-estimator, `compute_cost`), not their code.
BKZ cost uses this repository's port of the estimator's MATZOV model (lwemodel.reduction).

Paper formula (24), with their choices:
    rop = N * T_MCMC + q^{n_guess} + T_BKZ(m, beta)
    delta = exp(-m s^2 sigma_e^2 / 2) / 100,   N = n ln q / delta^2,   sigma_e = sqrt(2 pi) * stddev
    T_MCMC = prod_i rho_{|b_i*|/(q s)}(Z) with GSA |b_i*| = q^{n_dual/m} delta_beta^{m-1-2(i-1)}
Omitted factors made explicit here (our accounting, labelled):
    * scoring: N inner products of length m (N*m mults) + DFT over Z_q^{n_guess}: q^{n_guess} * n_guess * log2 q
    * MCMC: per sample ln(1/eps) * Delta mixing steps, eps = 1/(100 N), each step ~ m^2 ops (one Klein pass)
"""
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lwemodel import reduction  # noqa: E402

FX = 2 ** 48
Q = 3329
# Estimator schemes: Kyber512 uses CBD(3) for s and e; Kyber768/1024 CBD(2).
SCHEMES = {"Kyber512": (512, 3), "Kyber768": (768, 2), "Kyber1024": (1024, 2)}
# Table 1 (fixed version), no modulus switching: (m, n_guess, beta, s, reported attack bits)
TABLE1 = {
    "Kyber512": (1023, 19, 746, 0.090, 238),
    "Kyber768": (1519, 29, 1129, 0.110, 347),
    "Kyber1024": (2025, 39, 1602, 0.110, 478),
}
LN2 = math.log(2)


def delta_beta(beta):
    return ((beta / (2 * math.pi * math.e)) * (math.pi * beta) ** (1 / beta)) ** (1 / (2 * (beta - 1)))


def log2_rho_Z(x):
    # rho_x(Z) as in their rho_Z (Lemma 1 approximation)
    if x <= 1:
        return math.log2(1 + 2 * math.exp(-math.pi / x ** 2))
    return math.log2(x) + math.log2(1 + 2 * math.exp(-math.pi * x ** 2))


def log2_add(a, b):
    m = max(a, b)
    return m + math.log2(2 ** (a - m) + 2 ** (b - m))


def components(name):
    n, eta = SCHEMES[name]
    m, ng, beta, s, reported = TABLE1[name]
    nd = n - ng
    sigma_e = math.sqrt(2 * math.pi) * math.sqrt(eta / 2)
    log2_delta = (-m * s ** 2 * sigma_e ** 2 / 2) / LN2 - math.log2(100)
    log2_N = math.log2(n * math.log(Q)) - 2 * log2_delta
    db = delta_beta(beta)
    red_vol = Q ** (nd / m)
    log2_mcmc = sum(
        log2_rho_Z(red_vol * db ** (m - 1 - 2 * (i - 1)) / (Q * s)) for i in range(1, m + 1)
    )
    log2_guess = ng * math.log2(Q)
    log2_bkz = reduction.matzov_bits(beta, m) / FX
    rop = log2_add(log2_add(log2_N + log2_mcmc, log2_guess), log2_bkz)
    # explicit polynomial factors (our accounting)
    log2_eps_inv = log2_N + math.log2(100)
    mcmc_explicit = log2_mcmc + math.log2(log2_eps_inv * LN2) + 2 * math.log2(m)
    score = log2_add(log2_N + math.log2(m), log2_guess + math.log2(ng * math.log2(Q)))
    rop_explicit = log2_add(log2_add(log2_N + mcmc_explicit, score), log2_bkz)
    return dict(name=name, m=m, n_guess=ng, beta=beta, s=s, reported=reported,
                log2_delta=log2_delta, log2_N=log2_N, log2_mcmc=log2_mcmc,
                log2_guess=log2_guess, log2_bkz=log2_bkz, rop=rop, rop_explicit=rop_explicit)


def main():
    est = {"Kyber512": (149.88, 139.66), "Kyber768": (214.29, 196.37), "Kyber1024": (288.53, 262.34)}
    print("| Kyber | m | n_guess | β | s | log2 δ | log2 N | log2 T_MCMC | log2 q^n_guess | log2 T_BKZ "
          "| total (paper formula) | Table 1 | total with explicit poly factors | − est. dual | − est. dual hybrid |")
    print("| --- |" + " ---: |" * 15)
    for name in SCHEMES:
        c = components(name)
        d, h = est[name]
        print(f"| {name[5:]} | {c['m']} | {c['n_guess']} | {c['beta']} | {c['s']:.3f} | {c['log2_delta']:.2f} "
              f"| {c['log2_N']:.2f} | {c['log2_mcmc']:.2f} | {c['log2_guess']:.2f} | {c['log2_bkz']:.2f} "
              f"| {c['rop']:.2f} | {c['reported']} | {c['rop_explicit']:.2f} "
              f"| {c['rop_explicit'] - d:+.2f} | {c['rop_explicit'] - h:+.2f} |")


if __name__ == "__main__":
    main()
