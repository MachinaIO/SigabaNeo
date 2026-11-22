"""Lattice reduction cost of the lattice estimator (estimator/reduction.py): root-Hermite factor
δ(β), dimensions for free, and the default cost model `RC.MATZOV` (classical, list decoding);
mirror of SigabaNeo/Lib/Lattices/Estimator/Reduction.lean. Costs are log2 values (fixed point)."""

from . import fx

# MATZOV list_decoding-classical fit: cost of sieving in dimension β' is 2^(a β' + b)
NN_A = fx.of_rat(29613500308205365, 10 ** 17)
NN_B = fx.of_rat(20387885985467914, 10 ** 15)
# CheNgu12 enumeration fit (natural log in the β log β term)
CN_A = fx.of_rat(270188776350190, 10 ** 15)
CN_B = fx.of_rat(10192050451318417, 10 ** 16)
CN_C = fx.of_rat(1610253135200765, 10 ** 14)

DELTA_SMALL = [(2, 102190), (5, 101862), (10, 101616), (15, 101485), (20, 101420), (25, 101342),
               (28, 101331), (40, 101295)]

# The largest block size the attacks scan (estimator `conf.max_beta`). The estimator's default is 1754
# (RC.ADPS16(1754, 1754) ~ 2^512); here it is raised so that the scans certify large strength (about
# 2^4673 under RC.MATZOV). Mirror of `Estimator.maxBeta`.
MAX_BETA = 16384

LOG2_2PIE = fx.log2(fx.mul(2 * fx.PI, fx.E))
LOG2_PI = fx.log2(fx.PI)
LN_4_3 = fx.ln(fx.of_rat(4, 3))


def log2_delta(beta: int) -> int:
    """log2 δ(β) (estimator `ReductionCost._delta` at an integer β)."""
    if beta <= 2:
        return fx.log2(fx.of_rat(DELTA_SMALL[0][1], 10 ** 5))
    if beta < 40:
        prev = DELTA_SMALL[0][1]
        for b, d in DELTA_SMALL[1:]:
            if b > beta:
                return fx.log2(fx.of_rat(prev, 10 ** 5))
            prev = d
    if beta == 40:
        return fx.log2(fx.of_rat(DELTA_SMALL[-1][1], 10 ** 5))
    lb = fx.log2(fx.of_int(beta))
    t = lb - LOG2_2PIE + (LOG2_PI + lb) // beta
    return t // (2 * (beta - 1))


def d4f(beta: int) -> int:
    """β ln(4/3) / ln(β/(2πe)), at least 0."""
    den = fx.log2(fx.of_int(beta)) - LOG2_2PIE
    if den <= 0:
        return 0
    return max(0, fx.div(beta * LN_4_3, fx.mul(den, fx.LN2)))


LOG2_C = fx.log2(fx.div(fx.ONE, fx.ONE - fx.exp2(-NN_A)))   # C = 1/(1 - 2^-a)


def lll_bits(d: int) -> int:
    return 3 * fx.log2(fx.of_int(d))


def svp_repeat_bits(beta: int, d: int) -> int:
    return fx.log2(fx.of_int(8 * d)) if beta < d else 0


def matzov_bits(beta: int, d: int) -> int:
    """log2 of `RC.MATZOV(β, d)`."""
    if beta < 20:
        lnb = fx.ln(fx.of_int(beta))
        c = fx.mul(CN_A * beta, lnb) - CN_B * beta + CN_C + fx.log2(fx.of_int(100))
        return fx.log2_add(lll_bits(d), svp_repeat_bits(beta, d) + c)
    beta_ = fx.of_int(beta) - d4f(beta)
    svp = LOG2_C + fx.log2(fx.of_int(max(d - beta, 1)))
    gate = LOG2_C + fx.mul(NN_A, beta_) + NN_B
    return fx.log2_add(lll_bits(d), svp + gate)
