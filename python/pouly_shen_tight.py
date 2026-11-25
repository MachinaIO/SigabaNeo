"""Fixed-Table-1 sensitivity. Run directly with Python 3."""
import math

from pouly_shen_cost import Q, SCHEMES, TABLE1, components, log2_add


def rows(name):
    n, eta = SCHEMES[name]
    m, g, _, s, _ = TABLE1[name]
    c = components(name)
    r = math.sqrt(m * eta / 2)
    lam = math.sqrt(m / (2 * math.pi * math.e)) * Q ** (1 - n / m)
    tau = math.sqrt(m / (2 * math.pi)) / s
    u = ((lam - r) / tau) ** 2
    assert lam - r > tau
    log_true = -math.pi * (s * r) ** 2
    log_wrong = (m / 2) * (1 + math.log(u) - u)
    assert log_wrong < log_true
    gap = math.exp(log_true) * -math.expm1(log_wrong - log_true)
    log_delta = math.log2(gap) - 1
    log_k = g * math.log(Q)
    log_n_union = math.log2(log_k) - 2 * c["log2_delta"]
    log_n = math.log2(2 * (log_k + math.log(100))) - 2 * log_delta

    def cost(count):
        return log2_add(c["log2_bkz"], log2_add(c["log2_guess"], count + c["log2_mcmc"]))

    # Illustrative unit-cost model: direct separable DFT, dense projections.
    scoring = log2_add(log_n + math.log2(2 * m * (g + 1) + 1),
                       c["log2_guess"] + math.log2(2 * Q * g + 1))
    mixing = log_n + c["log2_mcmc"] + math.log2((log_n + math.log2(100)) * math.log(2))
    explicit = log2_add(c["log2_bkz"], log2_add(scoring, mixing + 2 * math.log2(m)))
    return (c["rop"], cost(log_n_union), cost(log_n_union), cost(log_n), explicit,
            log_delta, log_n, log_wrong - log_true)


if __name__ == "__main__":
    print("scheme baseline candidates geometry sample_count accounting log2_delta log2_N ln_wrong_over_true")
    for name in SCHEMES:
        print(name, *(f"{value:.4f}" for value in rows(name)))
