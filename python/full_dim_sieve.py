"""The full-dimension sieve route of docs/PROOF_GAP.md: run the (provable, average-case) sieve on the
planted LWE embedding lattice itself, with no BKZ. For Kyber-size plain LWE, choose the number of
samples m minimizing d = m + n + 1 such that the stage-2 bound
Pr[lambda_2 <= R] <= ((R + sqrt(d)/2)/G)^d is below 2^-64 at R = 1.05 * ||(e, s, 1)||, and
R sqrt(1 + B^2) < q. Then report 0.2925 d (sieve with search lemma P') and 0.415 d (T1).

  python3 full_dim_sieve.py
"""

import math


def ln_ball(d):
    return d / 2 * math.log(math.pi) - math.lgamma(d / 2 + 1)


def route(n, eta, q, fail_bits=64, slack=1.05):
    sigma, B = math.sqrt(eta / 2), eta
    for m in range(1, 20 * n):
        d = m + n + 1
        G = math.exp((m * math.log(q) - ln_ball(d)) / d)
        R = slack * sigma * math.sqrt(m + n)
        if R * math.sqrt(1 + B * B) >= q:
            continue
        lnfail = d * math.log((R + math.sqrt(d) / 2) / G)
        if lnfail < -fail_bits * math.log(2):
            return m, d, G, R, lnfail / math.log(2)
    return None


if __name__ == "__main__":
    for name, n, eta in [("Kyber512", 512, 3), ("Kyber768", 768, 2), ("Kyber1024", 1024, 2)]:
        m, d, G, R, fb = route(n, eta, 3329)
        print(f"{name}: m={m} d={d} G={G:.1f} R={R:.1f} stage-2 failure 2^{fb:.0f}; "
              f"0.2925d={0.2925 * d:.0f} bits, 0.415d={0.415 * d:.0f} bits")
