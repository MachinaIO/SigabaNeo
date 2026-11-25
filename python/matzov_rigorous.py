"""Compare MATZOV.Hf with Shannon entropy in bits per CBD coefficient."""
from math import comb, log2, pi, sqrt, e, tanh


def entropy_comparison(eta):
    probabilities = [comb(2 * eta, j) / 4**eta for j in range(2 * eta + 1)]
    entropy = -sum(p * log2(p) for p in probabilities)
    variance = eta / 2
    proxy = log2(sqrt(2 * pi * e * variance) / tanh(pi**2 * variance))
    return entropy, proxy


if __name__ == "__main__":
    print("parameter,eta,entropy_bits,Hf_bits,difference_bits_per_coefficient")
    for name, eta in [("Kyber512", 3), ("Kyber768", 2), ("Kyber1024", 2)]:
        entropy, proxy = entropy_comparison(eta)
        print(f"{name},{eta},{entropy:.8f},{proxy:.8f},{proxy-entropy:.8f}")
