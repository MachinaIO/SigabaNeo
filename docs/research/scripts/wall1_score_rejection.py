"""Interval checks for wall1_score_rejection.md. Run with Python and mpmath."""

from functools import lru_cache
from itertools import accumulate
from math import comb

from mpmath import iv

from wall1_hermite_budget import log_blichfeldt, log_floors, log_theta, maximum

iv.dps = 50
R = iv.mpf
q = 3329


def below(label, value, ceiling):
    assert value < R(ceiling), (label, value, ceiling)
    print(label, value)


def raw_mass(n, rows, radius):
    z = radius * iv.sqrt(2 * iv.pi / n)
    return iv.exp(R(n) / 2 + n * (iv.ln(z) + log_theta(z)) - rows * iv.ln(q))


@lru_cache(None)
def log_chart_factor(rank, independent):
    # Part 226, equation (1).
    small = 2 * iv.sqrt(13) * (iv.sqrt(13) + iv.sqrt(iv.pi))**rank / iv.gamma(R(rank+1)/2)
    large = (1 + 2 * iv.exp(-13) / (1 - iv.exp(-39)))**rank
    return iv.ln(small + large * R(".710")**independent)


@lru_cache(None)
def chart_logs(n, k, split):
    m = n - k
    high = (iv.ln(400 * comb(m, split)) +
            sum(log_chart_factor(k, j) for j in range(split)) +
            (m - split) * log_chart_factor(k, split))
    low = [R(0)]
    for j in range(1, split):
        low.append(iv.ln(400**3 * comb(k,j) * comb(m,j)) +
                   j * (log_chart_factor(k-j, 0) + log_chart_factor(m-j, 0)
                        + log_chart_factor(j, 0)))
    return high, low


def section_mass(n, k, log_b, deficiency, split=144):
    # Part 226 equations (2), (4), summed through deficiency. This counts
    # candidate spaces with membership, prior to imposing any selection.
    h = deficiency * iv.ln(q) + log_b
    if h < 0:
        return R(0)
    assert h >= 0 and max(k,n-k) - (k-400 + 2*deficiency - 1) >= 100
    high, low = chart_logs(n, k, split)
    terms = [v + (max(k,n-k) + 2*j + R(".02")) * h for j,v in enumerate(low)]
    low_upper = R([max(v.a for v in terms), max(v.b for v in terms)]) + iv.ln(split)
    upper = maximum(high + (n + R(".01")) * h, low_upper)
    return (4 * comb(n,k) * iv.exp(upper - deficiency*(k-400+deficiency)*iv.ln(q))
            / (1 - R(q)**(-100)))


def early_flag(draws, cutoff, floors):
    # Logarithms of Hermite upper bounds. Use the proved Part 224 profile.
    g = [R(0), R(0), iv.ln(R(4)/3)/2, iv.ln(2)/3, iv.ln(4)/4,
         iv.ln(8)/5, iv.ln(R(64)/3)/6, iv.ln(R(64)/3)/5]
    g.append(g[7] * 7 / 6)
    g.extend(log_blichfeldt(i) for i in range(9, draws + 1))
    caps = [R(0), R(0)]
    penalty = R(0)
    for rank in range(2, draws + 1):
        penalty += g[rank] / (2 * (rank - 1))
        caps.append(maximum(caps[-1], g[rank] / 2 + penalty))
    cumulative = list(accumulate(caps))
    radius = cutoff * iv.exp(caps[-1])
    assert radius < q
    total = iv.exp(R("252.5") * iv.ln(iv.pi) - iv.loggamma(R("253.5"))
                   + 505 * iv.ln(radius + iv.sqrt(505) / 2)
                   - iv.ln(2) - 400 * iv.ln(q))
    common = 506 * iv.ln(cutoff) - iv.ln(2)
    scales = [iv.sqrt(2 * iv.pi / (506 - j)) for j in range(draws)]
    weights = [iv.exp(x) for x in caps]
    theta_allowance = 505 * log_theta(cutoff)
    for i in range(1, draws + 1):
        k = draws - i + 1
        head = common - floors[i - 1] + cumulative[k] + theta_allowance
        for j in range(k):
            w = weights[k - j]
            z = maximum(R(1), w * scales[j])
            total += iv.exp(head - cumulative[k - j] + iv.pi * (w / z)**2
                            + (506 - j) * iv.ln(z))
    return total


def main():
    floors = log_floors()
    last = floors[-1]
    floor407 = maximum(last - iv.ln(q), R(505) / 506 * last - iv.ln(R("56.2142")) / 2)
    d, a = 505, R("959.5")
    t = d / (2 * (1 + a))
    u = (1 - 3 * d / (2 * a)) / 3
    assert 0 < u and u < t
    z = iv.sqrt(iv.pi / t)
    base = iv.exp(t * (1 + a) - u * a - R(d)/2 * iv.ln(1 - 3*u)
                  + d * (iv.ln(z) + log_theta(z)) - floor407)
    for k, ceiling in [(0, "1.17349e-7"), (1, "6.46897e-8"), (10, "2.02445e-19")]:
        below(f"fresh, plant heights {k}..30", base * sum(iv.exp(-t*j*j) for j in range(k, 31)), ceiling)
    below("translated raw lifts", 31 * raw_mass(912, 400, 250), "5.468e-9")
    def terminal_sections(radius, deficiency):
        return section_mass(912, 408, iv.ln(radius) - floor407, deficiency)

    below("score through deficiency 131", 124 * terminal_sections(938, 131), "1e-920")
    below("height zero through 132", 4 * terminal_sections(31, 132), "1e-258")
    below("height one through 132",
          4 * (terminal_sections(50, 132) + iv.exp(-R(2500)/12) * terminal_sections(62, 132)),
          "1e-69")
    below("large minimum, zero-suffix example", raw_mass(505, 400, 938), "1e-279")
    below("large minimum, radius-27 example", raw_mass(503, 399, 938), "1e-279")
    # Triangle bound grows on 0 <= k <= 30, as its derivative is positive there.
    below("enclosing radius at 30", 30 * iv.sqrt(a) + iv.sqrt(1 + a - 900), "938")
    margin = R("28.5")**2
    assert 2 * (margin / (margin + R("2272.5")) - R("0.00047835048014")) > R("0.52566")
    below("small prefix through 210", early_flag(210, R(13), floors), "5e-18")
    late = sum(section_mass(505+i, i, iv.ln(13)-floors[i-1], 132) for i in range(211,408))
    below("small prefix 211..407 through deficiency 132", late, "1e-1314")
    below("partial prefix charge", 420 * iv.exp(-R(169)/12), "0.000321319")
    below("full marginal prefix charge on floor", 814 * iv.exp(-R(169)/12), "0.000622746")
    radius = 26 / iv.sqrt(3)
    width = radius * iv.sqrt(2 * iv.pi / 506)
    per_draw = iv.exp(253 + 506 * iv.ln(width) + 505 * log_theta(width) - iv.ln(2) - last)
    below("fresh small-vector exit over 407 draws", 407 * per_draw, "1.02e-162")


if __name__ == "__main__":
    main()
