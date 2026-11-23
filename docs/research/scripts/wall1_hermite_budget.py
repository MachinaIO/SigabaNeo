"""Check the Part 192 scalar majorant and its one-at-a-time crossings.

Run with Python and mpmath. Every printed crossing is certified by evaluating
both rational endpoints with outward-rounded intervals. Rank eight uses the
Mordell step from rank seven. Other ranks follow the existing audited profile.
"""

from mpmath import iv

iv.dps = 40
real = iv.mpf
PLANE = 52 / iv.sqrt(3)
WINNER = iv.sqrt(iv.sqrt(2) * 1352 / iv.sqrt(3))
SHARP_LOG_SEVEN = iv.ln(64) / 7
MORDELL_LOG_SEVEN = iv.ln(real(64) / 3) / 5


def maximum(a, b):
    return real([max(a.a, b.a), max(a.b, b.b)])


def log_blichfeldt(rank):
    return iv.ln(2 / iv.pi) + 2 * iv.loggamma(real(rank) / 2 + 2) / rank


def log_floors():
    values = [400 * iv.ln(3329)]
    for _ in range(406):
        last = values[-1]
        values.append(maximum(last - iv.ln(3329), real(505) / 506 * last - iv.ln(real("56.2142")) / 2))
    return values


def log_theta(width):
    exponent = -iv.pi * width**2
    return iv.log1p(2 * iv.exp(exponent) / -iv.expm1(3 * exponent))


def late_charge(rank, radius, floors):
    width = radius * iv.sqrt(2 * iv.pi / rank)
    base = real(rank) / 2 - iv.ln(2) + rank * iv.ln(width) + (rank - 1) * log_theta(width)
    return sum(iv.exp(base - floor) for floor in floors)


def prefix(floors, log_seven, log_twentyfour):
    gammas = [real(0), real(0), iv.ln(real(4) / 3) / 2, iv.ln(2) / 3, iv.ln(4) / 4,
              iv.ln(8) / 5, iv.ln(real(64) / 3) / 6, log_seven, log_seven * 7 / 6]
    gammas.extend(log_blichfeldt(rank) for rank in range(9, 156))
    gammas[24] = log_twentyfour
    log_caps = [real(0), real(0)]
    cumulative = [real(0), real(0)]
    penalty = real(0)
    for rank in range(2, 156):
        penalty += gammas[rank] / (2 * (rank - 1))
        cap = maximum(log_caps[-1], gammas[rank] / 2 + penalty)
        log_caps.append(cap)
        cumulative.append(cumulative[-1] + cap)

    caps = [iv.exp(x) for x in log_caps]
    radius = PLANE * caps[-1]
    assert radius < 3329
    log_raw = (real("252.5") * iv.ln(iv.pi) - iv.loggamma(real("253.5"))
               + 505 * iv.ln(radius + iv.sqrt(505) / 2) - iv.ln(2) - 400 * iv.ln(3329))
    widths = [iv.sqrt(2 * iv.pi / (506 - j)) for j in range(155)]
    total = real(0)
    for i in range(154):
        k = 155 - i
        common = 506 * iv.ln(PLANE) - iv.ln(2) - floors[i] + cumulative[k]
        for j in range(k):
            n = 506 - j
            w = caps[k - j]
            z = maximum(real(1), w * widths[j])
            total += iv.exp(common - cumulative[k - j] + iv.pi * (w / z)**2 + n * iv.ln(z))
    # Each theta factor is between 1 and theta(PLANE)^505 because z >= 1.
    theta = iv.exp(real([0, (505 * log_theta(PLANE)).b]))
    return radius, iv.exp(log_raw), total * theta


def main():
    floors = log_floors()
    available = real("6.515e-12") - real("4.249e-12") - real("8.147e-14")
    evaluated = available - (
        late_charge(506, WINNER, floors[:394]) + late_charge(506, real(30), floors[:406])
        + late_charge(505, PLANE, [x - iv.ln(WINNER) for x in floors[:406]]))
    rounded = available - real("2.067e-12") - real("7.190e-15") - real("1.038e-13")
    print("prefix allowances (rounded late bounds, evaluated late sums)", rounded, evaluated)
    for seven in (SHARP_LOG_SEVEN, MORDELL_LOG_SEVEN):
        for twentyfour in (iv.ln(4), log_blichfeldt(24)):
            print("g7, g24, raw radius, raw term, flag sum", iv.exp(seven), iv.exp(twentyfour),
                  *prefix(floors, seven, twentyfour))

    # For each scalar check, vary one constant and hold the other at its sharp value.
    checks = (
        ("flag certificate", real("5.28399e-15"), lambda r, u, f: f,
         ("1.81144794", "1.81144795"), ("4.00001044", "4.00001045")),
        ("raw cutoff", real(2885), lambda r, u, f: r,
         ("1.81488768", "1.81488770"), ("4.05861320", "4.05861321")),
        ("rounded late bounds", rounded, lambda r, u, f: u + f,
         ("1.81603439", "1.81603440"), ("4.07831474", "4.07831475")),
        ("evaluated late sums", evaluated, lambda r, u, f: u + f,
         ("1.81648905", "1.81648906"), ("4.08614936", "4.08614937")),
    )
    for name, limit, scalar, seven_bounds, twentyfour_bounds in checks:
        for rank, bounds in ((7, seven_bounds), (24, twentyfour_bounds)):
            values = []
            for endpoint in bounds:
                log_value = iv.ln(real(endpoint))
                seven = log_value if rank == 7 else SHARP_LOG_SEVEN
                twentyfour = log_value if rank == 24 else iv.ln(4)
                values.append(scalar(*prefix(floors, seven, twentyfour)))
            assert values[0] < limit and values[1] > limit, (rank, name, values, limit)
            print(rank, name, *bounds)


if __name__ == "__main__":
    main()
