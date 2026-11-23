"""Outward interval certificate for the draw-406 membership-only flag count."""

from itertools import product

from mpmath import iv

iv.dps = 75
R = iv.mpf
q = 3329
rows = 400
log10 = iv.log(10)


def log_volume(d):
    volume = R(1) if d % 2 == 0 else R(2)
    for k in range(2 + d % 2, d + 1, 2):
        volume *= 2 * iv.pi / k
    return iv.log(volume)


def show_enclosure(name, interval, lower, upper):
    assert R(lower) < interval and interval < R(upper), (name, interval)
    print(f"{name} in ({lower}, {upper})")


def main():
    freeze_pivots = [*range(106, 510), 104, 511]
    assert len(freeze_pivots) == 406
    assert all(p <= 105 + i for i, p in enumerate(freeze_pivots, 1))
    assert sorted([*range(1, 104), *freeze_pivots, 105, 510]) == list(range(1, 512))

    # One output row over F_3, two input rows. Tuples are (input, output).
    # Check independent, dependent, incompatible, and zero-residue columns.
    for constraints, expected in [
        ([((1, 0), 2), ((0, 1), 1)], 1),
        ([((1, 0), 2), ((2, 0), 1)], 3),
        ([((1, 0), 2), ((2, 0), 0)], 0),
        ([((0, 0), 0)], 9),
    ]:
        count = sum(all((a*x + b*y - out) % 3 == 0 for (x, y), out in constraints)
                    for a, b in product(range(3), repeat=2))
        assert count == expected

    # Each choice stands for one coset modulo the preceding integer flag.
    d = 502
    delta = iv.sqrt(d) / 2
    unit_ball = log_volume(d)
    lower = upper = rows * iv.log(q)
    mass = R(0)
    checkpoints = {100: ("5000.0358", "5000.0359"),
                   200: ("10518.0262", "10518.0263"),
                   300: ("14821.0397", "14821.0398"),
                   405: ("15478.8820", "15478.8821")}

    for step in range(1, 406):
        hermite = iv.sqrt(R("56.2142")) * iv.exp(lower / 506)
        assert hermite < q or hermite > q
        radius = min(R(q), hermite)
        outer = iv.sqrt(radius**2 - 1)
        inner = outer - 2 * delta - 1
        assert inner > 1
        x = outer - delta
        mass += unit_ball + d * iv.log(x) + iv.log(1 - (1 - 1 / x)**d) - upper
        lower -= iv.log(radius)
        upper -= iv.log(inner)
        if step in checkpoints:
            show_enclosure(f"log10 weighted prefixes at {step}", mass / log10,
                           *checkpoints[step])

    # The reserved old coordinate 103 has coefficient 31 at the last freeze.
    final_cap = R("33.2")
    assert final_cap < iv.sqrt(R("56.2142")) * iv.exp(lower / 506)
    assert final_cap < 2**(R(1) / 4) * iv.sqrt(1352 / iv.sqrt(3))
    last_ball = iv.sqrt(final_cap**2 - 31**2 - 1) - delta
    assert last_ball > R("0.6396")
    mass += unit_ball + d * iv.log(last_ball) - upper
    upper -= iv.log(iv.sqrt(31**2 + 1))
    show_enclosure("log10 weighted prefixes at 406", mass / log10,
                   "14592.4241", "14592.4242")

    # Both final lifts use the same old grid, with distinct unit pivots.
    assert 27**2 < 1352 / iv.sqrt(3)
    last_ball = iv.sqrt(27**2 - 1) - iv.sqrt(503) / 2
    mass += 2 * (log_volume(503) + 503 * iv.log(last_ball) - upper)
    log_cost = rows * 408 * iv.log(q) / log10
    show_enclosure("log10 certificate for weighted pairs", mass / log10,
                   "14220.3962", "14220.3963")
    show_enclosure("-log10 membership per pair", log_cost,
                   "574841.6113", "574841.6114")
    show_enclosure("log10 certificate for distinct pairs", mass / log10 + log_cost,
                   "589062.0075", "589062.0077")

    for name, budget, lower_loss, upper_loss in [
        ("vertical", "6.485e-11", "620.73006889", "620.73006892"),
        ("horizontal", "7.1275e-11", "620.68904165", "620.68904168"),
    ]:
        budget = R(budget)
        radial = R(["610.54197888", "610.54197889"])
        show_enclosure(f"log10 Part 201 radial term / {name} budget",
                       radial - iv.log(budget) / log10, lower_loss, upper_loss)
        print(f"unit charge / {name} budget = {float((1 / budget).mid):.6f}")


if __name__ == "__main__":
    main()
