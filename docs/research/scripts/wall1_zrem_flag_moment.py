"""Interval checks for the line and quotient bounds in wall1_zrem_flag_moment.md."""

from mpmath import iv

iv.dps = 80
I = iv.mpf
n = 505
m = n - 1
q = 3329
budget = I("6.485e-11")
alpha = iv.sqrt(3) / 2
a = 1352 / iv.sqrt(3)
B = 52 / iv.sqrt(3)
R = iv.sqrt(iv.sqrt(2) * a)
volume = [I(1), I(2)]
for dim in range(2, n + 2):
    volume.append(2 * iv.pi * volume[dim - 2] / dim)


def line_constant(dim):
    # Bound the zeta tail after its first term by an integral.
    excess = I(2) ** (-dim) + I(2) ** (1 - dim) / (dim - 1)
    return volume[dim] / (2 * (1 + I([0, 1]) * excess))


def maximum(x, y):
    assert x > y or y > x
    return x if x > y else y


def check(label, value, lo, hi):
    assert I(lo) < value < I(hi), (label, value)
    print(f"{label}: ({lo}, {hi})")


c = {dim: line_constant(dim) for dim in (503, 504, 505)}
log_q = iv.ln(q)
log_D = 400 * log_q
ball_sum = incidence_sum = inner_sum = plane_sum = I(0)
for draw in range(1, 407):
    incoming = log_D
    log_D = maximum(incoming - log_q, n * incoming / (n + 1) - iv.ln(I("56.2142")) / 2)
    if draw < 396:
        continue
    D = iv.exp(log_D)
    g = iv.exp((incoming - iv.ln(volume[506])) / 506)
    b = alpha * maximum(I("30.5"), I("0.945") * g)
    assert a / b < B and b < B
    ball = c[m] * B ** (m + 1) / D
    inner = c[m] * a**m / (b ** (m - 1) * D)
    plane = (m - 1) * iv.pi * c[m] * c[m - 1] * a**m * B**2 / (6 * D**2)
    flags = n * c[n] * c[m] * a**m * (B**2 - b**2) / (2 * D**2)
    ball_sum += ball
    inner_sum += inner
    plane_sum += plane
    incidence_sum += flags

check("largest reference ball mean", ball, "3.02518e-14", "3.02519e-14")
check("one ball per draw", ball_sum, "3.0955018e-14", "3.0955020e-14")
check("one-ball factor", budget / ball_sum, "2094.9753", "2094.9754")
check("incident case", inner_sum, "9.3340497e-18", "9.3340498e-18")
check("transverse case", plane_sum, "7.0806513e-56", "7.0806514e-56")
check("two-test factor", budget / (inner_sum + plane_sum), "6947681.00", "6947681.01")
check("all line incidences", incidence_sum, "1.9082676e-58", "1.9082677e-58")
check("incidence factor", budget / incidence_sum, "3.3983702e47", "3.3983703e47")
check("unit bound divided by budget", 1 / budget, "1.5420e10", "1.5421e10")
# Part 193's padded example. For every eligible mark its determinant is >= D_in/R.
D_in = volume[506] * I("32.2")**506
example_ball = c[m] * B**505 * R / D_in
check("example comparison required", 2 / (q * example_ball), "3.3022456e10", "3.3022457e10")
assert I(27) < B and I(27) * B > a
