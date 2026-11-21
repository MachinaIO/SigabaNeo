# A conservative bound on LWE (`SigabaNeo/Lib/Lattices/Hardness.lean`)

The assumptions' `H` is now the formalized lattice estimator ([LWE_ESTIMATOR.md](LWE_ESTIMATOR.md)).
`Hardness.securityBits N rank m q error secret` is kept as a cross-check: a
**deliberately conservative lower bound on the cost of every known classical attack**, designed so
that any looseness makes it smaller than the best attack, never larger.

`python/lwe_hardness.py` mirrors the Lean definition with the same integer arithmetic.
`python/tests/test_hardness.py` checks that the two agree, and `lwe_hardness.py validate` compares
`H` with the [lattice estimator](https://github.com/malb/lattice-estimator).

## Parameters

| Field | Meaning |
| --- | --- |
| `N` | ring degree, `R = Z[X]/(X^N + 1)`; must be a power of two |
| `rank` | module rank; the LWE dimension is `n = N · rank` |
| `m` | module samples; the LWE view has `N · m` samples |
| `q` | modulus, `q ≥ 2` |
| `s` | error width: errors from `D_{Z,s}`, `ρ_s(x) = exp(-π x²/s²)`, standard deviation at most `s/√(2π)` |
| `secret` | `uniform` (over `Z_q`), `gauss s'` (`D_{Z,s'}`), `bounded B` (uniform on `{-B, …, B}`; `B = 1` is ternary) |

Outside this domain (`N` not a power of two, `q < 2`, `s ≤ 0`, `B = 0`, …) the claim is `0`.
`X^N + 1` is reducible over `Z` when `N` is not a power of two (for odd `N` it has the factor
`X + 1`, which gives LWE of dimension 1).

## Cost model

All costs are in bits of operations. The attackers of `HardAt` are classical multi-tape Turing
machines. A RAM step costs a Turing machine at least a constant number of steps, so a lower bound
on RAM operations is also a lower bound on Turing machine steps. Quantum attacks are not in the
model.

`H = max(0, min(lattice, algebraic, guessing, bitsCap) − log₂ N − safetyBits)`. Each term is the
minimum over up to three views `(samples, secret law, error law)` of the instance:

1. the instance itself (`N·m` samples, the given secret, errors `D_{Z,s}`);
2. its **normal form**, when `N·m > n`. A uniform (or wide) secret is traded for one distributed
   like the errors, with `n` fewer samples [ACPS09]. The estimator applies this when `m ≥ 2n`;
   `H` applies it whenever `m > n`;
3. the **swap**, when `N·m ≥ n` and the secret is not uniform. For `n` samples with `A`
   invertible, `A⁻¹ b = s + A⁻¹ e` is LWE with secret `e` and error `s`. The estimator applies
   this when `m = n` and the errors are narrower than the secret.

### Lattice reduction (primal uSVP/BDD, dual, hybrids)

The block size is the smallest `β` with which the primal attack succeeds under the geometric series
assumption. This is the "2016 estimate" [ADPS16, AGVW17], as in the estimator's `primal_usvp`:

```
√(σ_e² β) ≤ δ(β)^{2β−d−1} · (σ_e · ξ^n · q^{d−n−1})^{1/d}
```

Here `σ_e` is the error's standard deviation and `ξ = max(1, σ_e/σ_s)` rescales a small secret.
When the errors are the narrower part, the error coordinates are rescaled instead. Both parts are
brought to `σ* = max(σ_e, σ_s)`, and scaling the `m'` error coordinates by `σ*/σ_e` multiplies the
`q`-ary part of the volume, so `log q` becomes `log q + log(σ*/σ_e)`.
`δ(β)` is the estimator's root-Hermite factor: its table for `β ≤ 40`, and
`(β/(2πe) · (πβ)^{1/β})^{1/(2(β−1))}` above. The condition is taken over **every** embedding
dimension `d ∈ [n+1, n+N·m+1]`. The left side minus the right side is concave in `d`, so the
best `d` is computed in closed form, `d* = √(−C/log δ)`, and clamped to the range.

The cost of BKZ-`β` is taken as `2^{0.292 (β − d4f(β))}`:

* `0.292` is the exponent of the best classical sieve [BDGL16];
* `d4f(β) = β log(4/3)/log(β/(2πe))` is Ducas' "dimensions for free" [Duc18];
* no polynomial factor is counted: no additive constant (the estimator's MATZOV model adds about
  20 bits), no number of SVP calls, and no cost of LLL.

This is below every lattice attack in the estimator (`usvp`, `bdd`, `bdd_hybrid`,
`bdd_mitm_hybrid`, `dual`, `dual_hybrid`) under both its default (MATZOV) and Core-SVP (ADPS16)
cost models, on the validation grid below. The dual and hybrid attacks are not modelled
separately. They improve on the primal attack by a few bits, while dropping the polynomial factors
and the dimensions for free removes more than ten.

### Algebraic attacks (Arora–Ge, Gröbner bases)

Assume every error used lies in `[−B, B]`. Each sample then gives an equation of degree
`D = 2B + 1` in `n` variables. A bounded secret adds `n` equations of degree `2B_s + 1`. A Gaussian
secret also adds `n` such equations, for every `B_s`, and pays for its range like the errors do.
To solve at degree `d`, the ideal must contain every monomial of degree `d`, which gives the
counting bound

```
M · c(d − D) + n · c(d − D_s) ≥ c(d),      c(k) = binom(n − 1 + k, k)
```

This is a lower bound on the degree of regularity used by the estimator's `arora_gb` (and holds
for any system). The attack costs at least `binom(n + d, d)^2` (the estimator's `ω = 2`). It
succeeds only if all `M` errors are in range, with probability at most `Pr[|e| ≤ B]^M`. A lower
bound on `log₂ (1/Pr[|e| ≤ B])` uses two facts: a point mass of `D_{Z,s}` is at most
`1/max(1, s)`, and `Pr[|e| > B] ≥ 2 exp(−π(B+1)²/s²)/(1+s)`. The bound is minimised over `B`,
`d` and the number of samples `M ≤ N·m`. Gaussian errors are unbounded, so a very small `s` (or
very many samples) makes this term small, as it should.

### Exhaustive search and meet-in-the-middle

Half the secret's min-entropy: `n/2 · log₂ max(1, s')` for `D_{Z,s'}`, `n/2 · log₂(2B+1)` for
`bounded B`, and `n/2 · log₂ q` for uniform. The normal form view gives the error's.

### Ring structure

Ring-LWE and Module-LWE are attacked through their LWE view. No known attack on power-of-two
cyclotomics does better than that by more than polynomial factors, such as the `N` rotations of a
short vector. `log₂ N` bits are subtracted for them.

### Arithmetic

Every quantity is an interval of fixed-point numbers with 32 fractional bits. Logarithms come from
repeated squaring of the mantissa, π and e from rational enclosures, and the estimator's δ table
from its decimals. Every step rounds towards the attacker: the success condition is tested on an
upper bound, costs are lower bounds, and widths are lower bounds. The variance of `D_{Z,s}` is at
most `s²/(2π)` and at least `r(s) · s²/(2π)`:

| `s` | `≥ 2` | `[1.5, 2)` | `[1.2, 1.5)` | `[1, 1.2)` | `< 1` |
| --- | --- | --- | --- | --- | --- |
| `r(s)` | 0.999 | 0.97 | 0.8 | 0.49 | variance `≥ 2 ρ_s(1)/ρ_s(Z) ≥ 2^{1−⌈π log₂e / s²⌉}/(1+s)` |

The loops of the algebraic bound run with explicit fuel (`8n + 256` iterations). Running out
gives `0`. Everything is computable, and `decide +kernel` evaluates `k ≤ securityBits …` in a few
seconds.

## Validation

`sage -python python/lwe_hardness.py validate ESTIMATOR_DIR` compares `H` (plain LWE, `N = 1`)
with the cheapest attack the estimator reports. The estimator runs with its default model, the
Core-SVP model (ADPS16, all attacks) and `estimate.rough`. The grid has 720 points:

* `n ∈ {128, 256, 512, 1024, 2048}`;
* `q ≈ 2^{10}, 2^{16}, 2^{32}, 2^{64}`;
* `s ∈ {1, 3, 8, 64}`;
* uniform, Gaussian and ternary secrets;
* `m ∈ {n, 2n, ∞}`.

Status (interim, 247 of 720 points): `H` is below the cheapest estimator attack at every point but
one. The exception is `n = 256, q = 1023, s = 64`, uniform secret, unbounded samples, where coded-BKW
costs 2^197.2 and `H = 209`. The grid gave the estimator `m = ∞` but `H` `m = 2^64`, and this BKW
run needs ≈ 2^186 samples, so the comparison is not like for like. `H` has no BKW term for very
large `m`; that is open. An earlier violation (`n = 256, q = 1023, s = 1`, ternary secret, `m = n`:
`bdd_hybrid` at 2^12.2 against `H = 24`) led to the swapped view; there `H` is now `0`.

Examples (Module-LWE, `N = 256`):

| Parameters (Gaussian proxy with Kyber's standard deviation) | `H` | Kyber spec Core-SVP |
| --- | --- | --- |
| Kyber512: `rank 2, m 2, q 3329, σ = √1.5` | 99 | 118 |
| Kyber768: `rank 3, m 3, q 3329, σ = 1` | 159 | 182 |
| Kyber1024: `rank 4, m 4, q 3329, σ = 1` | 228 | 256 |

These are below Kyber's own figures. This `H` is a conservative lower bound: it drops polynomial
factors, subtracts the dimensions for free and subtracts `log₂ N`.

## Not covered

* **Sparse secrets** (fixed Hamming weight) are not a `SecretDist`. Hybrid and MITM attacks exploit
  them, and `H` does not model those.
* **BKW** is not modelled. With `m` bounded it lacks samples. With unbounded `m`, the estimator's
  coded-BKW is never the cheapest attack on the grid.
* **Quantum** attacks, and attacks on rings other than power-of-two cyclotomics.
* Attacks found after the estimator's revision `53da598` (August 2026). These lower `H` only
  through proven attacks in the harness.

## References

* [ACPS09] Applebaum, Cash, Peikert, Sahai. Fast cryptographic primitives and circular-secure
  encryption based on hard learning problems. CRYPTO 2009.
* [ADPS16] Alkim, Ducas, Pöppelmann, Schwabe. Post-quantum key exchange — a new hope. USENIX 2016.
* [AGVW17] Albrecht, Göpfert, Virdia, Wunderer. Revisiting the expected cost of solving uSVP and
  applications to LWE. ASIACRYPT 2017.
* [BDGL16] Becker, Ducas, Gama, Laarhoven. New directions in nearest neighbor searching with
  applications to lattice sieving. SODA 2016.
* [Duc18] Ducas. Shortest vector from lattice sieving: a few dimensions for free. EUROCRYPT 2018.
* [AG11] Arora, Ge. New algorithms for learning in presence of errors. ICALP 2011.
* [ACFP14] Albrecht, Cid, Faugère, Perret. Algebraic algorithms for LWE. ePrint 2014/1018.
* [MATZOV22] MATZOV. Report on the security of LWE: improved dual lattice attack. 2022.
* The lattice estimator, https://github.com/malb/lattice-estimator (`reduction.py`,
  `lwe_primal.py`, `gb.py`, `lwe_guess.py`).
