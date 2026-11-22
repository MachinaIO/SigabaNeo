# Terminal minimum at proportional width after one exact forward pass

At the target modulus 3329, increasing width and tour length together narrows the terminal distribution. The empirical first percentile initially falls below 0.90 and then recovers toward 0.954. The available tail counts leave the proposed 99% success rate at dimension 512 unresolved. The tables report experimental evidence.

## Sampling law and normalization

Each main row uses a uniform plain graph, $m=n-1$, width $b=n-6$, and retained rank $d=b-1=n-7$. The deterministic horizontal prefix removes six axes. The initial retained basis is therefore $qI_d$. Each of the $n$ appends draws $d$ fresh independent uniform residues and uses the inherited mark, including any loss of rank. No projected window is resampled. Holding each prime fixed across sizes permits within-modulus comparisons. The largest prime is also the modulus at the target dimension.

At append $t$, $X_t$ is the length of the selected vector divided by the Gaussian heuristic of the rank-$b$ window. After the last selection and orthogonal projection, $Y_n$ is the minimum of the rank-$d$ retained lattice divided by its own Gaussian heuristic. In rank $k$ the denominator is $(D/V_k)^{1/k}$, where $D$ is covolume in the physical span and $V_k$ is unit ball volume. Each trajectory contributes one observation to each marginal. The last three selections within a trajectory are dependent.

## Proportional sweep

Quantile columns give the empirical 1st, 5th, 50th and 95th percentiles, in that order. The last column gives the two preceding marginal medians. Threshold counts use the unrounded retained ratios and a strict inequality. Quantiles use order statistic $\lceil Np\rceil$ for probability $p$.

| n | b | q | N | Retained Y, GH units | Y < 0.954 | Final window X, GH units | Medians at n−2 / n−1 |
|---:|---:|---:|---:|:---|:---|:---|:---|
| 10 | 4 | 257 | 512 | 1.136 / 1.226 / 1.478 / 1.650 | 1 (0.20%) | 0.834 / 0.923 / 1.230 / 1.473 | 1.216 / 1.202 |
| 10 | 4 | 769 | 512 | 1.045 / 1.193 / 1.475 / 1.643 | 0 (0.00%) | 0.798 / 0.894 / 1.202 / 1.493 | 1.166 / 1.184 |
| 10 | 4 | 3329 | 512 | 1.070 / 1.190 / 1.470 / 1.654 | 1 (0.20%) | 0.737 / 0.832 / 1.186 / 1.479 | 1.144 / 1.165 |
| 12 | 6 | 257 | 512 | 1.010 / 1.091 / 1.290 / 1.453 | 1 (0.20%) | 0.735 / 0.844 / 1.131 / 1.339 | 1.123 / 1.132 |
| 12 | 6 | 769 | 512 | 1.046 / 1.110 / 1.294 / 1.442 | 0 (0.00%) | 0.689 / 0.798 / 1.133 / 1.341 | 1.099 / 1.121 |
| 12 | 6 | 3329 | 512 | 0.941 / 1.079 / 1.280 / 1.439 | 8 (1.56%) | 0.595 / 0.773 / 1.100 / 1.335 | 1.071 / 1.094 |
| 14 | 8 | 257 | 512 | 1.007 / 1.068 / 1.221 / 1.345 | 2 (0.39%) | 0.729 / 0.842 / 1.100 / 1.281 | 1.081 / 1.092 |
| 14 | 8 | 769 | 512 | 0.979 / 1.043 / 1.214 / 1.337 | 2 (0.39%) | 0.704 / 0.844 / 1.103 / 1.257 | 1.079 / 1.079 |
| 14 | 8 | 3329 | 512 | 0.887 / 0.986 / 1.201 / 1.323 | 12 (2.34%) | 0.681 / 0.807 / 1.062 / 1.226 | 1.077 / 1.077 |
| 16 | 10 | 257 | 512 | 0.945 / 1.022 / 1.177 / 1.277 | 7 (1.37%) | 0.691 / 0.832 / 1.083 / 1.210 | 1.071 / 1.071 |
| 16 | 10 | 769 | 512 | 0.942 / 1.012 / 1.161 / 1.269 | 6 (1.17%) | 0.653 / 0.828 / 1.067 / 1.209 | 1.057 / 1.058 |
| 16 | 10 | 3329 | 512 | 0.892 / 0.982 / 1.147 / 1.271 | 18 (3.52%) | 0.742 / 0.853 / 1.057 / 1.194 | 1.043 / 1.047 |
| 20 | 14 | 257 | 256 | 0.935 / 1.010 / 1.119 / 1.203 | 5 (1.95%) | 0.813 / 0.886 / 1.052 / 1.153 | 1.043 / 1.047 |
| 20 | 14 | 769 | 256 | 0.934 / 1.009 / 1.112 / 1.185 | 6 (2.34%) | 0.850 / 0.896 / 1.053 / 1.145 | 1.035 / 1.057 |
| 20 | 14 | 3329 | 256 | 0.936 / 0.991 / 1.105 / 1.190 | 5 (1.95%) | 0.744 / 0.846 / 1.045 / 1.147 | 1.036 / 1.029 |
| 24 | 18 | 257 | 256 | 0.973 / 1.004 / 1.085 / 1.153 | 0 (0.00%) | 0.828 / 0.897 / 1.047 / 1.127 | 1.032 / 1.039 |
| 24 | 18 | 769 | 256 | 0.946 / 0.988 / 1.075 / 1.144 | 5 (1.95%) | 0.826 / 0.910 / 1.030 / 1.114 | 1.029 / 1.037 |
| 24 | 18 | 3329 | 256 | 0.941 / 0.994 / 1.075 / 1.139 | 3 (1.17%) | 0.862 / 0.901 / 1.036 / 1.110 | 1.025 / 1.040 |
| 30 | 24 | 257 | 256 | 0.952 / 0.989 / 1.058 / 1.108 | 3 (1.17%) | 0.851 / 0.931 / 1.034 / 1.090 | 1.027 / 1.020 |
| 30 | 24 | 769 | 256 | 0.953 / 0.996 / 1.057 / 1.104 | 3 (1.17%) | 0.870 / 0.925 / 1.030 / 1.086 | 1.018 / 1.025 |
| 30 | 24 | 3329 | 512 | 0.945 / 0.984 / 1.052 / 1.103 | 7 (1.37%) | 0.884 / 0.916 / 1.020 / 1.082 | 1.021 / 1.019 |
| 36 | 30 | 257 | 32 | 0.965 / 0.996 / 1.048 / 1.079 | 0 (0.00%) | 0.934 / 0.943 / 1.008 / 1.063 | 1.012 / 1.015 |
| 36 | 30 | 769 | 32 | 0.938 / 0.968 / 1.037 / 1.088 | 1 (3.12%) | 0.952 / 0.986 / 1.020 / 1.058 | 1.012 / 1.020 |
| 36 | 30 | 3329 | 48 | 0.945 / 0.954 / 1.032 / 1.075 | 3 (6.25%) | 0.916 / 0.953 / 1.021 / 1.061 | 1.006 / 1.015 |

The empirical first percentile is the sixth order statistic for 512 passes and the third for 256. At 48 or 32 passes it is the sample minimum. The chance that 32 independent draws all miss a population tail of mass 1% is about 72.5%. The high-dimensional pilots mainly locate the bulk and illustrate the range of individual trajectories. Their reported minima have little power to locate a population percentile.

## Overlap with Part 119

Both rows reproduce all eight published quantiles to the displayed precision and both strict failure counts. A separate run of the unmodified Part 119 driver on the same 2,048 seeds matched all eight window ratios, first and last retained ratios, and incoming terminal mark rank seed by seed. As a further check, fpylll's proved SVP routine independently returned the same squared minimum as the rational enumerator for every window, first quotient and terminal quotient on seed offset zero at $n=10,16,24,30$ and all three main primes (264 lattice calls). The proved-SVP check compares norms. The trajectory uses the enumerator's signed lexicographic tie rule.

| n | b | q | N | Retained Y, GH units | Y < 0.954 | Final window X, GH units | Medians at n−2 / n−1 |
|---:|---:|---:|---:|:---|:---|:---|:---|
| 8 | 4 | 17 | 1024 | 1.139 / 1.280 / 1.500 / 1.661 | 0 (0.00%) | 0.857 / 0.942 / 1.257 / 1.475 | 1.194 / 1.211 |
| 8 | 6 | 17 | 1024 | 1.011 / 1.100 / 1.301 / 1.450 | 3 (0.29%) | 0.727 / 0.838 / 1.139 / 1.341 | 1.117 / 1.123 |

## What the lower tail says about dimension 512

At $q=3329$, the retained median falls from 1.470 at $n=10$ to 1.052 at $n=30$. Its lower tail behaves differently. The first percentile falls to 0.887 at $n=14$, then reaches 0.941 and 0.945 at $n=24,30$. At $n=16$ the strict failure count is 18/512, a pointwise two-sided 95% Clopper–Pearson interval of 2.10–5.50% under independent sampling. At $n=30$ it is 7/512, with nominal fixed-sample interval 0.55–2.80%. The latter spans the 1% target. Order statistics 1 and 11 in the same 512 trajectories bracket the population first percentile at a nominal fixed-sample coverage of at least 95% by a binomial calculation. That interval is [0.910, 0.959] at $n=30$ and [0.837, 0.921] at $n=16$ (rounded). These intervals describe individual rows under the sampling model. The sample sizes vary across rows, and the $n=30,q=3329$ row was expanded after inspecting its initial 256 passes. At the same dimension both smaller primes give 3/256. Across all three primes the final window has a lower first percentile than the retained lattice at $n=30$, and the last three selection medians are close. At $n=30,q=3329$, 72 of 512 final windows fell below 0.954. Only five of those 72 trajectories also failed the retained threshold, and two further retained failures followed a final window at or above 0.954.

At $n=36,q=3329$, 3/48 retained ratios fell below the threshold (6.25%, nominal exact 95% interval 1.31–17.20%). This weighs against a steady decrease in the failure rate, although the uncertainty is wide. At $n=40$ the 24-worker pilot completed 0 of 24 exact tours within a 15-minute wall-clock budget. The largest measured dimension is therefore 36.

The proposed dimension-512 statement concerns $p_{512}=\Pr(Y_{512}<0.954)$ for $(m,b,q)=(511,506,3329)$. A sustained rise in the retained first percentile above 0.954, accompanied by upper binomial limits below 1% along this same parameter path, would support extrapolation. A persistent lower tail below 0.954 with failure rates bounded above 1% would count against that extrapolation. Only evidence at the target law, or a justified comparison across dimensions, can settle the target itself. For example, under independent draws, zero failures in 299 target-dimension passes gives a one-sided 95% upper limit below 1%. A one-sided lower limit above 1% there would statistically reject the proposed rate. A mathematical refutation requires a lower bound exceeding the budget. The fixed-$n,q$ width limit of Part 119 does not apply because each additional dimension here also adds an adaptive graph selection.

## Reproduction and exactness

The run used SageMath 10.7, Python 3.12.12, fpylll 0.6.4, and Singular on the executable path. The default shell Python lacked fpylll. fpylll supplies unimodular LLL reduction. The audited closed-ball rational enumeration then resolves the shortest norm and every signed ambient lexicographic tie. This matters because a choice among tied lines can change later windows. Floating point is used for reporting the GH ratios.

To keep basis entries manageable, apply the unimodular LLL transform $U$ to the window before completing the selected coefficient row $c$. If $T$ completes $c$ in the reduced basis, the new mark before dropping its first column is $[C\;0]U^{-1}T^{-1}$. This is the coordinate change for the same physical generators. The checks verify the selected norm, completion, and terminal squared-covolume identity. The experiment measures minima and selections only. It supplies no plane-count estimate.

Save the code below as a temporary Python script and run it from the repository root in the Sage environment. Its arguments are `n b q N base workers`. For example, `python /tmp/replay.py 30 24 3329 512 1006329000 24` reproduces the target-modulus row at $n=30$. Each main row uses consecutive seeds starting at $10^9+10^5n+10^3q$. The two validation rows start at 0 and 10,000,000 respectively. Output fields are $n,b,q$, seed, $Y_n,X_{n-2},X_{n-1},X_n$. This replay omits unused diagnostics from the measurement driver. It reads the enumerator from [Part 119](wall1_experiments.md) and returns its reduced-basis coefficient and transform separately.

The SHA-256 digest of all 10,864 reported trajectories is `ff3d3b6307e2eb337ea6d2e6d3fd50a486b9bcfa083215037274e4cd42df10ea`. Hash validation rows first, then main rows in table order, with seeds ascending within each row. Encode each replay record as UTF-8 `json.dumps(r,separators=(',',':')) + '\n'`. The hash includes the floating-point outputs for this environment.

```python
from pathlib import Path
from multiprocessing import Pool
import json
import sys

# Load the audited enumerator in the same directory as the repo root invocation.
note = Path("docs/research/wall1_experiments.md").read_text()
source = note.split("```python\n", 1)[1].split("\n```", 1)[0]
enum = source.split("def trial(", 1)[0]
assert enum.count("return coeff*U,") == 1
exec(enum.replace("return coeff*U,", "return (coeff,U),"))

def measure(job):
    n,b,q,seed = job
    d = b-1
    rng = Random(seed)
    B = q*identity_matrix(QQ,d)
    C = identity_matrix(ZZ,d)
    xs = []
    for _ in range(n):
        raw = vector(ZZ,[rng.randrange(q) for i in range(d)])
        a = vector(QQ,[v % q for v in raw*C])/q
        W = B.stack(matrix([a*B])).augment(matrix(QQ,b,1,[0]*d+[1]))
        (c,U),s2,D2,_ = shortest(W)
        xs.append(ratio(s2,D2,b))
        R = U*W
        v = c*R
        _,H = matrix(c).transpose().hermite_form(
            transformation=True,include_zero_rows=True)
        T = H.inverse().transpose().change_ring(ZZ)
        assert T[0] == c and v*v == s2
        rest = T[1:]*R
        B = rest - (rest*matrix(v).transpose())*matrix(v)/s2
        C = (C.augment(zero_matrix(ZZ,d,1))*U.inverse()*H.transpose())[:,1:].change_ring(ZZ)%q
    _,l2,outdet,_ = shortest(B)
    assert outdet*s2 == D2
    return [n,b,q,seed,ratio(l2,outdet,d),*xs[-3:]]

if __name__ == "__main__":
    n,b,q,N,base,workers = map(int,sys.argv[1:])
    with Pool(workers) as pool:
        for r in pool.imap(measure,[(n,b,q,base+j) for j in range(N)]):
            print(json.dumps(r),flush=True)
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

**Reproduction.** The implementation, the checksum (ff3d3b63…, over 10,864 records) and every displayed statistic were
reproduced. The Clopper–Pearson intervals are 0.55–2.80% for 7/512 and 1.31–17.20% for 3/48.

**Main addition: physical-floor failure rates.** The ratio target 0.954 is a conservative sufficient cutoff. The physical
requirement is λ1 ≥ F_d = √(1 + 1.5d − √(4.5d/99)), with d = b − 1. At q = 3329, the empirical failure rates against that floor
are:

| n | Physical floor F_d | Y_n < 0.954 | Physical λ1 < F_d |
|---:|---:|---:|---:|
| 10 | 2.2651 | 1/512 | 389/512 |
| 12 | 2.8325 | 8/512 | 187/512 |
| 14 | 3.3070 | 12/512 | 36/512 |
| 16 | 3.7230 | 18/512 | 2/512 |
| 20 | 4.4420 | 5/256 | 0/256 |
| 24 | 5.0617 | 3/256 | 0/256 |
| 30 | 5.8718 | 7/512 | 0/512 |
| 36 | 6.5842 | 3/48 | 0/48 |

All ratio failures at n = 30 and n = 36 pass the physical floor. The 3/48 result bears on the stronger ratio target only.

**Interpretation.** Passing the floor is only a necessary condition for height-zero success. The zero-error GH radius 35.18 at
b = 506 (physical cutoff ratio 0.7804) is a counterfactual benchmark, not an established typical value.
