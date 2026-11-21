# How far below typical BKZ output do bad reduced bases reach? (numerical)

**Result.** In ranks 24–60 with widths 8–20, adversarial search finds exactly verified BKZ-$b$ bases whose terminal length $g_k$, $k=N-b$, sits at $0.87$–$0.95$ times the typical BKZ value. The median over lattices is about $0.90$. Every such basis gets there through one local dip at index $k$: $g_k/g_{k-1}$ is pushed toward the adjacent two-column floor $t=\sqrt3/2$. We found no globally steeper profile and no systematic gain in $\det W$. Search gains saturate with effort, and planted large-covolume prefixes always fail a crossing window. In this range the data do not support a minimum $M_b$ far below GSA. They do rule out lower bounds equal to the typical value itself. This is evidence, not proof: the search finds upper bounds on $M_b$ in small dimension. [Bad reduced bases](wall1_bad_reduced_bases.md)

## What was computed

Indices are zero-based and lengths are normalized by $\det^{1/N}$. Windows are $[i,\min(i+b,N))$ for every $i\le N-2$, including truncated ones, as in the definition of $M_b$. The lattice families are:

* q-ary lattices of rank $2n$ and determinant $q^n$, with $q=3329$ or $257$;
* Goldstein–Mayer lattices with prime determinant $p\approx2^{2N}$.

For each lattice the search proceeds in four steps. All BKZ runs use fplll with exact enumeration.

1. Standard BKZ from the given basis, run to a clean tour.
2. Reverse-order and progressive variants.
3. $R$ random unimodular restarts, each followed by BKZ.
4. $S$ annealed local-search steps over BKZ fixed points, minimizing $g_k$. Moves add tail vectors into the prefix $W$, swap prefix and tail vectors, or apply unimodular moves on windows straddling $k$. Each move is followed by BKZ repair.

The budgets were $R=1000$ and $S=3000$, reduced to $300$ and $900$ at $N=60$. Deep runs used $2$–$3\cdot10^4$ of each.

Every reported standard and best basis was checked exactly. Size reduction was checked on a rational Gram–Schmidt decomposition. Each window was enumerated in 320-bit MPFR at radius $r_{ii}(1+10^{-6})$, and each candidate's projected norm was recomputed in rationals. fplll's $1-\delta$ slack was removed by exact unimodular insertions until the exact check passed. All 202 best bases passed.

## Numbers

Columns: median standard BKZ output, median restart, best found (median and minimum over lattices), and the ratio of the best to the same lattice's restart median.

| family | $N$ | $b$ | lattices | std | restart median | best (median / min) | best ÷ restart median: median / min |
|---|---|---|---|---|---|---|---|
| q-ary 3329 | 24 | 8 | 16 | 0.882 | 0.889 | 0.809 / 0.793 | 0.912 / 0.889 |
| q-ary 3329 | 24 | 12 | 16 | 0.994 | 1.001 | 0.952 / 0.914 | 0.954 / 0.920 |
| q-ary 3329 | 32 | 8 | 16 | 0.791 | 0.784 | 0.707 / 0.691 | 0.903 / 0.873 |
| q-ary 3329 | 32 | 16 | 16 | 0.994 | 1.002 | 0.929 / 0.893 | 0.919 / 0.882 |
| q-ary 3329 | 40 | 10 | 16 | 0.738 | 0.742 | 0.666 / 0.652 | 0.899 / 0.876 |
| q-ary 3329 | 40 | 20 | 16 | 1.001 | 0.999 | 0.908 / 0.890 | 0.907 / 0.882 |
| q-ary 257 | 40 | 20 | 16 | 0.988 | 0.997 | 0.907 / 0.896 | 0.908 / 0.893 |
| q-ary 3329 | 60 | 10 | 8 | 0.530 | 0.553 | 0.497 / 0.482 | 0.899 / 0.872 |
| q-ary 3329 | 60 | 20 | 8 | 0.786 | 0.765 | 0.687 / 0.672 | 0.901 / 0.875 |
| GM | 32 | 16 | 16 | 1.005 | 1.002 | 0.918 / 0.873 | 0.917 / 0.871 |
| GM | 40 | 20 | 16 | 0.993 | 0.999 | 0.906 / 0.891 | 0.907 / 0.894 |

A line fitted to the standard profile agrees with the standard value to within about $3\%$. The deficit is therefore about $3$–$4$ index steps of the GSA line at every size. It shows no visible trend in $N$ or $k$.

The restart population is close to log-normal, with standard deviation of $\ln g_k$ between $0.025$ and $0.033$. The minimum over the first $m$ restarts falls by about $0.01$–$0.02$ per decade of $m$ and then stalls. In the deep runs at $N=40$, $b=10$, the ratio to the median was $0.90$ at $m=10^3$, $0.876$–$0.887$ at $10^4$, and $0.874$–$0.887$ at $2\cdot10^4$. Local search rarely improved on the best restart.

## The only lever found is a local dip

The table compares the standard basis with the best basis found. $H_T=g_k/\det(T)^{1/b}$ is the Hermite ratio of the terminal quotient.

| configuration | $g_k/g_{k-1}$, std → best (best min) | $g_{k+1}/g_k$, std → best | $\ln H_T$, std → best | $\ln\det W$, std → best |
|---|---|---|---|---|
| q-ary $N=40$, $b=10$ | 0.959 → 0.909 (0.881) | 0.956 → 1.076 | 0.130 → 0.035 | 4.32 → 4.41 |
| q-ary $N=40$, $b=20$ | 0.971 → 0.899 (0.873) | 0.975 → 1.062 | 0.277 → 0.185 | 5.55 → 5.63 |
| GM $N=40$, $b=20$ | 0.981 → 0.896 (0.875) | 0.975 → 1.060 | 0.276 → 0.182 | 5.64 → 5.62 |
| q-ary $N=60$, $b=10$ | 0.929 → 0.894 (0.885) | 0.992 → 1.065 | 0.112 → 0.037 | 7.41 → 7.37 |
| q-ary $N=60$, $b=20$ | 1.003 → 0.898 (0.876) | 0.947 → 1.056 | 0.294 → 0.164 | 10.85 → 10.80 |

At $N=40$, the mean of $\ln(g_i^{\rm best}/g_i^{\rm std})$ is about $-0.10$ at $i=k$ and within $\pm0.03$ at every other index. The adversary does not enlarge the prefix covolume. It selects a quotient whose first minimum is short for its covolume, and the next length rebounds. The smallest adjacent ratio in any best basis was $0.873$, against the floor $t=0.866$.

## Planted prefixes do not survive

We took $W$ from a weaker reduction (LLL, BKZ-4, BKZ-6 or BKZ-$b/2$), reduced $W$ inside $W$ and $T$ inside $T$ without changing either lattice, and checked the concatenation exactly. Whenever $\ln\det W$ exceeded the standard prefix value, by between $0.2$ and $24$, the concatenation failed. Only crossing windows $k-b+1,\dots,k-1$ failed. A minimal repair, using window insertions without global LLL, returned $g_k$ to $0.96$–$1.04$ times the standard value. The few concatenations that passed had $W$ about as reduced as BKZ-$b$ already gives ($\Delta\ln\det W\approx0$). The runs covered 8 lattices for each of $(24,8)$, $(32,16)$ and $(40,10)$, and 1 for $(40,20)$.

## Caveats

* The search explores neighbourhoods of BKZ fixed points, so its values are upper bounds on $M_b$.
* A global steepening from many windows with Hermite ratio well above the Gaussian heuristic would scale like $N\log(\sqrt{\gamma_b}/\mathrm{GH}_b)$. It could appear only at ranks far beyond 60. Nothing here exhibits even a weak version of it, but nothing here excludes it.
* When $N=2b$ the index $k$ is the centre of the profile.
* Restart values come from fplll at $\delta=0.99999$ and were not individually verified exactly. All reported standard and best bases were.

## Audit note (independent audit, Nov 2026)

28 sampled best bases (2 per configuration + all deep runs) were re-verified with an independent exact checker (rational
Gram–Schmidt size reduction; every window including truncated tails enumerated with exact rational re-checks; pure-rational
enumeration cross-checked on 3 bases; lattice identity by determinant, membership and HNF): all pass. Corrections:
(a) the threshold depends on the baseline — best ÷ restart median ≥ 0.871 (min over 176 lattices; median 0.909), but best ÷ the
lattice's own standard BKZ output goes down to 0.839 (q-ary N = 60, β = 20); (b) for N = 2β the restart populations are
degenerate (few distinct BKZ fixed points, e.g. a median of 10 distinct values out of 1000 at N = 24, β = 12), so the log-normal
and saturation remarks partly reflect this; (c) the smallest adjacent ratio over the 180 stored best bases is 0.868 (still above
√3/2); (d) the change in ln det W is small but mostly positive (+0.05 to +0.12), not absent; (e) 180 (not 202) best bases are
stored; local search strictly improved on the best restart in 17 of 176 lattices.
