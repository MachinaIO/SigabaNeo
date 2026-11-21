# The terminal minimum after one exact forward pass

Across 10,240 sampled passes, the first percentile of the **retained** minimum at fixed eight graph columns and modulus 17 fell from 1.139 GH at width 4 to 0.926 at width 10, then stayed between 0.930 and 0.940 through width 20. The final **window** had a substantially lower first percentile at every setting. The data support looking for a short *pair* at the last selection. A short final selection alone was common, and loss of subgroup rank had very different base rates across the grid.

There is also a limit in which the proposed convergence to one is mathematically impossible. With the number of graph columns and the modulus fixed, the retained ratio converges in probability to **zero** as the width tends to infinity. The coordinate-prefix argument below proves this independently of the experiment. The regime where the number of graph columns grows with the width remains open, including the width-506 parameters of Parts 114 and 117.

## Experiment and observables

Let $d=b-1$, $V_k$ be unit ball volume, and $G_k=V_k^{-1/k}$. At graph append $t$, record $X_t=\lambda_1(W_t)/(G_b\det(W_t)^{1/b})$. After freezing the signed lexicographically least shortest vector and projecting, record $Y_t=\lambda_1(L_t)/(G_d\det(L_t)^{1/d})$ at the first and last append. The terminal observables are $X_n,Y_n$. All ratios use physical Euclidean volume in the lattice's own span.

Take $m=20$ for every row. For any $m\ge b$ the horizontal prefix freezes the earliest $m-d$ axes, leaving exactly $qI_d$. The deleted rows of $A$ never enter an ambient comparison because those coordinates are identically zero. Sampling only the remaining $d$ residues independently per append gives the same law as sampling the full matrix. There is one pass per seed, with no preprocessing of unread columns. See [Part 108](wall1_first_tour.md).

With row basis $B$ for the retained lattice, the rows of $CB/q$ represent the marked horizontal generators modulo the lattice. Initially $C=I_d$. A fresh row $a$ gives displacement $((aC)\bmod q)B/q$. If $T$ completes the selected coefficient row to a unimodular basis, the new mark is obtained from $[C\;0]T^{-1}$ by dropping the first column and reducing modulo $q$. This keeps the exact inherited subgroup even when it loses rank. Ambient coordinates of projected rows are rational ratios of integers. fpylll supplies an integer unimodular LLL transformation for speed. A closed-ball rational Gram enumeration compares every candidate that could improve or tie the incumbent, using integer square roots for the endpoints. Floating point enters the reported ratios and the basis diagnostic. The checks in the driver verify the selected norm, completion and terminal determinant identity on every trajectory. On three small bases, including a signed coordinate tie and a sheared cubic basis, the selected ambient vector also matched a separate finite-box search.

## Empirical distributions

Each entry gives nearest-rank empirical percentiles. The 1% estimate is the 11th observation out of 1,024. Counts in the last column use the Part 114 threshold.

| b, n, q | passes | retained Y (1/5/50/95%) | window X (1/5/50/95%) | Y < .954 |
| --- | --- | --- | --- | --- |
| 4, 8, 17 | 1024 | 1.139 / 1.280 / 1.500 / 1.661 | 0.857 / 0.942 / 1.257 / 1.475 | 0 |
| 6, 8, 17 | 1024 | 1.011 / 1.100 / 1.301 / 1.450 | 0.727 / 0.838 / 1.139 / 1.341 | 3 |
| 6, 8, 31 | 1024 | 0.989 / 1.082 / 1.298 / 1.451 | 0.667 / 0.808 / 1.124 / 1.340 | 3 |
| 6, 8, 101 | 1024 | 0.919 / 1.029 / 1.267 / 1.429 | 0.622 / 0.772 / 1.097 / 1.326 | 23 |
| 6, 16, 17 | 1024 | 1.227 / 1.284 / 1.411 / 1.507 | 1.072 / 1.127 / 1.306 / 1.426 | 0 |
| 8, 8, 17 | 1024 | 0.981 / 1.048 / 1.218 / 1.339 | 0.718 / 0.846 / 1.101 / 1.257 | 3 |
| 10, 8, 17 | 1024 | 0.926 / 1.030 / 1.163 / 1.271 | 0.725 / 0.852 / 1.072 / 1.204 | 13 |
| 12, 8, 17 | 1024 | 0.930 / 0.992 / 1.122 / 1.222 | 0.788 / 0.869 / 1.047 / 1.171 | 23 |
| 16, 8, 17 | 1024 | 0.940 / 0.984 / 1.091 / 1.160 | 0.821 / 0.899 / 1.036 / 1.126 | 21 |
| 20, 8, 17 | 1024 | 0.935 / 0.985 / 1.068 / 1.128 | 0.859 / 0.916 / 1.029 / 1.100 | 21 |

**Width, time and modulus.** At widths 10, 12, 16 and 20, intervals for the population first percentile of $Y_n$ from order statistics 4 and 18 are respectively [0.908, 0.971], [0.914, 0.941], [0.901, 0.951] and [0.916, 0.952] (rounded). Under independent sampling their pointwise coverage is at least 97.4% by the binomial count at probability 0.01. This sweep resolves neither a positive rate of approach to one nor a monotone increase. At width 6, extending the pass from 8 to 16 appends at modulus 17 raised the retained first percentile from 1.011 to 1.227. Keeping eight appends and raising the modulus from 17 to 101 lowered it to 0.919. A width-only extrapolation would discard both effects. Zero hits in 1,024 trials gives a one-sided 95% binomial upper endpoint of about 0.00292.

## Which histories produced low terminal ratios?

Each cell is **low outcomes within the event / total occurrences of the event**, with low meaning $Y_n<0.954$. Deficiency means $\operatorname{rank}_{\mathbb F_q} C<d$ immediately before the final draw. Height zero means the selected vector in the final window was inherited. For a near-cubic diagnostic we use the longest row of the enumeration's LLL basis divided by $\det(W_n)^{1/b}$. This spread equals one only for an orthogonal equal-length basis by Hadamard. The cutoff 1.15 is exploratory and basis dependent. A large spread cannot exclude an alternative, more nearly cubic basis.

| b, n, q | previous X < 1 | final X < 1 | deficient H | height zero | LLL spread ≤ 1.15 |
| --- | --- | --- | --- | --- | --- |
| 4, 8, 17 | 0/155 | 0/108 | 0/170 | 0/45 | 0/94 |
| 6, 8, 17 | 3/255 | 3/207 | 0/208 | 1/87 | 0/3 |
| 6, 8, 31 | 2/264 | 3/254 | 0/152 | 0/72 | 0/4 |
| 6, 8, 101 | 14/312 | 22/319 | 0/94 | 1/32 | 0/4 |
| 6, 16, 17 | 0/3 | 0/1 | 0/835 | 0/367 | 0/14 |
| 8, 8, 17 | 1/294 | 3/223 | 0/189 | 0/77 | 0/0 |
| 10, 8, 17 | 2/289 | 12/275 | 1/189 | 0/65 | 0/0 |
| 12, 8, 17 | 8/349 | 23/317 | 1/170 | 0/59 | 0/0 |
| 16, 8, 17 | 8/335 | 19/342 | 12/462 | 0/58 | 0/0 |
| 20, 8, 17 | 1/337 | 19/339 | 20/1010 | 0/56 | 0/0 |

At $(6,8,101)$, a sub-GH last selection gave 22 low outcomes in 319 draws, versus one in 705 for the complement. The preceding selection was sub-GH in only 14 of the 23 failures. All 23 had full pre-draw mark. At $(20,8,17)$ the mark was deficient in 1,010 of 1,024 runs, including 20 of the 21 failures. Charging every deficient history would spend almost the entire probability budget. The near-cubic test was too rare in the wider windows to distinguish risk. A horizontal final selection accounted for only two failures across the grid. A nonhorizontal selection can still form a short plane with an inherited vector.

## Dependence and comparison to the Haar one-step law

The first three columns below correlate $X_n$ with $X_{n-j}$ across independent matrices at fixed times. The fourth averages the $n-1$ fixed-time consecutive Pearson correlations, giving each time equal weight. This avoids an artificial correlation from pooling different time means. The last two columns count low quotient ratios after one graph append and after the last (each denominator is 1,024).

| b, n, q | lag 1 | lag 2 | lag 4 | mean consecutive | first Y < .925 | last Y < .925 |
| --- | --- | --- | --- | --- | --- | --- |
| 4, 8, 17 | 0.114 | 0.128 | 0.080 | 0.024 | 51 | 0 |
| 6, 8, 17 | 0.085 | 0.040 | 0.010 | 0.028 | 53 | 2 |
| 6, 8, 31 | 0.020 | 0.020 | 0.034 | 0.009 | 40 | 2 |
| 6, 8, 101 | 0.011 | 0.020 | 0.016 | 0.005 | 55 | 13 |
| 6, 16, 17 | 0.203 | 0.116 | 0.128 | 0.084 | 29 | 0 |
| 8, 8, 17 | 0.046 | 0.015 | 0.067 | 0.019 | 38 | 2 |
| 10, 8, 17 | 0.050 | 0.047 | -0.002 | 0.026 | 16 | 8 |
| 12, 8, 17 | 0.027 | -0.038 | 0.094 | 0.013 | 19 | 7 |
| 16, 8, 17 | 0.016 | -0.030 | 0.038 | 0.028 | 31 | 7 |
| 20, 8, 17 | 0.042 | 0.021 | -0.019 | 0.040 | 153 | 6 |

Most late correlations at width 6 and eight appends are small (a rough null standard error is 0.031). At 16 appends the terminal lag-one correlation is 0.203 and lag four is still 0.128. Weak linear dependence for this scalar observable gives no mixing-time certificate for its tails or for the marked lattice. The process starts at a cube and runs for finite, nonstationary time.

For a **Haar input window**, [Part 105](wall1_selection_law.md) proves the one-step upper bound
$$
P(Y< c)\le \frac{V_b}{4\zeta(b)\zeta(d)V_d}(2c^2/\sqrt3)^d.
$$
At $c=.925$ its values for widths 4, 6, 8, 10, 12, 16 and 20 are respectively .2183, .2190, .1949, .1728, .1550, .1287 and .1100 (rounded). These are bounds, not point predictions. At width 20 the **first** graph quotient fell below .925 in 153/1,024 runs (14.9%), above even the Haar upper bound. By the final graph quotient the count was 6/1,024. Thus a small terminal hit rate can coexist with a first graph transition very unlike the Haar step. The much smaller numerical bounds quoted for Haar widths 406 and 506 use those dimensions explicitly.

## A fixed-time width limit (proof)

Fix prime $q$, positive $n$, and take $m\ge b>n+1$. Follow the forced coordinate deletions of [Part 117](wall1_idea_round2.md), **including one extra inspection of the terminal retained lattice**. At forced window $t$ the graph has $b-t$ horizontal rows and $t$ graph coordinates. After the last deletion the quotient graph has $d-n$ horizontal rows and $n$ graph coordinates. Each of these matrices is marginally uniform because the chosen row labels are deterministic.

Every integer vector of length at most $q$ has support at most $q^2$. In at most $b$ dimensions their number is at most $N_b=\sum_{i=0}^{\min(b,q^2)}\binom bi(2q)^i$. A label with nonzero graph residue satisfies the graph equations with probability $q^{-h}$ for $h$ horizontal rows. With zero graph residue all coordinates of a member are divisible by $q$, so only the origin and signed $q$-axes can occur in that ball. Consequently, outside an event of probability at most $(n+1)N_b q^{-(d-n)}$, every forced selection takes the negative earliest horizontal axis by lexicographic order and the terminal minimum is exactly $q$. This union bound needs no conditional independence. For fixed $q,n$ its polynomial factor is dominated by the exponential. The terminal graph has determinant $q^{d-n}$, hence on agreement
$$
Y_n=V_d^{1/d}q^{n/d}\sim\sqrt{2\pi e/d}.
$$
This proves the limit and its typical rate in that regime. The bound can be vacuous at the simulated widths. It gives no quantitative prediction for $n$ comparable to $b$.

## A sufficient condition worth trying at proportional width

Let $D=\det L_{n-1}$, $s=\lambda_1(W_n)$, $R(s)=cG_d(D/s)^{1/d}$ and $\alpha=\sqrt3/2$. Reduction of a lift modulo the selected vector gives $\lambda_1(L_n)\ge\alpha s$, hence failure requires
$$
X_n < K_b(c)=(cG_d/\alpha)^{d/b}/G_b .
$$
For $c=.954$, $K_b$ ranges from about 1.120 at width 4 to about 1.064 at width 20. The strict gate explains why a last selection slightly above GH can still fail. Paying for the whole gate discards the rarer second-vector requirement.

More precisely a bad quotient supplies a primitive short quotient line whose preimage in the window is a saturated plane of area $<sR(s)$ containing the lex-selected line. Conversely such a plane certifies failure by projecting its second basis vector. This suggests a **conditional first moment on planes**, with two independently checkable budgets. Choose a measurable good set of penultimate histories and charge its complement by $\delta$. Bin $s$ up to the gate. On a bin $[l,u]$, count saturated planes of area $<uR(u)$ with internal minimum in the bin, discarding planes if a strictly shorter vector outside is certified. The area cap follows since $sR(s)$ is increasing for $d>1$. The selected plane passes all these filters. If the expected sum of surviving plane counts on good histories is at most $\epsilon$, then $P(Y_n<c)\le\delta+\epsilon$ by Markov. No stationarity assumption enters. At width 506 the restart in Part 117 allows a suffix budget $\delta+\epsilon\le .00977696$.

To estimate this moment, separate horizontal planes, which are already measurable given the history, from planes of positive height subgroup $j\mathbb Z$. For the latter take the primitive horizontal generator $x$ up to sign; the second generator at height $j$ has horizontal component in $jU+L$ modulo $\mathbb Zx$. The area cap requires $j|x|<uR(u)$ and a disk for the projection perpendicular to $x$ of squared radius $(uR(u)/|x|)^2-j^2$. Average the slice count over the actual finite image $jH$, keeping multiplicity modulo $\mathbb Zx$. Further discard a candidate if even one enumerated outside vector beats its internal minimum. Defining a good set by bounds on these short horizontal plane and projected disk counts, then bounding their *history-averaged* sizes after the coordinate restart, is a concrete proof target. The data favor retaining the second-vector and outside-competitor tests; neither rank deficiency nor a previous short selection reliably identifies exceptional histories. The required small plane moment and good-set probability at proportional width remain conjectural. [Part 114](wall1_idea_drift.md) · [Part 117](wall1_idea_round2.md)

## Reproduction

Save the following block as `pass.py` and use a SageMath Python environment with fpylll and Singular on its executable path. Run `python pass.py 1024 > narrow.jsonl` and `python pass.py 1024 wide > wide.jsonl`. Each row contains the parameters, sequence of window ratios, terminal quotient ratio, incoming mark rank, signed last height, first quotient ratio, and last-window LLL spread. Changing the LLL implementation may affect the spread. Quantiles use order statistic $\lceil Np\rceil$; event counts use the displayed strict thresholds.

```python
from sage.all import ZZ, QQ, GF, matrix, vector, identity_matrix, zero_matrix
from fpylll import IntegerMatrix, LLL
from math import sqrt, gamma, pi, isqrt
from random import Random
from multiprocessing import Pool
import json, sys

def shortest(B):
    # Reduce integer numerator rows, retaining the exact basis change.
    den = B.denominator()
    A = (den*B).change_ring(ZZ)
    f = IntegerMatrix.from_matrix(A.rows())
    u = IntegerMatrix.identity(A.nrows())
    LLL.reduction(f,U=u)
    k = A.nrows()
    U = matrix(ZZ,k,k,lambda i,j:u[i,j])
    A = U*A
    gram = A*A.transpose()
    D = gram.change_ring(QQ)
    mu = identity_matrix(QQ,k)
    diag = []
    for i in range(k):
        diag.append(D[i,i])
        for j in range(i+1,k):
            mu[j,i] = D[j,i]/diag[i]
        for j in range(i+1,k):
            for h in range(i+1,j+1):
                D[j,h] -= mu[j,i]*D[h,i]
    best = gram[0,0]
    winner = A[0]
    coeff = identity_matrix(ZZ,k)[0]
    z = [0]*k
    def walk(i,cost):
        nonlocal best,winner,coeff
        if i < 0:
            if cost:
                a = vector(ZZ,z)
                v = a*A
                if (cost,tuple(v)) < (best,tuple(winner)):
                    best,winner,coeff = cost,v,a
            return
        shift = sum((mu[j,i]*z[j] for j in range(i+1,k)),QQ(0))
        p,h = shift.numerator(),shift.denominator()
        radius = isqrt(int(((best-cost)*h*h/diag[i]).floor()))
        for x in range(int(-((p+radius)//h)),int((radius-p)//h)+1):
            new = cost+diag[i]*(x+shift)**2
            if new <= best:
                z[i]=x
                walk(i-1,new)
    walk(k-1,QQ(0))
    gdet = gram.det()
    # Longest row of this LLL basis in geometric-mean units.
    spread = float(max(gram.diagonal())**k / QQ(gdet))**(0.5/k)
    return coeff*U, QQ(best)/den**2, gdet/QQ(den)**(2*k), spread

def ratio(s2,det2,k):
    return sqrt(float(s2))*gamma(1+k/2)**(-1/k)*sqrt(pi)/float(det2)**(0.5/k)

def trial(args):
    b,n,q,seed=args
    rng=Random(seed)
    d=b-1
    B=q*identity_matrix(QQ,d)
    C=identity_matrix(ZZ,d)
    xs=[]
    for t in range(n):
        # Deleted leading coordinates contribute identically zero.
        raw=vector(ZZ,[rng.randrange(q) for _ in range(d)])
        a=vector(QQ,[x%q for x in raw*C])/q
        W=B.stack(matrix([a*B])).augment(matrix(QQ,d+1,1,[0]*d+[1]))
        c,s2,det2,spread=shortest(W)
        xs.append(ratio(s2,det2,b))
        v=c*W
        assert v*v==s2
        # H*c^T=e1, hence inverse transpose starts with row c.
        _,H=matrix(c).transpose().hermite_form(transformation=True,include_zero_rows=True)
        T=H.inverse().transpose().change_ring(ZZ)
        assert T[0]==c
        rest=T[1:]*W
        B=rest-(rest*matrix(v).transpose())*matrix(v)/s2
        if t==n-1:
            rank=C.change_ring(GF(q)).rank()
        C=(C.augment(zero_matrix(ZZ,d,1))*H.transpose())[:,1:]%q
        if t==0:
            _,l0,D0,_=shortest(B)
            first=ratio(l0,D0,d)
    _,l2,outdet,_=shortest(B)
    assert outdet*s2==det2
    return [b,n,q,xs,ratio(l2,outdet,d),int(rank),int(c[-1]),first,spread]

if __name__=='__main__':
    grid=[(4,8,17),(6,8,17),(8,8,17),(6,16,17),(6,8,31),(6,8,101)]
    if len(sys.argv)>2: grid=[(10,8,17),(12,8,17),(16,8,17),(20,8,17)]
    jobs=[(*p,10000000*i+j+(90000000 if len(sys.argv)>2 else 0)) for j in range(int(sys.argv[1])) for i,p in enumerate(grid)]
    with Pool(12) as pool:
        for row in pool.imap(trial,jobs,chunksize=4):
            print(json.dumps(row),flush=True)
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

* **Reproduction.** All 4,096 reruns of the published seeds match exactly, and all displayed table rows reproduce from the
  10,240 saved trajectories.
* **Exact SVP.** The search is exact, including ties. It was checked against exhaustive searches on 36 small bases.
* **Width-limit theorem.** Correct for prime q: the exceptional probability is ≤ (n+1)·N_b·q^{−(d−n)} = o(1).
* **Plane condition.** It is sufficient.

Corrections:

* When multiplication by j has a kernel, a filtered competitor count must keep U or average over its fiber given jU. Averaging
  over jH is valid only for the raw projected count.
* The tables measure scalar gates. They do not measure how many planes the outside-competitor test removes.

The empirical percentiles are labeled as evidence, not proofs.
