# Raw graph witnesses for early long winners

**The conditional fourth-moment hypothesis is sufficient on draws 54–405 alone.** A vector in the raw graph with nonzero newest coordinate survives all preceding projections. Counting such vectors over the original independent columns gives an unconditional tail bound in physical units. Hölder's inequality converts the marginal bounds into a bound for the product of the first 53 lengths, allowing arbitrary dependence among them. The same argument shortens both conditional tail tests.

| Sufficient remaining hypothesis, given the incoming history | Required draws | Upper probability of a crossing on 396–406 |
|---|---:|---:|
| (A) Tails at 1.05 and 1.15 bounded by 0.60 and 0.15 | 67–405 | $2.3750\cdot10^{-11}$ |
| (B) Normalized fourth moment at most 1.7860 | 54–405 | $2.4681\cdot10^{-11}$ |
| (C) Tail at 1.10 bounded by 0.126 | 49–380 | $2.0204\cdot10^{-11}$ |

Each row separately fits the $2.72513\cdot10^{-11}$ allowance. **None proves the remaining hypothesis.** A second result uses only old vectors. Outside a set of original histories of mass less than $2.417\cdot10^{-11}$, on every draw 11–19 the horizontal lattice already certifies (B) for every possible next mark. The table uses the unconditional marginal argument directly and incurs no separate exceptional-set charge. The results are paper proofs with interval verification. [First-tour law](wall1_first_tour.md) · [Part 216](wall1_small_g_frequency.md) · [Part 217](wall1_long_winner_ceiling.md) · [R91](wall1_long_winner_routes.md)

## A count before shortest-vector selection

Let $q=3329$, $n=506$, $d=505$, $V_j$ be the unit-ball volume, and $N=505+i$ at draw $i$. The raw graph is $L=\{(x,y)\in\mathbb Z^{400}\times\mathbb Z^{N-400}:x=Ay\bmod q\}$ with independent uniform entries of $A$. Write $G_N=(q^{400}/V_N)^{1/N}$ for its raw Gaussian-heuristic length. This differs from the incoming projected length $g_i$. All probabilities in this section integrate over the original graph law.

**Raw ball lemma.** For $506\le N\le572$ and $1690\le R\le q$, there is a deterministic family of centered integer vectors in the radius-$R$ ball, each with nonzero last coordinate, representing distinct projective points modulo $q$. If $Z$ counts its members belonging to $L$, then
\[
 \mu=\mathbb E Z\ \ge\ \tfrac14 (R/G_N)^N,\qquad
 \operatorname{Var} Z\le\mu.                                             \tag{1}
\]
For a single representative the incidence probability is $q^{-400}$ because $y\ne0\bmod q$. If two input residues are independent, the corresponding events are independent, row by row. If their inputs are proportional, distinct full projective points require incompatible outputs and the covariance is negative. It remains to prove the size of the family. The following estimates use physical Euclidean balls throughout.

1. Count centered vectors in $B_R$. Integrate over $B_{R-c}$, $c=1.3$, restricted to coordinates of absolute value at most 1664. Independently round each coordinate to the two adjacent integers with its original mean. Each integer point receives total weight at most one, since the product of the linear interpolation kernels integrates to one over all space. With rounding error $e$, one has $\|e\|^2\le N$ and $\operatorname{Var}\langle z,e\rangle\le\|z\|^2/4$. Put $k=c-N/[2(1690-c)]>0$. For $\|z\|\le R-c$, the event $\langle z,e\rangle\le k\|z\|$ implies $\|z+e\|\le R$. Its probability is at least $4k^2/(1+4k^2)$ by Cantelli, including the trivial case $z=0$. The fraction cut off the continuous ball by the coordinate restriction is at most
\[
 b_N=2N(V_{N-1}/V_N)(1-(1664/q)^2)^{(N-1)/2}.
\]
This follows by integrating each cap over an interval of length at most the radius. Consequently the centered count divided by $V_NR^N$ is at least $(1-c/1690)^N(1-b_N)4k^2/(1+4k^2)$.
2. Discard vectors with last coordinate zero. Their count divided by $V_NR^N$ is at most $2(V_{N-1}/V_N)(1+(N-1)/(4\cdot1690^2))^{(N-1)/2}/1690$. Indeed the inward half of each centered unit cube in dimension $N-1$ lies in the ball of squared radius $R^2+(N-1)/4$. [Part 172, half-cube bound](wall1_transference.md)
3. Discard vectors participating in an alias $z'\equiv uz\bmod q$ in the ball with $u\notin\{0,1,-1\}$. For fixed $u$, each coordinate pair belongs to the plane lattice $J_u=\{(v,w):w\equiv uv\bmod q\}$ of determinant $q$. Its minimum $b$ satisfies $\sqrt5\le b\le 2\sqrt{q/\pi}$. Enumeration of squared lengths below five gives the lower bound and the planar Minkowski disk bound gives the upper bound. A primitive shortest vector gives GS spacings $b,q/b$. For a shifted one-dimensional Gaussian with spacing $l$, the sum is at most $1+\sqrt{\pi/\beta}/l$, by integrating the level-set count of a shifted interval. Sum successively in the two basis coordinates with $\beta=N/(4R^2)$ and $T=2\sqrt\pi R/\sqrt N$. Including both ball weights, an upper bound on the discarded fraction is
\[
  \frac{q}{V_N}
  \left[\frac{e^{1/2}}{R}(1+T/b)(1+Tb/q)\right]^N.                    \tag{2}
\]
Here the count of ordered pairs majorizes the number of discarded vectors, including both signs. The bracket is convex in $R$ at fixed $b$ (a constant plus positive multiples of $R$ and $1/R$), and convex in $b$ at fixed $R$. The four endpoint pairs suffice. Centered representatives have unique lifts coordinatewise, so the remaining ambiguity is exactly the two signs. Retain one sign. Subtracting both losses in steps 2–3 from step 1 gives more than $1/2$ of $V_NR^N$ before dividing by two, throughout the stated range. This proves (1).

This calculation uses the entire raw graph law. Conditional on a selected prefix, a single new mark generally gives different pair covariances. All vectors counted with last coordinate nonzero have nonzero projection off the previously frozen space, which has zero in that coordinate. Projection contracts length, so $s_i>R$ implies $Z=0$. Cantelli and (1) give the marginal inequality
\[
  \Pr(s_i>R)\le (1+\mu)^{-1}\le 4(G_N/R)^N .
                                                                    \tag{3}
\]
Multiple candidate vectors sharing one *fresh* mark cause no loss in this implication. The randomness averaged in (1) includes the previous columns too. [Part 219, conditional collision problem](wall1_covering_ceiling.md)

## Incorporating marginal bounds into the determinant recursion

Use $x_i=\log g_i$, $a=505/506$, $X=\log34.807$, $Q=\log q$, $h=\sqrt{56.2142}\,V_n^{1/n}$, and $Y_i=\log(s_i/g_i)$. The two exact recursions are
\[
 x_{i+1}=x_i-\log(s_i)/n=ax_i-Y_i/n,\qquad x_1=(400Q-\log V_n)/n.
\]
Use the first expression on the initial segment and the second on the suffix. On a crossing, stop the normalized increments after the first crossing and use zero thereafter. The comparison stays below $X$ since $aX<X$. A predictable exit from the tested gates can also stop the comparison when bounding the joint event of a surviving crossing. Future gates can be imposed on the resulting event. For $m<395$, $\lambda>0$, $v=\lambda a^{405-m}$, $p=mv$, $w_i=a^{405-i}$, the crossing probability is at most
\[
 e^{-\lambda n(a^{405-m}x_1-X)}
 \prod_{i=1}^{m} (\mathbb E s_i^p)^{1/m}
 \prod_{i=m+1}^{405} K_i(\lambda w_i).                               \tag{4}
\]
Indeed, first condition on the history through $m$ and iterate the suffix conditional bounds $K_i(u)\ge1$ for $e^{uY_i}$. The prefix factor remaining is $\mathbb E\prod s_i^v$, bounded by the displayed product by Hölder. Prefix paths can be included with their full marginal weight even when only gated crossings count.

For all prefix indices used in the table, $G_N>1690$. Put $T_N=4^{1/N}G_N$. Using the trivial tail up to $T_N$, (3) from $T_N$ to $q$, and the period cap $s_i\le q$ beyond, integration gives, for $0<p<N$,
\[
 \mathbb E s_i^p\le\min\{q^p,\ T_N^p N/(N-p)\}.                     \tag{5}
\]
Extending the power-tail integral to infinity is an upper estimate. If $T_N\ge q$ the first branch suffices.

* For (A) take $m=66,\lambda=5.7$ and $K_i(u)=.40(1.05)^u+.45(1.15)^u+.15h^u$.
* For (B) take $m=53,\lambda=4$ and $K_i(4w_i)=1.7860^{w_i}$ by concavity.
* For (C) take $m=48$, $\lambda=1.286/\log(h/1.10)$ and $K_i(u)=.874(1.10)^u+.126h^u$ through 380, followed by $h^u$ on the last 25 draws.

These choices give the three table entries. With one more prefix draw in each row, the same majorants and exponents give, respectively, more than $4.23\cdot10^{-11}$, $3.14\cdot10^{-11}$ and $2.77\cdot10^{-11}$. These endpoints concern this certificate. The exact conditional law on each later draw is still the marked kernel: on $\lambda_1(M)>r$, the strict tail is one minus the fraction of marks covered by the union of the closed balls at all positive heights. The zero-height and period tests apply pathwise. [Part 108](wall1_first_tour.md) · [Exact common-mark formula](wall1_small_g_frequency.md)

## A simultaneous certificate from the retained lattice

Put $t=1.7860^{1/4}\in(1.15603,1.15604)$. Form a comparison path $g_i^*$ taking the largest allowed length $\min(q,hg_i^*)$, with the extra cap $t g_i^*$ on 11–19. For each such $i$, apply (1) to the **incoming raw graph** in dimension $N=504+i$ at $R_i=tg_i^*$. The witness family is fixed before the graph is drawn. On the event that the raw graph in dimension 523 has minimum greater than 2500, every earlier raw prefix has that minimum floor by zero extension. The exit probability is at most $V_{523}(2500+\sqrt{523}/2)^{523}q^{-400}<1.08\cdot10^{-21}$. Nonzero vectors of this length have nonzero input residues whenever they belong to the graph, and the outward cube gives the count.

If all the counted witnesses in the graph lie in its frozen $(i-1)$-space, disjoint open balls of radius 1250 there, centered at zero and both signs of each witness, give
\[
 Z\le L_i=\big[(1+2R_i/2500)^{i-1}-1\big]/2 .
\]
Consequently, with $u_i=(R_i/G_N)^N/4>L_i$, the joint probability of the raw minimum gate and absence of a surviving witness is at most $u_i/(u_i-L_i)^2$. This follows by applying the unconditional variance bound to $Z\le L_i$ and using the monotonicity of $u/(u-L_i)^2$ above $L_i$. No conditioning on the future minimum gate enters the moment calculation.

Summing these nine bounds and the single exit gives less than **$2.417\cdot10^{-11}$** (through 18 alone, less than $1.939\cdot10^{-12}$ with the same exit). On the complement, projection gives $\lambda_1(M_i)\le R_i$ at every tested entry. Inductively $g_i\ge g_i^*$, since both scalar update branches are increasing and the extra cap holds at each tested step. Thus, at those entries, $s_i/g_i\le t$ for **every** new mark. Equivalently the probability that any of the nine incoming histories fails the pointwise horizontal certificate is bounded by the same joint exception. This is stronger on those histories than a conditional moment estimate. The draw-406 scalar floor on that event is in $(32.20596,32.20598)$.

At draw 20 the full count of all raw unoriented short vectors, even before discarding any aliases, has mean at most $V_{524}(R_{20}^2+524/4)^{262}/q^{400}<1.567\cdot10^{10}$ for $R_{20}=tg_{20}^*<q$. Even the variance majorant $\operatorname{Var}Z\le\mu$ with zero packing charge gives a Cantelli certificate $1/(1+\mu)>6.38\cdot10^{-11}$. This diagnoses the loss in trying to buy another pointwise draw with the entire crossing allowance. At draw 405, on the crossing corridor $g_i<35.0743$, the same raw-ball first moment at $t\cdot35.0743$ is below $10^{-707}$. Short projections of longer raw vectors would have to be accounted for there. [Part 219, corridors](wall1_covering_ceiling.md)

## Deterministic sublattices and the sign of feedback

For a specified incoming prefix let $F$ be its frozen space, $P$ its orthogonal complement projection and $M=PL$. For every rational extension $U\supset F$ of relative dimension $k\ge1$, the corresponding saturated horizontal section has squared covolume $q^{2(d_F-d_U)}p_U/p_F$, where $p_U=\det(U\cap\mathbb Z^N)^2$ and $d_U$ is the codimension of the syndrome image of that integer section. Thus an upper Hermite coefficient $c_k$ gives a deterministic test
\[
 \frac{s_i}{g_i}\le
 \min\left(\frac q{g_i},\ h,\ \min_U
 \frac{\sqrt{c_k}}{g_i}\left(q^{2(d_F-d_U)}p_U/p_F\right)^{1/(2k)}\right).
\]
With $c_1=1$, the inner minimum over *all* such sublattices equals $\lambda_1(M)/g_i$: the shortest primitive line attains it and Hermite bounds each section from above. This identifies precisely what optimizing over unknown section determinants requires. The frozen section itself projects to zero. For any proposed smaller rank, a sufficient input is an actual determinant at most $(tg_i/\sqrt{c_k})^k$. The dual gate in Part 172 gives a lower bound on section covolume, with the opposite inequality. [Part 212, section identity](wall1_integrality_bound.md) · [Part 172](wall1_transference.md)

For the entire horizontal lattice the known determinant is $D=V_n g_i^n$. With the published rank-505 log cap $H_{505}=1016.893214922$, the resulting normalized bound is $\exp((H_{505}+\log V_n+\log g_i)/505)$. It exceeds **1.37099** throughout the range $g_i>32.18553$, already above $h<1.36749$. The period and these two determinant-only tests certify zero whole additional draws on 11–405 via the existing incoming floors. A full-rank window cap would need squared coefficient at most $t^2V_n^{-2/n}<40.174$ to give (B) pointwise; the available coefficient is 56.2142. The exact supremum of the sublattice minimum over gated reachable histories is unknown. The nine-draw result above instead finds a short rank-one section with quantified probability. [Rank-505 and rank-506 certificates](wall1_hermite_caps.md)

Finally $D_{j+1}=D_1/\prod_{i=1}^j s_i$: the final **raw** determinant stays fixed, while the final **retained** determinant is random. At fixed later normalized increments increasing $Y_i$ by $\delta$ changes $x_{j+1}$ by $-a^{j-i}\delta/n$. A short winner raises the outgoing GH length. In the scalar relaxation one may take equality at every available cap, even imposing $s_i\le tg_i$ on 11–19. On every tested draw 11–405 the resulting normalized length exceeds one, so every upper bound on the probability of a subunit normalized length holds there; the path still crosses. This is an obstruction to using short-winner upper tails and conservation alone. It is not a counterexample from the marked lattice law.

## Reproduction

Run the embedded interval verifier from the repository root. Embedding it keeps the deliverable in one file.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_long_winner_handle.md | python -B -)
```

```python
from mpmath import iv

iv.dps = 70
I, log, exp, sqrt = iv.mpf, iv.ln, iv.exp, iv.sqrt
q, n, d = 3329, 506, 505
a, Q, X = I(d)/n, log(q), log(I('34.807'))
V = [I(1), I(2)]
for j in range(2, 910):
    V.append(2*iv.pi*V[j-2]/j)
x1 = (400*Q-log(V[n]))/n
h = sqrt(I('56.2142'))*exp(log(V[n])/n)
M = I('1.7860')
t = exp(log(M)/4)
budget = I('2.72513e-11')

def smaller(x, y):
    assert x < y or y < x
    return min(x, y)

# Deterministic family of projectively distinct raw ball witnesses.
lo, c = I(1690), I('1.3')
for N in range(506, 573):
    k = c-N/(2*(lo-c))
    assert k > 0
    cut = 2*N*V[N-1]/V[N]*(1-(I(1664)/q)**2)**(I(N-1)/2)
    centered = (1-c/lo)**N*(1-cut)*4*k*k/(1+4*k*k)
    hyperplane = (2*V[N-1]/(V[N]*lo)
                  *(1+(N-1)/(4*lo**2))**(I(N-1)/2))
    for R in (lo, I(q)):
        T = 2*sqrt(iv.pi)*R/sqrt(N)
        for b in (sqrt(5), 2*sqrt(q/iv.pi)):
            aliases = q*(exp(I(1)/2)*(1+T/b)*(1+T*b/q)/R)**N/V[N]
            assert centered-hyperplane-aliases > I(1)/2
    assert exp((400*Q-log(V[N]))/N) > lo

# Suffix product and Holder prefix moments, all in log units.
def crossing(kind, m):
    lam = {'A': I('5.7'), 'B': I(4), 'C': I('1.286')/log(h/I('1.10'))}[kind]
    power = a**(405-m)
    v, p = lam*power, m*lam*power
    value = -lam*n*(power*x1-X)
    for i in range(1, m+1):
        N = 505+i
        assert 0 < p < N
        logT = (400*Q-log(V[N])+log(4))/N
        value += smaller(v*Q, v*logT+log(N/(N-p))/m)
    for i in range(m+1, 406):
        w = a**(405-i)
        u = lam*w
        if kind == 'A':
            value += log(I('.40')*I('1.05')**u+I('.45')*I('1.15')**u
                         +I('.15')*h**u)
        elif kind == 'B':
            value += w*log(M)
        elif i <= 380:
            value += log(I('.874')*I('1.10')**u+I('.126')*h**u)
        else:
            value += u*log(h)
    return exp(value)

for kind, m, low, high, next_low in [
        ('A', 66, '2.3749e-11', '2.3750e-11', '4.23e-11'),
        ('B', 53, '2.4680e-11', '2.4681e-11', '3.14e-11'),
        ('C', 48, '2.0203e-11', '2.0204e-11', '2.77e-11')]:
    assert I(low) < crossing(kind, m) < I(high) < budget
    assert crossing(kind, m+1) > I(next_low) > budget

# Extra gate and rank-one certificate from the incoming graph.
raw_exit = V[523]*(2500+sqrt(523)/2)**523/q**400
assert raw_exit < I('1.08e-21')
exception = raw_exit
x, unrestricted = x1, x1
assert I('1.15603') < t < I('1.15604')
for i in range(1, 406):
    g = exp(x)
    s = smaller(I(q), h*g)
    if 11 <= i <= 19:
        N, f, R = 504+i, i-1, t*g
        assert lo < R < q
        mean = V[N]*R**N/(4*q**400)
        packing = ((1+2*R/2500)**f-1)/2
        assert mean > packing
        exception += mean/(mean-packing)**2
        s = smaller(s, R)
        if i == 18:
            assert exception < I('1.939e-12')
    if i == 20:
        R = t*g
        assert R < q
        upper = V[524]*(R**2+I(524)/4)**262/q**400
        assert upper < I('1.567e10') and 1/(1+upper) > I('6.38e-11')
    if i >= 11:
        assert s > g
        assert smaller(I(q)/exp(unrestricted), h) > t
    x -= log(s)/n
    unrestricted -= log(smaller(I(q), h*exp(unrestricted)))/n
assert exception < I('2.417e-11')
assert I('32.20596') < exp(x) < I('32.20598') < exp(X)
assert exp(unrestricted) > I('32.18553')
raw405 = V[909]*((t*I('35.0743'))**2+I(909)/4)**(I(909)/2)/q**400
assert raw405 < I('1e-707')
oldcap = exp((I('1016.893214922')+log(V[n])+log(I('32.18553')))/d)
assert oldcap > I('1.37099') > I('1.36749') > h
assert I('40.1739') < t**2*exp(-2*log(V[n])/n) < I('40.174')
print('Verified raw ball counts, all three suffix tests, and the nine-draw horizontal certificate.')
```

## Audit

**Confirmed for the original width-506 graph law.** The embedded interval verifier passed. An independent calculation using $\log V_N=(N/2)\log\pi-\log\Gamma(1+N/2)$ reproduced the following majorants for a crossing on draws 396–406. Each requires its stated conditional hypothesis on the relevant incoming histories.

| Hypothesis | Draws requiring it | Majorant, approximately |
|---|---:|---:|
| A | 67–405 | $2.37496543\cdot10^{-11}$ |
| B | 54–405 | $2.46808808\cdot10^{-11}$ |
| C | 49–380 | $2.02037536\cdot10^{-11}$ |

The rounding, hyperplane and alias estimates leave more than $V_NR^N/2$ centered vectors before identifying opposite signs. For distinct retained projective points, independent input residues give independent incidences under the raw matrix law, and proportional input residues give disjoint incidences. Thus $\operatorname{Var}Z\le\mathbb EZ$. The newest coordinate survives projection off every earlier frozen space, so one incidence suffices to bound the physical winner length. In (4), conditioning through draw $m$ handles the stopped suffix, and Hölder bounds the product of the first $m$ lengths under their original joint law. This permits arbitrary dependence among winners.

For draws 11–19 the count uses the incoming dimensions $515,\ldots,523$. On the dimension-523 minimum gate, zero and the two signs of each frozen witness are mutually separated by more than 2500. Hence absence of a witness surviving projection on this gate forces $Z\le L_i$, to which the unconditional variance estimate applies. The gate exit is charged once. Including that exit, the sum through draw 18 is approximately $1.93885177\cdot10^{-12}$, and draw 19 contributes another $2.22297606\cdot10^{-11}$. The total is below $2.417\cdot10^{-11}$. On the complement the increasing comparison update gives $g_i\ge g_i^*$, and a surviving horizontal vector gives $s_i\le t g_i$ for every next mark at each realized entry. This proves (B) there under the original transition law.

**Budget.** All nine draws lie inside the unconditional prefix of every table row. Equation (4) already includes the exceptional histories at their full probability, so each row uses only its displayed crossing bound against $2.72513\cdot10^{-11}$. A separate argument that discarded the exceptional histories would have to account for their contribution to the crossing. Charging the full rounded exception there would leave $3.0813\cdot10^{-12}$. The later conditional hypotheses remain open.
