# A populated terminal shell with zero acceptance at dimension 647

**Theorem.** In the Part 39 model at $D=647$, put $h=\tau^2$ and choose any $h$ in $[1.02076213,1.02076215]$. Uniform sampling on this interval gives irrational squared height almost surely. The plant remains uniquely shortest with probability at least $1-0.00483352$. Conditional on any planting and height independent of the matrix, the terminal population exceeds 101% of the prescribed volume with probability at least $1-2\cdot10^{-79}$. Yet the last merge has zero eligible pairs for every matrix and planting. Even a separately supplied complete terminal shell has zero representations of the plant as a difference. Thus removing the empty-shell obstruction gives no running-time exponent for this schedule and height law.

## The scaled first moment for uniqueness

Write $w=(x,y)$, $p=(e,s)$, $P=\|p\|^2$, $q=3329$, $n=512$ and $r=D-513$. Squared length is $\|w\|^2+ht^2$ and covolume is $q^r\sqrt h$. Condition on $p,h$ with the retained matrix uniform. The competitor test is exactly
$$
\|w\|^2\le P+h(1-t^2).
$$
For $1\le h<2$ its integer cutoff at $t=0$ is $P+1$, at $|t|=1$ it is $P$, and at $|t|\ge2$ it is at most $P+1-t^2$. Thus the entire competitor set is contained in its unit-height counterpart, including ties. For one representative per competing signed pair, excluding zero and the marked pair, its exact mean is the sum of $q^{-r}$ for $y-ts\ne0\bmod q$ and of one for $w-tp=0\bmod q$. Other representatives have weight zero by the independent-row calculation. Set inclusion preserves the capped first-moment certificate pointwise. Averaging gives the stated Part 39 bound and likewise $1.423\cdot10^{-20}$ failure at 662. This argument also allows height selection from the plant alone. [Part 39](wall1_projected_reference.md)

## Last two shell spectra

Let $C=(4/3)e^{2/7}(q^r\Gamma(1+D/2))^{2/D}/\pi$. For squared-radius multiplier $f$, the closed shell has endpoints $fCh^{1/D}(1\pm D^{-2})^2$. The multiplier is one for the terminal shell and $49/36$ for its source. In each layer the horizontal squared norm $j$ must be an integer between the endpoints minus $ht^2$. Intersecting these layers with $x+Ay=t(e+As)\bmod q$ gives precisely the shell in the lattice. At 647 the complete ambient labels are as follows.

| Shell | $(|t|,j)$ |
|---|---|
| Source | $(9,2581),(30,1745)$ |
| Terminal | $(0,1957),(17,1662),(34,777)$ |

The following interval certificate checks both inclusion and exclusion uniformly, including the closed endpoints. The height interval was chosen by centering the $t=0$ terminal layer at the next integer above $C$.

```python
from math import factorial
from mpmath import iv
iv.dps = 50
I = iv.mpf
d = 647
h = I(['1.02076213', '1.02076215'])
g = I(factorial(648))*iv.sqrt(iv.pi)/(4**324*factorial(324))
C = 4*iv.exp(I(2)/7)/3*(3329**134*g)**(I(2)/d)/iv.pi
for f, expected in [(I(1), [(0,1957),(17,1662),(34,777)]),
                    (I(49)/36, [(9,2581),(30,1745)])]:
    c = f*C*h**(I(1)/d)
    lo, hi = (c*(1+sign*I(1)/d**2)**2 for sign in [-1,1])
    assert hi < 2700 and h*52**2 > hi
    actual = []
    for t in range(52):
        a, b = lo-h*t*t, hi-h*t*t
        for j in range(max(0,int(float(a.a))-1), int(float(b.b))+2):
            if j < a or j > b:
                continue
            assert a <= j and j <= b
            actual.append((t,j))
    assert actual == expected
```

Source height differences have absolute values in $\{0,18,21,39,60\}$. Only zero can enter the terminal shell. Equal signed heights force equal horizontal squared lengths by the table. The squared length of their horizontal difference is even by polarization, whereas the terminal zero-height label is 1957. This proves zero acceptance, so every terminal target has zero source representations. Furthermore terminal heights all belong to $17\mathbb Z$, excluding the height-one plant from both the terminal shell and its difference set. The second exclusion matters because the sieve seeks the plant by a final difference scan. Exact-tie exclusion for certain two-dimensional quotients does not address either representation count. [Tie analysis](wall1_ties.md) · [Sieve hypotheses](provable_sieving.md)

## S1 discrepancy from the first two tuple moments

Let $X$ count signed terminal points at $t=0$ alone, counting both signs. Put $T_m(j)=[z^j](\sum_{a\in\mathbb Z}z^{a^2})^m$. Then
$$
\mu=\mathbb E X=q^{-134}(T_{646}(1957)-T_{134}(1957)),\qquad
\operatorname{Var}X\le2\mu .
$$
Indeed $y=0$ forces $x=0\bmod q$, impossible at this length. For the remaining points each inclusion probability is $q^{-134}$. Two points with independent $y$ residues have independent checks. For dependent $y$ residues joint inclusion requires proportional full horizontal residues, by consistency of the checks. Every two-column minor of their two full rows has absolute value at most 1957 by the area bound, strictly below $q$. Modular proportionality then implies rational proportionality, hence equality up to sign at this fixed norm. Only the point and its negative can contribute positive covariance per point. These are the first two instances of the planted tuple identity; the last-merge support proof already annihilates every marked representation term, including order three. [Planted tuple formula](planted_qary_sieve.md)

The target volume divided by covolume is
$$
V=((4/3)e^{2/7})^{647/2}\big((1+647^{-2})^{647}-(1-647^{-2})^{647}\big).
$$
Here $1.385\cdot10^{79}<\mu<1.387\cdot10^{79}$ and $1.119\cdot10^{78}<V<1.121\cdot10^{78}$. Chebyshev gives $\Pr[X\le1.01V]\le2\mu/(\mu-1.01V)^2<2\cdot10^{-79}$. For reproducibility the following exact coefficient recurrence also checks the CBD anti-concentration bound below. It follows by equating coefficients in $F(F^m)'=mF'F^m$.

```python
def coefficients(F, m, K):
    a = [F[0]**m]
    for k in range(1,K+1):
        a.append(sum(((m+1)*j-k)*v*a[k-j] for j,v in F.items()
                     if 0 < j <= k)//(k*F[0]))
    return a

F = {i*i: 2 for i in range(1,45)}
F[0] = 1
M = coefficients(F,646,1957)[-1]-coefficients(F,134,1957)[-1]
assert 1385*10**76*3329**134 < M < 1387*10**76*3329**134
V = (4*iv.exp(I(2)/7)/3)**(I(d)/2)*((1+I(1)/d**2)**d-(1-I(1)/d**2)**d)
assert 1119*10**75 < V and V < 1121*10**75
a = coefficients({0:20,1:30,4:12,9:2},646,9*646)
assert 1000000*max(a) < 8109*64**646
```

## Other height laws and the remaining exponent

At 647 **any** positive height law independent of the plant puts the plant in the terminal shell with probability below $0.008109$. In fact membership requires $h\le C(1+D^{-2})^2 h^{1/D}$, hence $h<2100$ (use $C<1957$). The squared interval width $4Ch^{1/D}/D^2$ is then below $0.02$. For each fixed $h$ at most one integer $P$ works. Its largest atom is bounded by the displayed coefficient test since each squared CBD(3) coordinate has generating polynomial $(20+30z+12z^4+2z^9)/64$. Averaging proves the bound. It concerns direct membership only. A plant-dependent height could target a label, but membership alone supplies no difference representation.

For block scalings with squared factors $a,b,h>0$, the shell test becomes $a i+b j+ht^2$ between the same unit-height endpoints multiplied by $(a^r b^n h)^{1/D}$, with $i=\|x\|^2,j=\|y\|^2$. Each ambient label has multiplicity $T_r(i)T_n(j)$. For fixed factors independent of the matrix given the plant, the exact lattice moments still weight each tuple by its modular consistency and rank as in Theorem 2 of the planted tuple note. An orthogonal rotation preserves every distance. Independent diagonal factors can change the spectra, but for other choices we have no simultaneous population, lens-degree and marked coverage estimates. Gaussian smoothing would require a quantitative transfer back to these hard indicators or a proof for a different sampling rule. A centered Gaussian mass upper bound supplies no lower bound on eligible centers. [Reverse Minkowski analysis](reverse_minkowski_blocks.md)

No positive success guarantee or time exponent follows for the prescribed sieve on the interval proved above. The broader height and diagonal families remain open for difference recovery. Even proving terminal coverage for another metric would leave earlier stages and pair-search work to certify. The Haar exponent $\tfrac12\log_2(3/2)$ therefore remains unproved for this ensemble. As a separate baseline the original unit-height lattice admits the randomized worst-case $2^{D+o(D)}$ exact-SVP time and space bound; this is an asymptotic algorithmic bound without a finite runtime estimate at 647. [ADRS](https://arxiv.org/abs/1412.7994)
