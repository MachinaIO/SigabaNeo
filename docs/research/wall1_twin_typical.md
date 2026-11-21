# Actual block minima in the two-block twin test

The proposed unweighted first moment over primitive pairs diverges at both widths. Even imposing an exact shortest head in each of the two internal oracle windows, on the same basis, leaves the set of passing extensions exactly as in Part 90. The obstruction is the free choice of intermediate subspaces. The following 99% certificates therefore use distinct extensions. The probability is for each fixed width on the unimodular Haar ensemble of rank 1023, with exact terminal SVP and positive twin slack $10^{-6}$ as in Part 90.

| Width | Terminal minimum lower bound | Lower fraction of $0.85G_\beta$ | Target less certified bound (approx.) |
|---:|---:|---:|---:|
| 406 | 0.12656786 | 0.342813 | 0.24263 |
| 506 | 0.36551260 | 0.447758 | 0.45080 |

## Which determinant occurs in the test?

Write $b=\beta$, $k=n-b$, $W=L_k$, $P=L_{k+1}$, $B=L_b$, $v=\det W$, $D=\det P$, $g=D/v$, and $u=b_1$, $x=|u|$. Here $L_i$ denotes the primitive prefix. The two twin inequalities are
$$
 x/v^{1/k}\le a,\qquad g^{-1}(D/x)^{1/k}\le a .
$$
The normalized minimum $s=\lambda_1(B)/(\det B)^{1/b}$ yields $x/v^{1/k}=s(\det B)^{1/b}/v^{1/k}$ when $u$ is shortest in $B$. A large left side does not force a large $s$. The power of the Hermite constant in $a$ comes from the guarantee for a capped sequence of DBKZ tours on a rank-$k$ input. The last rank-$b$ SVP call alone gives no bound on the determinant ratio. The audited implementation hypotheses of Part 88 apply, including the Hermite cap used for the comparison and the LLL pre-pass for the subroutine. [Li–Walter, Algorithms 1 and 4](https://eprint.iacr.org/2023/140.pdf) · [Part 88 and audit](wall1_li_walter.md)

## Simultaneous completion lemma

Fix any passing Part 90 witness, retaining the primitive chain $\mathbb Zu\subset W\subset P\subset L$. Let $p\in P^*$ be the primitive normal to $W$ in the span of $P$, with $|p|=1/g$. For $2\le b<k$, infinitely many choices of $B$ in this chain realize $u$ as a shortest vector of $B$ and $p$ as a shortest vector of the reversed-dual first $b$-window of the shifted block. They preserve $x,v,D,g$ and the projected terminal lattice.

Indeed let $E=(W/\mathbb Zu)\otimes\mathbb R$, of dimension $k-1$. Choose a rational complete flag $F_i$ in $E$ and take $L_j$ inside $W$ as the saturated preimage of $F_{j-1}$ for $1\le j\le k$. Saturation gives an adapted integral basis by successive primitive rank-one extension. Keep the terminal lift and all later columns. The primal window is $L_b$. The dual window is
$$
 C=P^*\cap (\operatorname{span} L_{k+1-b})^\perp .
$$
Indeed the dual basis columns in reverse order starting at index $k+1$ annihilate the preceding prefix and span its integral annihilator. They also belong to the dual of the shifted projected block since they annihilate $u$. Its first column is $p$ up to sign.

Each $w\in W$ with $0<|w|<x$ has nonzero class in $E$ by primitivity of $u$. Exclude flags with this class in $F_{b-1}$. For each $q\in P^*$ with $0<|q|<1/g$ and $q(u)=0$, its restriction to $E$ is a nonzero functional since the integral annihilator of $W$ is $\mathbb Zp$. Exclude flags with $F_{k-b}\subset\ker q$. There are finitely many competitors in these bounded balls. Each exclusion is a proper closed incidence condition since $b-1<k-1$ and $k-b>0$. Their complements are dense open: an arbitrarily small rotation moves any incident subspace out of the specified incidence. Rational flags are dense by approximating an adapted real frame by rational frames. This gives a rational flag outside all exclusions. Repeating while excluding finitely many previously used $F_{b-1}$ gives infinitely many distinct $B$. Size reduction by earlier columns preserves each prefix, its annihilator and the projected terminal test. This proves the lemma, including for the overlapping primal and dual windows at the two stated widths.

In fact $s$ tends to zero along distinct such $B$: their primitive exterior vectors up to sign belong to the discrete lattice $\bigwedge^b W$ and have norm $\det B$. Only finitely many lie below any fixed norm. Thus witnesses arbitrarily far from the upper Hermite tail already suffice.

## Consequence for unfolding

At fixed $D$, write $r=k+1$ and $t=\det B/D^{b/r}$. Iterating the primitive split first at $P$, then at $B$ in its unit shape, gives radial intensity
$$
 nK_{n,r}D^{n-1}\,dD\; rK_{r,b}t^{r-1}\,dt ,
$$
where $K_{d,j}$ is the unit determinant-cut primitive mean in dimension $d$. At fixed radii the three normalized diagonal shapes are independent Haar before testing, and the lift coordinates must be retained. The integrand for counting pairs is the conditional probability that a compatible flag passes all the tests, including $g<\rho$. Using the exact minimum density of Part 46 inside this conditional integral is legitimate if one retains the remaining conditional data. By the lemma and Tonelli the resulting integral is infinite whenever the bad-extension event has positive probability. [Primitive split](wall1_prefix_level.md) · [Minimum density](wall1_haar_prefix_law.md)

For every $\rho>0$ the event has positive Haar measure here. Take the first $r$ columns orthogonal of equal length $c<\min(1,\rho)$ and the remaining $n-r$ orthogonal of length $c^{-r/(n-r)}$. Both twin ratios equal one, strictly below the audited $a$. The terminal line is strictly shorter than every off-line competitor. These inequalities persist on a neighborhood of the basis matrix by continuity (locally only finitely many lattice vectors can compete in the projected quotient). Its image has positive Haar measure. This proves divergence for every positive cut. Counting each $P$ once restores exactly the Part 90 event by the lemma; the Part 90 upper limit of $1+4\cdot10^{-12}$ times the determinant-only Markov radius therefore still applies to these extra local tests with the audited factors.

The construction concerns existential witnesses. It gives no distribution for the intermediate flags actually returned by DBKZ. Weighting flags by the implementation's selection probabilities or proving a further determinant constraint from its history could change the count. Treating a selected block as an independent Haar draw, or substituting its normalized minimum for the Hermite constant throughout the tour guarantee, is heuristic.

## Interval certificate

Elimination gives $D\le a^{k(k+1)/(k-1)}g^{k+1}$. Setting the primitive mean below this determinant cut equal to $0.01$ gives the radius used in the table. Run from the repository root. The reused Part 90 interval routine implements this radius and the comparison scale using Part 86's audited caps. The checks enclose the displayed shortfalls to the nearest last digit and certify the downward rounding of both lower bounds. [Part 90](wall1_selfdual_sharpen.md)

```python
from pathlib import Path
source = Path("docs/research/wall1_selfdual_sharpen.md").read_text()
exec(source.split("\n```python\n")[1].split("def ball")[0])
for b, length, fraction, gap in [
    (406, 12656786, 342813, 24263),
    (506, 36551260, 447758, 45080),
]:
    R, f, _, _ = row(b, ".000001")
    assert length <= R*10**8 and R*10**8 < length+1
    assert fraction <= f*10**6 and f*10**6 < fraction+1
    delta = R/f - I.mpf(length)/10**8
    assert 2*gap-1 < 2*10**5*delta and 2*10**5*delta < 2*gap+1
    print(b, length, fraction, gap)
```
