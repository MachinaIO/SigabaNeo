# A weighted finite-graph bound for the terminal minimum

At horizontal width 506 the lower bound proved here is **0.14196763 normalized, or 8.15876975 physical**, with design probability greater than 0.99. It uses exact terminal SVP, the 1% twin tests, and the sharpened width-506 Hermite cap of Part 96. With the original Part 88 cap it gives **0.14175651**, or **8.14663693** physical, on the same assumptions as the 7.41883519 comparison. The gain comes from a rank-dependent weight on short ambient vectors. The weight controls the covolume of *every* candidate annihilator, including one chosen after seeing the matrix. These are the best bounds obtained here for the respective predicates. Optimal graph-ensemble quantiles remain open. [Part 88](wall1_li_walter.md) · [Part 92](wall1_qary_gap.md) · [Part 96](wall1_rankin_twin.md)

## A determinant test from ball overlaps

Write $N=1023$, $m=511$, $n=512$, $q=3329$, $u=q^{m/N}$. Consider either $G=L_A=\{(x,y):x+Ay=0\bmod q\}$ with length unit $s=u$, or $G=qL_A^*=\{(x,y):y=A^t x\bmod q\}$ with $s=q/u$. For a fixed nonzero integer vector shorter than $q$, graph membership has probability at most $s^{-N}$. This follows by exposing the image of its nonzero input residue under the uniform matrix. A zero input residue makes membership impossible at these lengths. This elementary finite averaging step is related to Construction A vector averaging. [Loeliger](https://people.ee.ethz.ch/~loeliger/localpapers/LatticesAveraging1997.pdf)

In dimension $d$, let $f(v)$ be the volume of overlap of two radius-$t$ balls with center difference $v$, divided by $V_dt^d$, where $V_d$ is unit ball volume. Use the same radial profile in the ambient space. For *every* rank-$d$ sublattice $J$ of $G$,
$$
\frac{V_dt^d}{\det J}\le \sum_{v\in J} f(v)\le 1+Y,\qquad
Y=\sum_{0\ne v\in G}f(v).
$$
Indeed, count the points of a uniformly translated $J$ inside the ball in its span. Its mean is $V_dt^d/\det J$, and its second moment is that mean times the overlap sum, by integration over a fundamental domain. Nonnegative variance gives the first inequality. This second moment is over translations and holds for each fixed lattice.

Slicing the lens perpendicular to the line of centers gives $f(v)=\Pr(2tS\ge\|v\|)$ where $S$ on $[0,1]$ has density proportional to $(1-S^2)^{(d-1)/2}$. In particular
$$
m_N=\mathbb E S^N=\frac{\Gamma((d+2)/2)\Gamma((N+1)/2)}
{\sqrt\pi\,\Gamma((N+d+2)/2)}.
$$
A ball of radius $a$ contains at most $2V_N(a^2+N/4)^{N/2}$ integer points. From the unit cube at each such point $v$ take the half with displacement $e$ satisfying $v\cdot e\le0$. These disjoint half-cubes fit into the enlarged ball. Thus if $2t<q$, graph averaging and the triangle inequality in $L^{N/2}$ give
$$
\mathbb EY\le 2V_Ns^{-N}\left((2t)^2m_N^{2/N}+N/4\right)^{N/2}.
$$
This remains valid at arbitrarily small slice radii. Including the integer origin in the counting upper bound only enlarges it.

Choose $p=0.009999$, $h=d/(N-d)$ and $t$ by setting the right side equal to $ph$. Then Markov gives, with probability at least $1-p$, simultaneously for all $J$ of this rank,
$$
(\det J)^{1/d}/s\ge F(d,s)=V_d^{1/d}(t/s)(1+h)^{-1/d}.
$$
The choice of $h$ optimizes the expression after omitting the cube correction. The numerical certificate retains that correction.

## From determinants to the width curve

Put $b=\beta$, $k=N-b$, $r=k+1$, $z=b-1$. For a primitive extension $P$ of rank $r$, the orthogonal annihilator $J=qL_A^*\cap P^\perp$ has $\det J/(q/u)^z=\det P/u^r$ by primitive completion. If the cap is $\det P\le (e^\ell g)^r$ for physical terminal head $g$, either overlap test separately certifies
$$
g/u\ge e^{-\ell}F(r,u)\quad\text{or}\quad
g/u\ge e^{-\ell}F(z,q/u)^{z/r},
$$
respectively. The script selects the larger certificate *before sampling*, also comparing the Part 92 single-vector test. For $b\le511$ use the Part 88 twin with $\ell=k[\log J_b/(b-1)+\log(1.01)/(k-1)]$, $J_b$ the Hermite square-root cap. For $b\ge512$ the published two-block layout ends. Use Part 93's terminal variant with exact terminal primal SVP and named full-extension dual normal of length $1/g\le1.0001\lambda_1(P^*)$. Hermite gives $\ell=\log J_r+\log(1.0001)$. The latter rows require this variant. Part 95's suffix completion alone gives no stronger extension test. [Part 93](wall1_combined_reducer.md) · [Part 95](wall1_hkz_terminal.md)

| Horizontal width | Winning lattice | Normalized floor | Physical floor |
|---:|:---|---:|---:|
| 450 | dual | 0.09115370 | 5.23853250 |
| 475 | dual | 0.11217772 | 6.44676672 |
| 500 | dual | 0.13572853 | 7.80021391 |
| 505 | dual | 0.14074162 | 8.08831183 |
| 506 | dual | 0.14196763 | 8.15876975 |
| 511 | dual | 0.14689112 | 8.44171912 |
| 512 | dual | 0.14939740 | 8.58575305 |
| 525 | primal | 0.15204207 | 8.73774013 |
| 550 | primal | 0.15756051 | 9.05488046 |
| 575 | primal | 0.16363365 | 9.40389905 |
| 600 | primal | 0.17035375 | 9.79009846 |
| 625 | primal | 0.17783645 | 10.22012319 |
| 647 | primal | 0.18516440 | 10.64125487 |

The script gives every integer width 450–647. The probability applies at each predetermined width to every passing basis, with no joint 198-width probability asserted. The graph model is uniform over all matrices. A particular supplied matrix would require testing its geometry.

At $b=506$ the necessary height-zero cutoff of Part 94 is $\sqrt{1+1.2b}=24.66171121\ldots$, or $0.4291290066\ldots$ after division by $u=57.46922448\ldots$. The improved floor reaches about 33.1% of it. For comparison the Part 88 Haar certificate converts to about 20.80 physical, and its $0.85$ GSA benchmark to 46.91. Even the necessary cutoff understates the difficulty. With $Z=\|QX\|^2$, Part 94 gives $\mu=1.5b$ and $\operatorname{Var}Z\le4.5b$. Cantelli gives $\Pr(Z\le\mu-a)\le4.5b/(4.5b+a^2)$. If height zero succeeds 99% of the time, this forces $g\ge\sqrt{1+\mu-\sqrt{4.5b/99}}$, about **27.481 physical**. Neither floor supplies height-one or higher-height uniqueness. Horizontal width 505 is the appropriate row for final oracle rank 506 if the reducer meets the tests at 505. [Threshold](wall1_threshold.md) · [Conditional uniqueness](wall1_dist_unique.md) · [Wall 1](../PROOF_GAP.md)

## Joint modular counts and the remaining arithmetic sum

There is also an exact mixed mean. Fix a rational extension plane with saturated integral basis $(E;F)$ (top $m$ rows). Sum over distinct matrices $B$ representing restrictions $AF=B$, equivalently over $B$ killing $\ker F$ modulo $q$. For an ordered tuple of dual vectors with coordinate matrices $(X;Y)$, impose $A^tX=Y$. Write $t_0=\operatorname{rank}_q F$, $a=\operatorname{rank}_q X$. The joint weight for a given $B$ is zero unless
$$
\ker X\subseteq\ker Y,\qquad X^tB=Y^tF.
$$
Otherwise it is exactly $q^{-mt_0-a(n-t_0)}$. Indeed on the image of $F$ the map is prescribed. On each of $n-t_0$ complementary basis vectors its $m$ output entries satisfy $a$ independent scalar equations. The compatibility conditions give precisely consistency on the prescribed space and among the rows. Multiply by the cap indicator
$$
\mathbf1\{\det(V\cap\mathbb Z^N)\ q^{\operatorname{rank}_q(E+B)}\le D\}
$$
and sum over rational planes, restrictions and any finitely supported tuple weights. This counts one primitive extension per plane; impose real orthogonality to the plane if counting only its annihilator vectors. Taking zero tuple columns recovers the finite primitive-sublattice first moment. Two columns include both modularly dependent and independent pairs. [Exact graph mean](wall1_selfdual_qary.md)

This identity exposes the correlation but still needs a bounded-height rational-plane sum with the indicated incidence conditions. A second moment of the raw extension count alone bounds a *lower* tail via Paley–Zygmund and does not improve Markov's upper bound merely by being available. The overlap test bypasses that sum by charging dense sublattices to one ambient statistic. It does not transfer the Haar primitive-sublattice constant or settle the gap at any listed width.

## Interval reproduction

Run from the repository root. The columns are width, method (0 primal overlap, 1 dual overlap, 2 Part 92), normalized floor, physical floor and normalized Part 94 necessary cutoff. The last three columns round down in units of $10^{-8}$.

```python
from pathlib import Path
src=Path('docs/research/wall1_dual_pinning.md').read_text()
exec(src.split('\n```python\n')[1].split('def ceildiv')[0])
N,q=1023,3329
u=I.exp(511*I.ln(q)/N)
def logvol(d):
    return d*I.ln(I.pi)/2-I.loggamma(1+I.mpf(d)/2)
def logJ(d):
    return I.mpf(C[d])/(M*d)
def bound(d,unit):
    # E Y <= p * d/(N-d), so the Markov denominator is N/(N-d).
    p=I.mpf('.009999')
    h=I.mpf(d)/(N-d)
    B=unit*I.exp((I.ln(p*h/2)-logvol(N))/N)
    lm=(I.loggamma(1+I.mpf(d)/2)+I.loggamma(I.mpf(N+1)/2)
        -I.ln(I.pi)/2-I.loggamma(1+I.mpf(N+d)/2))
    t=I.sqrt(B**2-I.mpf(N)/4)*I.exp(-lm/N)/2
    assert 2*t<q
    return (logvol(d)-I.ln(1+h))/d+I.ln(t/unit)
def twinlog(b):
    return min(logJ(b),I.mpf("1019.379685531")/506) if b==506 else logJ(b)
def row(b):
    k=N-b
    r,z=k+1,b-1
    ell=(k*(twinlog(b)/(b-1)+I.ln(I.mpf('1.01'))/(k-1)) if b<=511
         else logJ(r)+I.ln(I.mpf('1.0001')))
    pd=bound(r,u)
    dd=bound(z,q/u)*z/r
    L=I.sqrt(N/(2*I.pi*I.exp(1)))*I.exp(I.ln(I.mpf('.0199'))/N)
    old=(I.ln(L)-logJ(z))*z/r
    # Choose one test in advance. No charge for taking the best theorem.
    gain=max([pd,dd,old],key=lambda x:x.a)
    return I.exp(gain-ell),[pd,dd,old].index(gain)
def digits(x):
    lo,hi=int((10**8*x).a),int((10**8*x).b)
    assert lo==hi
    return lo
for b in range(450,648):
    R,method=row(b)
    need=I.sqrt(1+I.mpf('1.2')*b)/u
    assert R<need
    print(b,method,digits(R),digits(u*R),digits(need))
assert digits(row(506)[0])==14196763
assert digits(row(506)[0]*u)==815876975
assert digits(I.sqrt(I.mpf('608.2'))/u)==42912900
assert I.mpf('27.48097') < I.sqrt(760-I.sqrt(I.mpf(2277)/99)) < I.mpf('27.48099')
original=row(506)[0]*I.exp(-517*(logJ(506)-twinlog(506))/505)
assert digits(original)==14175651 and digits(original*u)==814663693
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT WITH MINOR ISSUES.

* **Mixed modular count.** The identity is exact for every case: zero ranks, dependent columns, and rank-deficient A.
* **Adaptivity.** A single Markov event covers every annihilator, including one chosen by a reducer after seeing A. The design
  probability is ≥ 0.990001 per predetermined width.
* **Which twin cap.**
  * 8.14663693 holds under Part 88's original twin thresholds.
  * 8.15876975 needs the actual twin factors to satisfy a ≤ 1.01·exp(516·H_506/(506·505)), using Part 96's first column, which
    is the universal cap. It does not need any above-β predicate.
* **Height-zero floor.** The downward-rounded necessary floor is 27.48097830 (Cantelli).
* **Reproduction.** An independent outward-rounded recurrence reproduced all 198 widths. The dual test wins through width 512,
  and the primal test from 513 on.
