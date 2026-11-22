# Averaged sublattice counts in the first tour

At width 506 the proposed all-cutoff Haar class already needs a multiplier greater than $10^{375}$ **at the unconditioned restart**. This obstruction uses the actual graph law and rank one alone. A closed positive linear upper recursion does exist after a packing relaxation. Its one-step loss on the Haar vector can be even larger. Neither loss is a lower bound on terminal failure.

## The restart test

Use $d=505$, $b=d+1$, $q=3329$. At time zero of the reduced experiment the lattice consists of $(u,y)$ with $u=By\pmod q$, where $B$ is uniform of size $400\times105$, and $D_0=q^{400}$. Each zero column supplies its own primitive unit line. Thus for every $x>1$,
$$M_1^{(0)}(x)\ge105q^{-400}.$$
The unoriented primitive-line Haar mean at determinant $D$ is $V_dx^d/(2\zeta(d)D)$. Taking $x\downarrow1$ gives the necessary multiplier $C\ge210\zeta(505)/V_{505}>10^{375}$. Linearity counts the columns even if several vanish. There is no conditioning on agreement with the coordinate prefix. [Restart law](wall1_idea_round2.md)

More generally the Haar mean for $1\le r<d$ is $a(d,r)x^d/D^r$, where
$$
a(d,r)=\frac1d{d\choose r}\prod_{i=1}^r
\frac{V_{d-i+1}\zeta(i)}{V_i\zeta(d-i+1)}
$$
with $\zeta(1)=1$ in this product. Rank $d$ has the single atom $D$. With a random determinant the physical-cutoff reference averages this formula over $D$; a cutoff in own-determinant units instead tests $\det P<zD^{r/d}$ inside each history. An unconditioned physical-cutoff inequality alone cannot substitute a correlated random cutoff. The restart obstruction applies to both conventions since $D_0$ is fixed. [Kim, Theorem 1](https://arxiv.org/abs/2005.10874)

## Exact identity with the mark

Condition on the old framed lattice $(L,H)$, put $D=\det L$, draw $U$ uniformly from $H$, and let $v$ be the prescribed signed shortest vector of $W=L+\mathbb Z(\tilde U,1)$, $s=|v|$. The quotient has determinant $D/s$. Full inverse image under projection is a bijection from saturated rank-$r$ sublattices of the quotient to saturated rank-$(r+1)$ sublattices $N$ of $W$ containing $v$. Indeed the quotient group by either sublattice is the same and extending $v$ to a basis of $N$ gives $\det N=s\det(\pi_v N)$. Thus use the strict cap $C(U)=sx$ or, for a normalized threshold, $C(U)=zD^{r/d}s^{1-r/d}$. [Parts 120–121](wall1_global_quotient.md)

The exact old horizontal contribution is the draw average of the sum over saturated rank-$(r+1)$ sublattices $N$ of $L$ of $\mathbf1_{v\in N,\ \det N<C(U)}$. In particular a fresh winner kills the entire horizontal term. For the other term sum over saturated rank-$r$ kernels $P\subset L$, $a=\det P$, and positive height generators $j$. Put $L_j/L=jH$. Sum over $[y]\in L_j/P$ with weight $1/|jH|$ times the conditional mean over $U$ satisfying $jU=y+L$. Inside this mean use the indicator of all three tests
$$
 N=P+\mathbb Z(y,j)\text{ saturated in }W,\qquad
 v\in N,\qquad a\sqrt{j^2+|\pi_{P^\perp}y|^2}<C(U).
$$
Here $P$ sits at height zero. Height and its kernel uniquely recover the data modulo $P$. Saturation is primitivity of $(y-j\tilde U\bmod P,j)$ in $(L/P)\oplus\mathbb Z$. The fiber average has denominator $|H[j]|$, including when $q\mid j$. Averaging the two contributions over the old history gives equality. The projected coset and the selector in its fiber still enter the answer for a fixed kernel covolume. [Part 108](wall1_first_tour.md) · [Part 110](wall1_additive_tour.md) · [Part 120](wall1_plane_count.md)

## A linear upper operator on the unmarked moments

Write $dM_r(a)$ for the expected counting measure, so $M_r(x)$ excludes atoms at $x$. Use deterministic bounds $m_t\le\lambda_1(L)$, $s\le S_t$. At the restart take $m_0=1$ by integrality and then $m_t=(\sqrt3/2)^t$: positive height costs at least one, hence $s\ge\min(m_t,1)$, and rounding a lift along $v$ gives the next floor. One can always use $S_t=q$ since the projected $q$-axes span the window and have length at most $q$. The Hermite cap $\sqrt{\gamma_b}D^{1/b}$ can also be used with a deterministic upper bound on $D$ (or within determinant bins). For example $D_{t+1}\le D_t/\min(m_t,1)$. All formulas below concern physical $x>0$.

Set $C=S_t x$ and $k_r=V_{r+1}(m_t/2)^{r+1}$. For $r<d$, any nonzero difference in $\pi_{P^\perp}L$ has length at least $k_r/a$. Indeed adjoining its lift to $P$ gives a rank-$(r+1)$ lattice of minimum at least $m_t$, whose determinant is at least $k_r$ by packing. For each individual draw the projected coset at height $j$ has exactly one point per class modulo $P$, by saturation. Packing disjoint balls in dimension $d-r$ bounds its disk count, uniformly over the mark. Dropping saturation of the extension and winner incidence now gives
$$
M_r^{(t+1)}(x)\le M_{r+1}^{(t)}(C)+
\int \sum_{1\le j<C/a}
\left(1+\frac{2\sqrt{C^2-a^2j^2}}{k_r}\right)^{d-r}\,dM_r^{(t)}(a).
$$
The weight decreases with $a$, so domination of cumulative counts also suffices by layer cake. This is a linear upper system across all interior ranks. At the top use the exact $M_d^{(t+1)}(x)=\Pr(D/s<x)\le M_d^{(t)}(S_t x)$, and rank zero is the fixed atom at one. Floors can truncate the integration to the actual support $a\ge V_r(m_t/2)^r$. Binning $s$ more tightly requires joint bin-restricted moments if their probabilities are to be used. The identity above retains the winner exactly, while this upper operator spends its entire incidence probability on every candidate. [Depth and kernels](wall1_depth_truncation.md)

## Testing the operator and the budgets

For the displayed operator with the global $S_t=q$ and no optional support truncation, its rank-one output includes at least $M_1^{(t)}(qx)$ from the unit-height summand alone. Feed it the physical Haar vector at restart. The new physical Haar reference is at most $q$ times the old one at the same $x$, since $D'=D/s$. Thus even the first application has ratio at least $q^{504}>10^{1775}$. The same lower bound on the **operator's amplification** iterates: monotonicity and the unit-height summand give output at least the initial Haar line mean at $q^{407}x$, while the actual-determinant Haar reference grows at most $q^{407}$ at fixed $x$. The ratio exceeds $10^{722525}$. This quantifies one explicit relaxation. The restart lower bound is independent of that relaxation, including any change to caps or packing.

Even granting normalized domination at the terminal step, Markov would give $C\,(0.954)^{505}/(2\zeta(505))$. A charge of $0.00488848$ allows only about $2.08\times10^8$ for this multiplier, or twice that for the entire reduced budget. The all-cutoff restart constant makes this certificate vacuous. For the horizontal charge the exact quantity is $\mathbb E[w_0 I_0]$ from Part 120, and the other charge is $\mathbb E F_*$. A small terminal line moment would cover their union's failure event directly; a separate horizontal estimate requires the old short-plane event through its designated winner. The recursion provides neither allocated bound. Rare unit lines explain the failure of *uniform relative comparison*: their absolute expected count is tiny. An additive exceptional-history budget or a comparison restricted to selected cutoff ranges would require a different propagation estimate.

There is also a separate numerical loss in dropping the horizontal incidence test. Part 120's uniform gated area ceiling is $J K^{1-1/d}G_b^2D^{2/b}$, with $J K^{1-1/d}>1.04143$. Since $d$ independent projected axes of length at most $q$ give $D\le q^d$, this ceiling in old determinant units is at least $z_*=1.04143G_b^2q^{-2/b}$. Even with exact Haar input at fixed $D$, the **unrestricted** rank-two mean at this ceiling exceeds $10^4$, against $0.00488848$. This tests the uniform-ceiling, all-plane Markov bound. It leaves open the frequency of qualifying planes incident to the selected line at its actual cutoff. [Area gate](wall1_plane_count.md)

## Reproducible checks

Python interval checks use $1<\zeta(d)<1+2^{-d}(1+2/(d-1))$ by the integral test.

```python
from mpmath import iv
iv.dps = 60
I = iv.mpf
d, q = 505, 3329
V = iv.pi**(I(d)/2)/iv.gamma(1+I(d)/2)
assert 210/V > I(10)**375
def vol(n):
    return iv.pi**(I(n)/2)/iv.gamma(1+I(n)/2)
b = d+1
zstar = I('1.04143')*vol(b)**(-I(2)/b)*I(q)**(-I(2)/b)
# zeta(2)>1 and both denominator zeta factors are less than two.
a2lower = I(d-1)/2 * V*vol(d-1)/(2*iv.pi*4)
assert a2lower*zstar**d > 10**4
assert q**504 > 10**1775
assert I(407*504)*iv.log(I(q))/iv.log(I(10)) > 722525
base = I(2)*I('.00488848')/I('.954')**d
zmax = 1+I(2)**(-d)*(1+I(2)/(d-1))
assert I('2.08e8') < base and base*zmax < I('2.09e8')
```

For an exact check of information loss, use $L=\mathbb Z^2$ and cyclic marks of order three along either coordinate. Every incoming rank and cutoff, the determinant, and even the mark cardinality agree. The Part 119 signed SVP kernel selects $-e_1$ in all six draws. At $x=1.01$ the outgoing line means are $2$ and $4/3$. Thus the exact marked transition does not factor through all the unmarked moments on general inputs. This example concerns the transition domain; the zero-column calculation above concerns the specified graph law itself. Run with the Python block of [Part 119](wall1_experiments.md) saved as kernel.py in a Sage environment.

```python
from kernel import *
from itertools import product
for direction,target in [(0,[2,2,2]),(1,[2,1,1])]:
    counts=[]
    for k in range(3):
        u=[QQ(0),QQ(0),QQ(1)]
        u[direction]=QQ(k)/3
        W=matrix(QQ,[[1,0,0],[0,1,0],u])
        c,s,_,_=shortest(W)
        assert tuple(c*W)==(-1,0,0) and s==1
        # Projection deletes coordinate one. Short vectors have |n|<=1,
        # |m|<=2, and are primitive since the projected minimum is one.
        count=sum(1 for m,n in product(range(-2,3),repeat=2)
                  if 0<(m+n*u[1])**2+n*n<QQ(101)**2/10000)
        counts.append(count//2)
    assert counts==target
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **All-cutoff obstruction.** The bound 10^375.304 holds, as the right-hand limit at x ↓ 1: the expected line count is exactly
  105·q^{−400}, against the Haar line mean. The Markov allowance is ≈ 2.081·10⁸.
* **Recursions and amplification.** The exact marked recursion, the linear unmarked upper recursion, the one-step amplification
  ≥ q^504, and the unrestricted plane mean > 17,981 are all verified.
* **Key addition: the obstruction disappears on a GH band.** At the restart cutoff R = 0.954·GH(L_0) ≈ 3221.6 < q, every graph
  candidate has membership probability q^{−400}. A cube cover then gives

  M_1^{(0)}(R) / M_{1,Haar}(R) ≤ ζ(505)·(1 + √505/(2R))^505 < 5.803,

  and this holds throughout R ≤ x ≤ q.
* **Open.** Propagating a comparison restricted to the GH band through the suffix. The upper recursion samples incoming
  covolumes below its cap, so a band-only comparison does not close by itself.
