# A global shortest flag in the retained lattice

The old horizontal winner is global in the retained lattice. This identifies the right flag to follow. Even with fixed determinant, a unique shortest line, and zero displacement, the two normalized lengths of that flag do not determine their next values. There is an exact induction on marked flags, but its horizontal branch consumes one additional old direction per draw.

## The terminal test has two different GH normalizations

Write $d=b-1$, $D=\det L$, $G_i=V_i^{-1/i}$, and $Q_x L=\pi_{x^\perp} L$. Choose the signed shortest vector $x$ using the inherited ambient frame, and put $t=|x|$, $Y=t/(G_d D^{1/d})$. The old statistic is $\psi=\lambda_1(Q_x L)/(G_{d-1}(D/t)^{1/(d-1)})$. The *new* quotient on a horizontal win has rank $d$ and determinant $D/t$, since the append has height one. Thus the exact horizontal charge in Part 120 is
$$
 w_0\,\mathbf1\!\left\{\psi < \theta(D,t)\right\},\qquad
 \theta(D,t)=c\frac{G_d}{G_{d-1}}(D/t)^{-1/[d(d-1)]}.
$$
An induction must carry physical scale as well as shape. Its law also depends on the displacement subgroup and the tie frame. Conditional on this marked state, average over uniform $U\in H$, form $W=L+\mathbb Z(\tilde U,1)$, choose its shortest $v$, and push forward to $Q_v W$ with the projected mark, exactly as in [Part 108](wall1_first_tour.md). This gives an exact recursion for expectations of any test on the state, initialized with the reduced graph law at the restart. Marginalizing to $Y,\psi$ leaves an unknown conditional transition.

Explicitly, write $S=(L,H,\text{frame})$ and $T(S,U)$ for the marked update. For a terminal test $f$ set
$$
 (Kf)(S)=|H|^{-1}\sum_{U\in H} f(T(S,U)).
$$
If $\nu$ is the restart law, the required horizontal expectation is $\nu K^{406}f$ with $f=w_0\mathbf1_{\psi<\theta}$. Taking $f=\mathbf1_{Y<a,\,\psi<p}$ instead gives the recursion for the joint lower-tail distribution at any suffix step by changing the exponent. The witness decomposition below describes the information needed to evaluate one application of $K$ to that test.

## A witness for the next pair

Set $s=|v|$, $L'=Q_vW$, let $z$ be the designated shortest of $L'$, and put $u=|z|$. The event $Y'<a$ tests $u<aG_d(D/s)^{1/d}$. For $\psi'<p$ put $R=pG_{d-1}(D/(su))^{1/(d-1)}$. The latter event is equivalent to the existence of a saturated flag of ranks $1,2,3$ in $W$, starting with $v$, whose plane projects to the designated line of $z$, and whose triple has determinant $<suR$. Indeed the two quotient maps have kernel lines with primitive lengths $s,u$. The inverse image of a primitive witness line under the composite supplies the triple, and projecting recovers the line. The plane alone has area $su$.

* If the triple is horizontal, it lies in $L$. Both winner tests still apply. A small plane in $L$ suffices as a necessary witness for the $Y'$ test, while the joint test can require the third direction.
* Otherwise the height image is $j\mathbb Z$, $j>0$, and the primitive horizontal kernel $P$ has rank two. Write the extra generator as $(y,j)$ modulo $P$, $y\in j\tilde U+L$. The triple volume is $\det P\sqrt{j^2+|\pi_{P^\perp}y|^2}$. Summing over kernels, heights and cosets, with saturation and both selected lines checked for the actual draw, is the rank-three version of the [Part 120 fiber sum](wall1_plane_count.md). For the plane alone the horizontal kernel has rank one.
* There is also a vector-only charge. Round a lift of $z$ along $v$, then lift the short final line rounding successively along $z,v$ in Gram–Schmidt coordinates. The three resulting generators have lengths at most $s,\sqrt{u^2+s^2/4},\sqrt{R^2+u^2/4+s^2/4}$, respectively (strict for the last). Positive height forces one of them to have positive absolute height. On bins with deterministic upper bounds use the largest of these radii, enlarged for closed endpoints, in the [Part 110 layer moment](wall1_additive_tour.md). This bounds the event by an expected vector count. It need not be small at that enlarged radius, and it discards the two selector tests.

## What propagates exactly

For a saturated rank-$r$ sublattice $N\subset L'$, its full inverse image $M\subset W$ has rank $r+1$. Define $h_r(N;B)=\det N/(\det B)^{r/\mathrm{rk}(B)}$. Basis extension and orthogonal projection give
$$
 h_{r+1}(M;W)=(s/D^{1/b})^{1-r/d} h_r(N;L').
$$
Minimizing on the left **through the winner** gives the exact quotient Rankin minimum with this factor. Removing incidence gives only a lower bound for the quotient minimum. Neither the factor nor incidence disappears on repeating the update. A positive-height inverse image needs a rank-$r$ horizontal kernel, whereas a horizontal inverse image needs old rank $r+1$.

For a concrete information loss take orthogonal sides $(1/8,1/4,1/3,3)$ or $(1/8,1/4,1/2,2)$, with the same trivial mark and a unit orthogonal append. The old determinants agree, as do the first two minima, the minimum plane area and the selected pair $(Y,\psi)$. The first two winners in the appended flag have lengths $1/8,1/4$. The third lengths are $1/3,1/2$, so the new quotient-of-shortest ratios differ at identical determinant. More generally put $k$ distinct increasing sides below one, then a variable side between the last of these and one, then a balancing side above one to fix the determinant. Through rank $k$ even all Rankin minima agree (coordinate products attain the lower bounds by Cauchy–Binet). Under repeated zero appends the initial short sides are removed in order, exposing the hidden side. For a terminal old plane, arbitrarily many horizontal pullbacks are thus possible across dimensions. These are marked-state counterexamples to fixed-depth exact propagation. They do not establish how frequently these flags occur in the graph process or exclude a probabilistic majorant on reachable states.

## Small first-pass experiment (evidence)

Start from the Part 119 cubic state, use prime 17 and seeds 0 through 63 in each width, and take ten draws. At each step record the two normalized retained minima. Lift the designated shortest plane backwards through the saved basis completions until its inverse image first has positive height, counting consecutive wholly horizontal lifts. This measures the depth of the horizontal branch for that particular flag, including flags above the threshold. The positive-height branch can still need old kernel statistics.

| Width | Statistic | Counts below 0.954 at steps 1 through 10 (out of 64 each) |
|---|---|---|
| 5 | $Y$ | 3, 5, 2, 0, 0, 0, 0, 0, 0, 0 |
| 5 | $\psi$ | 0 at every step |
| 7 | $Y$ | 1, 3, 3, 2, 2, 1, 2, 0, 0, 0 |
| 7 | $\psi$ | 0, 0, 0, 0, 0, 1, 0, 0, 0, 0 |

From step one to step two there were 36 certified strict decreases in $Y$ and 33 in $\psi$ at width 5. At width 7 the counts were 31 and 30. Thus even the normalized statistics along graph trajectories can decrease. The largest observed horizontal depth was one, reached once at step ten at width 5 and once at each of steps eight through ten at width 7. All other tested flags met positive height on the first lift. These counts use a fixed diagnostic threshold for both ratios. They neither bound the depth on other histories nor estimate the weighted terminal event at 506.

## Width 506

After the restart, the last horizontal charge tests a rank-two flag in the penultimate retained lattice. Pulling it back through all 406 preceding draws could ask for rank 408 in the initial rank-505 state. This is a finite hierarchy for the given horizon. Its exact recursion also retains incidences, selector weights and displacement fibers. There is no derived bounded-rank estimate for the history average. [Part 107](wall1_lit_random_bases.md) proves a global-selection estimate for a Haar **parent** at rank 1000. Here the parent has rank 505 and its law comes from the marked graph recursion. Even the Haar benchmark must use the one-sided, scale-dependent threshold above. The [Part 105 conditional density](wall1_selection_law.md) assumes a Haar input and supplies no comparison for these histories.

Consequently neither the horizontal budget $0.00488848$ nor the separate positive-height budget of that size follows. If both estimates held, Part 120's union bound and prefix coupling would give failure below one percent. A transfer estimate for the weighted threshold event, plus an estimate for the filtered positive-height moment, would suffice without proving a full shape law. [Part 120 and audit](wall1_plane_count.md) · [Wall 1](../PROOF_GAP.md)

## Reproduction

Save the Python block from [Part 119](wall1_experiments.md) as `kernel.py` and run this block alongside it with the same Sage Python environment. Its SVP decisions are exact. The unused floating-point LLL spread plays no role. GH comparisons use outward-rounded intervals and the threshold tests assert separation.

```python
from kernel import *
from sage.all import RealIntervalField
from collections import Counter
I=RealIntervalField(160)
def gh(k,D2):
    return (I(D2).sqrt()*((I(k)/2+1).gamma())/(I.pi()**(I(k)/2)))**(I(1)/k)
def below(x,c):
    assert x.upper()<c.lower() or x.lower()>c.upper()
    return int(x.upper()<c.lower())
def cut(B):
    c,s,D,_=shortest(B)
    v=c*B
    _,H=matrix(c).transpose().hermite_form(transformation=True,include_zero_rows=True)
    T=H.inverse().transpose().change_ring(ZZ)
    R=T[1:]*B
    Q=R-(R*matrix(v).transpose())*matrix(v)/s
    assert T[0]==c and (Q*Q.transpose()).det()*s==D
    return T,H,Q,I(s).sqrt()/gh(B.nrows(),D)
def run(d,q,N):
    out=[Counter() for _ in range(10)]
    for seed in range(N):
        rng=Random(seed)
        B=q*identity_matrix(QQ,d)
        C=identity_matrix(ZZ,d)
        past=[]
        prev=None
        for row in out:
            a=vector(QQ,[x%q for x in vector(ZZ,[rng.randrange(q) for _ in range(d)])*C])/q
            W=B.stack(matrix([a*B])).augment(matrix(QQ,d+1,1,[0]*d+[1]))
            T,H,B,_=cut(W)
            past.append(T)
            C=(C.augment(zero_matrix(ZZ,d,1))*H.transpose())[:,1:]%q
            U,_,P,y=cut(B)
            V,_,_,psi=cut(P)
            flag=matrix([U[0],V[0]*U[1:]])
            depth=0
            for S in reversed(past):
                lift=matrix([S[0]]+list((flag*S[1:]).rows()))
                if any(lift.column(-1)): break
                flag=lift[:,:-1]
                depth+=1
            if prev is not None:
                row['dropY']+=int(y.upper()<prev[0].lower())
                row['dropP']+=int(psi.upper()<prev[1].lower())
            prev=(y,psi)
            row['Y']+=below(y,I('0.954'))
            row['psi']+=below(psi,I('0.954'))
            row['max']=max(row['max'],depth)
            row[depth]+=1
    Y,P,H,dy,dp={
        4: ([3,5,2,0,0,0,0,0,0,0],[0]*10,[0]*9+[1],36,33),
        6: ([1,3,3,2,2,1,2,0,0,0],[0]*5+[1]+[0]*4,[0]*7+[1]*3,31,30)
    }[d]
    assert [r['Y'] for r in out]==Y and [r['psi'] for r in out]==P
    assert [r[1] for r in out]==H and all(r[0]+r[1]==N for r in out)
    assert (out[1]['dropY'],out[1]['dropP'])==(dy,dp)
run(4,17,64)
run(6,17,64)
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **Non-closure of (λ1/GH, ψ).** The explicit rectangular counterexample works: two states with determinant 1/32 and trivial
  H give next ψ values 1/(3G_3) and 1/(2G_3) on the same zero draw.
* **Rank growth.** Rank 408 is right for the all-horizontal branch. Rectangular families realize arbitrary horizontal depth on
  the general state space. How often this happens under the width-506 restart law is open.
* **Experiments.** Reproduced exactly. Strict-decrease counts are (36, 33) at width 5 and (31, 30) at width 7. Of 1,280
  designated planes, 4 had depth one and the rest depth zero. These counts are evidence only.
