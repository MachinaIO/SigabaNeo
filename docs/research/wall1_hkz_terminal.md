# A dual-HKZ terminal flag at widths 406 and 506

Write $s_i=\|b_i^*\|$ with **one-based** indices, $N=1023$, $b=\beta$, $k=N-b$, $r=k+1$, $z=b-1$. Two endpoints matter. The Wall 1 radius is $g=s_r$, the **first** height of the last $b$ columns. The literal last height is $s_N$. For a Haar unimodular lattice the following lower bounds hold on one event of probability at least $1-61/6200>0.99$, for both widths and every output of the dual completion specified below. Twin slack is 1%, and terminal SVP is exact. Each fraction divides the lower bound by $0.85$ times the GSA height **at that row**.

| Quantity | 406 length | 406 fraction | 506 length | 506 fraction |
|---|---:|---:|---:|---:|
| Wall 1 head $s_r$ | 0.12531200 | 0.33941234 | 0.36188423 | 0.44331371 |
| $s_{N-59}$ | 0.00724412 | 0.29843217 | 0.01751895 | 0.43348580 |
| $s_{N-29}$ | 0.00765404 | 0.39925233 | 0.01717718 | 0.52026046 |
| $s_{N-9}$ | 0.00785821 | 0.47974545 | 0.01690241 | 0.58580407 |
| Literal last $s_N$ | 0.00793499 | 0.51997528 | 0.01677121 | 0.61760234 |

The last row holds deterministically for this completion. With the head alone and failure budget $1/101$ per width, the fractions are 0.33941455 and 0.44331716. The slight change is probability allocation. The Part 93 narrow-width curve used a smaller twin slack. Its peak near 512 pertains to the block head. [Part 88](wall1_li_walter.md) · [Part 93](wall1_combined_reducer.md)

## What suffix reduction alone implies

Start with a passing Part 88 basis and fix its first $r$ columns, including the exact shortest terminal head. Any unimodular completion in the quotient by their primitive span $P$ preserves both twin tests and $g$. For any fixed intermediate primitive prefix of rank $N-t$ extending $P$, its projected rank-$t$ quotient admits an HKZ basis in either chosen orientation by recursive exact SVP and primitive completion. Lift and size-reduce. Thus the set of passing $(P,g)$ is exactly the same before and after this terminal requirement. Even full primal HKZ on the $b$-block can continue recursively from its already shortest head. In particular no shape thinning factor at $P$ follows merely from existence of an HKZ completion. Part 87's wider reducer also preserves its tests under changes after $P$; its direct test in $P^*$ costs rank 618 or 518 here, above budget. [Part 87](wall1_selfdual_extend.md)

In fact for suffix-only reduction **there is no positive all-passing-bases lower bound on the literal last height**, even for a fixed input lattice. Here $2t\le z$. In an arbitrary quotient basis after $P$, select $t$ disjoint pairs $(e_i,f_i)$. Install all unpaired columns and the $e_i+m f_i$ in the intermediate prefix, for any positive integer $m$. The remaining $f_i$ complete unimodular pairs. After projecting away the enlarged prefix, their lengths are at most $\max_i\|e_i\|/m=E/m$, since the projections satisfy $m\pi f_i=-\pi e_i$. These short vectors generate the terminal lattice. In a primal HKZ recursion their projections still generate every remaining quotient, so every shortest head is at most $E/m$. In dual HKZ the first dual vector pairs nontrivially with some generator, hence has norm at least $m/E$ and $s_N\le E/m$. Size reduction preserves these heights. This proves the obstruction even for exact terminal oracles, simultaneously for any desired small cutoff on the primal HKZ tail. The literal last-height fraction certified by the suffix-only predicate is zero. Counting flags with free, uncapped middle choices cannot fix this: varying $m$ already gives infinitely many distinct intermediate planes for a single passing prefix. This is the multiplicity issue in [the twin count](wall1_twin_typical.md).

## A width-budgeted choice of the intermediate prefix

Run the terminating two-block reducer under the audited Part 88 assumptions. Preserve $P$ and form $J=L^*\cap P^\perp$, the dual of the remaining projected quotient. HKZ-reduce $J$ in forward order, taking its first $t$ recursive exact shortest vectors for any $1\le t\le60$. Complete this primitive flag arbitrarily and use the reversed dual basis in the quotient by $P$. This uses at most $t$ extra exact calls of dimensions $z,z-1,\ldots,z-t+1$, all below $b$. With $t=60$ one output suffices for the entire range. The first $t$ columns in the dual span are HKZ internally because each chosen shortest vector remains shortest in the restricted projected sublattice containing it. Dual HKZ size reduction can be performed on that span. If primal size reduction is required, reverse dualization followed by primal size reduction preserves the dual prefix flag and all its projected shortest heights (dual HKZ is understood up to size reduction). The construction fixes the intermediate prefix through the annihilator of the chosen dual span. This choice is essential to the numerical tail rows.

Let $U_j$ be the primitive rank-$j$ dual prefix so obtained, $u_j=\det U_j$, $u_0=1$. Equivalently $U_j$ annihilates the rank-$(N-j)$ primal prefix inside $L^*$. Put $D=\det P=\det J$ by complementary projected volume. The dual quotient at step $j$ has determinant $D/u_j$, dimension $z-j$, and shortest length $1/s_{N-j}$. Write $H_d$ for an audited upper bound on $\sqrt{\gamma_d}$. Hermite gives
$$s_{N-j}\ge H_{z-j}^{-1}(u_j/D)^{1/(z-j)}.$$
The denominator needs an **upper** bound. Write $v=\det L_k$,
$a=1.01 H_b^{(k-1)/(b-1)}$ and $M_0=a^{kr/(k-1)}$. The two twin inequalities yield $v\le M_0g^k$ and $D=vg\le M_0g^r$ by elimination of the first vector as in Part 88. Exact terminal SVP and Hermite also give $g\le H_b v^{-1/b}$. Consequently
$$v\le V=(M_0 H_b^k)^{b/N},\qquad D\le B=H_b V^{1-1/b}.$$

For $1\le d<N$ let $K_d X^N$ be the Haar mean number of unoriented primitive rank-$d$ sublattices of determinant at most $X$ in $L^*$. It equals the primal rank-$(N-d)$ count by annihilation. Put $F_d=(6200K_d)^{-1/N}$ and $F_0=1$. Markov and the union bound over $d=1,\ldots,59,405,505$ give, on the stated common event,
$$g\ge(F_z/M_0)^{1/r},\qquad
s_{N-j}\ge H_{z-j}^{-1}(F_j/B)^{1/(z-j)},\quad 0\le j<t.$$
Indeed $D\ge F_z$ and $u_j\ge F_j$ for every eligible primitive lattice at each cut. At $j=0$ only the deterministic cap enters. Dual prefix primitivity in the ambient dual follows by primitivity in the saturated $J$. Thus single-rank means suffice even though the output sublattices are nested and chosen adaptively. The per-width head-only calculation uses $101$ in place of $6200$. For the mean formula see [Kim, Mean value formulas on sublattices and flags of the random lattice](https://arxiv.org/abs/2005.10874).

## Interpretation and finite graph ensemble

The literal last row gains a positive floor from the prescribed dual choice. The Wall 1 head gains nothing from that choice: every passing head has such a completion. The inequalities certify neither the GSA slope nor a two-sided band. For example the 506 lower envelope goes from 0.01751895 to 0.01677121 over the displayed 60 rows; its fraction of the local target changes from 43.35% to 61.76%. A slope of lower bounds does not bound the slope of the realized heights. None of the 60 floors reaches its local target at either width. These results leave the selected-profile and planted recovery questions in [Wall 1](../PROOF_GAP.md) open.

For the Part 92 graph lattice divide primal lengths by $u=3329^{511/1023}$ and use its reciprocal dual scaling. Part 92 proves on a single event of probability greater than 0.99 that the normalized ambient dual minimum exceeds $L$ in the script below. Every rank-$j$ sublattice then has determinant at least $(L/H_j)^j$ by Hermite. Substituting this for each $F_j$ (keep $F_0=1$) proves the same joint tail formula, including the deterministic last row, for this finite ensemble. The normalized heads are at least 0.05852472 and 0.12909231, fractions 0.15851643 and 0.15814005. No Haar mean for graph flags is needed. [Part 92 and its theta bound](wall1_qary_gap.md)

## Interval certificate

Run from the repository root. The shared setup supplies outward-rounded Hermite caps and the Part 88 interval for $\log K_j=A_N-A_j-A_{N-j}-\log(2N)$. Printed integers round down in units of $10^{-8}$. The GSA comparison uses the Part 93 convention at one-based row $i$.

```python
from pathlib import Path
exec(Path('docs/research/wall1_dual_pinning.md').read_text()
     .split('\n```python\n')[1].split('def ceildiv')[0])
def logH(d):
    return I.mpf(C[d])/(M*d)
def floorlogdet(j):
    K=A[n]-A[j]-A[n-j]-I.ln(2*n)
    return (-I.ln(6200)-K)/n
def floor8(x):
    return int((10**8*x).a)
assert I.mpf(61)/6200 < I.mpf('.01')
for b in (406,506):
    k,z=n-b,b-1
    r=k+1
    U=k*r*(logH(b)/z+I.ln(I.mpf('1.01'))/(k-1))
    head=I.exp((floorlogdet(z)-U)/r)
    logv=(U+k*logH(b))*b/n
    logD=logH(b)+(b-1)*logv/b
    S=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*z)
    def target(i):
        return I.mpf('.85')*I.exp((n+1-2*i)*S)
    print(b,'head',floor8(head),floor8(head/target(r)))
    for j in range(60):
        F=floorlogdet(j) if j else 0
        R=I.exp(-logH(z-j)+(F-logD)/(z-j))
        ratio=R/target(n-j)
        assert ratio > 0
        if j in (0,9,29,59):
            print(j,floor8(R),floor8(ratio))
    K=A[n]-A[z]-A[n-z]-I.ln(2*n)
    solo=I.exp(((-I.ln(101)-K)/n-U)/r)
    print('head only',floor8(solo),floor8(solo/target(r)))
    assert head < solo < target(r)
    assert all(I.exp(-logH(z-j)+((floorlogdet(j) if j else 0)-logD)/(z-j))
               < target(n-j) for j in range(60))
    L=I.sqrt(n/(2*I.pi*I.exp(1)))*I.exp(I.ln(I.mpf('.0199'))/n)
    qhead=I.exp((z*(I.ln(L)-logH(z))-U)/r)
    print('graph',floor8(qhead),floor8(qhead/target(r)))
```

## Audit note (Nov 2026)

Independent audit: CORRECT WITH MINOR ISSUES. Every table entry reproduces, both from the embedded certificate and from an
independent 40-digit recomputation. The targets are the row-specific 0.85·GSA values. The 61-event joint accounting
(61/6200 < 0.01) and the oracle budget (≤ 60 exact SVP calls, all in dimension < b) are correct. Caveats:

* q-ary tail fractions are not printed in the note. The audit computed them for j = 0, 1, 9, 29, 59:
  * β = 406: 0.5200, 0.5154, 0.4755, 0.3774, 0.2522.
  * β = 506: 0.6176, 0.6140, 0.5817, 0.4977, 0.3804.
* The head-only row is a per-width (1/101) statement, not a joint one.
* The tail fractions rise partly because the GSA line is a poor, low model for the last ~β rows.
* The extra dual SVP calls are assumed exact. δ-approximate calls would divide the tail bounds by δ.
