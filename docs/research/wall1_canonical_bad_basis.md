# Canonical bad BKZ flags at Wall 1

A minimum-potential bad flag exists. On a Haar-generic lattice **every** fully BKZ flag is already isolated under reducedness-preserving changes supported on at most one window. Local minimality under these moves therefore gives zero additional discrimination among exact flags. A different way to remove completions, retaining just the primitive prefix **one column after the terminal cut**, improves the 99% absolute radius at widths 406 and 506 to **0.00765902** and **0.01703981**. None of the twelve GSA targets is certified.

## What a minimizing flag must satisfy

Use zero-based columns, rank $n$, width $b$, $k=n-b$, $L_j$ the primitive rank-$j$ prefix, $S_j=\log\det L_j$, and $g_j=\exp(S_{j+1}-S_j)$. Identify signs and choose size-reduced lifts. Minimize $\Phi=\sum_{j=1}^{n-1}S_j$ over all fully reduced flags with $g_k<\rho$. On a fixed lattice each nonzero exterior lattice vector has norm bounded below by a positive constant of its degree. Thus bounding $\exp\Phi$ bounds every individual prefix wedge norm. There are finitely many wedge choices in these balls, and a primitive wedge up to sign determines its saturated prefix. Any one bad flag supplies a finite nonempty sublevel set. A measurable tie break can enumerate integral changes of basis in a measurable lattice chart and take the first minimizer. [Basis multiplicity](wall1_basis_multiplicity.md)

Here is an explicit coefficient test even for moves longer than $b$. Let $G=B^tB$, $V\in GL_n(\mathbb Z)$, $D'_j=\det(V_{:j}^t G V_{:j})$, with $V_{:j}$ the first $j$ columns and $D'_0=1$. Write $D_j$ for the original prefix Gram determinants. If $D'_{k+1}<\rho^2 D'_k$ and $\prod_{j=1}^{n-1}D'_j<\prod_{j=1}^{n-1}D_j$, there must be a start $i$ and a nonzero integer $z$ of length $d=\min(b,n-i)$ such that
$$
z^t Q'_{i,d} z < D'_{i+1}/D'_i.
$$
Here $Q'$ is the trailing $d$-row Schur complement of the leading $i$-row block in the first $i+d$ principal minor of $V^t G V$ (the full minor for $i=0$). Indeed the right hand side is the squared candidate head and the quadratic form is the squared projected norm. Size reduction preserves all these projected lattices, head lengths and prefix determinants. Without the shorter vector the candidate would be an admissible strict improvement. Conversely testing the implication for every $V$ suffices for minimality among bad exact flags. For insertion of $b_t$ at $s<t$, the potential comparison is the product of $\|\pi_j b_t\|/g_j$ for $s\le j<t$, with $\pi_j$ projecting off $L_j$. For $t-s+1\le b$ every factor is already at least one.

**Local rigidity.** Fix endpoints $L_s,L_t$ with $t-s\le b$. Any exact BKZ completion induces an HKZ flag in $\pi_s L_t$. At every intermediate start $i$ the original SVP test remains true when its right endpoint is truncated to $t$. The truncated test chooses a shortest line and the same argument applies recursively in its quotient. For fixed endpoints this determines all intermediate prefixes whenever each shortest line is unique. Almost surely this holds simultaneously for every integral flag and subquotient: a tie between independent projected lines is a nonidentical polynomial equation on a positive definite Gram form after clearing the prefix determinant. To see nonidentity choose a form making the prefix orthogonal to the two independent quotient directions and give the directions unequal norms after accounting for the chosen representatives. Scaling preserves equality and allows determinant one. Take the countable union. Distinct primitive lines cannot be collinear in the quotient lattice.

Consequently *any* two exact flags agreeing outside the interior of such an interval agree everywhere, irrespective of their potentials or terminal cuts. The same holds for a succession of such moves through exact flags. A repair that passes through nonreduced bases and changes several windows has only the global implication above. Ties can allow choices on exceptional lattices. Haar genericity here supplies no tie statement for the discrete $q$-ary ensemble.

**Why Rankin optimality fails.** In rank three take an orthogonal sum of a line of length $0.99$ and a unit triangular lattice. At full width every reduced flag starts with the line, and its rank-two prefix has area $0.99$. The triangular summand is primitive of area $\sqrt3/2<0.99$. Set $\rho$ above the first length (or rescale both lattice and threshold to unit determinant). Every such flag is bad, including the minimizer. Replacing its plane by the smaller plane forces a nonshortest first vector. The strict area and first-length gaps persist under small perturbations. Moreover in any rank every strictly increasing positive diagonal profile with product one and $g_k<\rho$ occurs as a global potential minimum on its rectangular lattice. Cauchy–Binet bounds each rank-$j$ integer prefix volume below by the product of the first $j$ diagonal lengths, since at least one integer minor is nonzero. The coordinate flag attains all bounds simultaneously and passes BKZ. These examples rule out deterministic pinning to a narrow GSA shape by local minimality. They do not quantify Haar concentration. Part 64's single dip describes its finite search outputs. [Bad-basis experiment and audit](wall1_bad_bases_experiment.md)

## Residual at the requested cuts

Use $n=1023$ and the determinant-one GSA benchmark $G_b$ of Part 71. The coefficient implication for short moves supplies no independent acceptance factor. We reran the Part 82 oriented weighted relaxation with its audited paper inputs. The second column group below is a separate multiplicity-free count *per primitive line*: keep only $S_1\le U_1$ of the candidate. It is an especially coarse relaxation, included to quantify how much even this single necessary condition overcounts. Each group lists the three cuts $\rho/G_b=0.25,0.50,0.85$ in order. All logarithms are natural.

| Width | Weighted log integral, certified lower endpoints | Log mean of admitted primitive lines, enclosures |
|---:|---:|---:|
|406|795649, 810482, 812882|[2910,2914], [2920,2924], [2921,2925]|
|506|558869, 575806, 580225|[2176,2180], [2186,2190], [2187,2191]|
|647|360659, 375575, 380478|[1504,1508], [1515,1519], [1518,1522]|
|800|218002, 234985, 241200|[1075,1079], [1079,1083], [1080,1084]|

The weighted lower endpoints concern the relaxed integrand alone. Imposing exact overlapping BKZ tests or the long-move implication inside the integral can decrease it. The integral with the exact unique selector, unfolded modulo signs, equals the bad-event probability and is at most one. None of the positive log lower endpoints applies to that quantity. Removing signs from the oriented integral subtracts $1022\log 2$. The closest primitive-line first moment still misses the $-\log 100$ log target by more than 1079 nats. [Haar normalization](wall1_volume_method.md) · [Profile boxes](wall1_surviving_mass.md) · [Weighted integral](wall1_small_d_caps.md)

## Counting one primitive prefix after the cut

Use the upward Part 71 envelope $U$, with a dent at $k$. Away from row $k$, a minimizing width in the recurrence gives the reverse of the necessary facet inequality $dS_{i+1}\le(d-1)S_i+S_{i+d}+H_d$. Thus a positive maximum of $S-U$ at $i+1$ forces the same maximum at $i$. At $k+1$ the same propagation holds if the absolute cut is violated at radius $\exp(U_{k+1}-U_k)$; it also holds if the relative cut is violated at radius $\exp(U_{k+1}-(1-1/b)U_k)V_b^{1/b}$, since $\det(\pi_k L)=\exp(-S_k)$. The endpoints agree. Either violation therefore implies $S_j\le U_j$ at every rank. An undented supersolution uses ordinary propagation everywhere.

Count the unsigned primitive rank-$j$ sublattices satisfying this one bound. Integration of the Part 65 split density gives the exact log mean of this relaxed count,
$$
 A_n-A_j-A_{n-j}+nU_j-\log(2n),\qquad A_d=\log K_d .
$$
It applies for **arbitrary** $1\le j<n$: the projected blocks need no internal BKZ tests in a primitive-sublattice count. In particular, one may discard all intermediate cuts even when a resulting piece exceeds $b$. Dropping cuts need not increase the first moment because many nested chains map to the same prefix. For the radius certificate take $j=k+1$, so that the cut directly controls the retained covolume. For each width separately, with probability greater than 0.99 every fully BKZ basis obeys **both** lower bounds in its row. $R_T=(\det(\pi_k L)/V_b)^{1/b}$. [Primitive split formula](wall1_one_sided_terminal.md)

| Width | Dent in billionths | $g_k$ lower | $g_k/R_T$ lower | Log failure upper |
|---:|---:|---:|---:|---:|
|406|5496787725|0.00765902|0.00572169|−4.6413|
|506|5007519720|0.01703981|0.00924937|−4.6383|
|647|4504578931|0.04255794|0.01517094|−4.6112|
|800|3662797435|0.15090292|0.03498389|−4.6112|

The gain at the first two widths comes from discarding internal flags. Part 82 already uses this single cut at the last two widths. At the requested targets the same rank-$k+1$ log means, in increasing order of $c$, lie in $[h-4,h]$ with upper endpoints $(712900,723456,724927)$, $(549464,561919,564578)$, $(343828,356166,359439)$, and $(152729,165703,169566)$. Distinguishing the prefixes that admit an exact bad completion would require a bound on the simultaneous crossing tests or on admissible longer changes of flag. The fixed-width cubic growth theorem in the multiplicity note has no corresponding proved cubic rate for these proportional widths. The Haar-to-$q$-ary step also remains open. [Wall 1 frontier](../PROOF_GAP.md)

## Interval certificate

Run the following Python from the repository root with NumPy and mpmath. The full Part 82 block reproduces the weighted rows, including its integer slack and interval quadrature. The new evaluations reuse its upper recurrence. The LCZ rational witnesses are checked by the inherited code; the LP density bounds have the published-input status specified in Part 82. The three-point decimals below are the outward bounds from Table 1.1. The choices of cuts and dents came from a search; only the displayed witnesses enter the proof. [Cohn, de Laat and Salmon, Table 1.1](https://arxiv.org/pdf/2206.15373)

```python
from pathlib import Path

path = Path("docs/research/wall1_small_d_caps.md")
body = path.read_text().split("\n```python\n", 1)[1].split("\n```", 1)[0]
marker = "for d,s in dens.items():"
paper = """dens.update(zip([4,5,6,7,*range(9,17)],
    ".636108 .512646 .410304 .321148 .191121 .143411 .106726 .079712 .060165 .045062 .033757 .024995".split()))
"""
assert body.count(marker) == 1
exec(body.replace(marker, paper + marker))
C = lattice.copy()

def prefix(v, j):
    return I.mpf(n*sum(v[:j])-j*sum(v))/(n*M)

def log_mean(v, j):
    return A[n]-A[j]-A[n-j]+n*prefix(v,j)-I.ln(2*n)

rows_new = [
    (406,5496787725,765902,572169,"-4.6413"),
    (506,5007519720,1703981,924937,"-4.6383"),
    (647,4504578931,4255794,1517094,"-4.6112"),
    (800,3662797435,15090292,3498389,"-4.6112"),
]
for b,t,absolute,relative,log_upper in rows_new:
    k = n-b
    v = profile(b,t,True)
    gh = I.exp(I.loggamma(1+I.mpf(b)/2)/b)/I.sqrt(I.pi)
    x = coords(v,k)
    assert I.exp(x) >= I.mpf(absolute)/10**8
    assert I.exp(x+prefix(v,k)/b)/gh >= I.mpf(relative)/10**8
    assert log_mean(v,k+1) < I.mpf(log_upper) < -I.ln(100)
    G = I.exp((2*b-n-1)*(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1)))
    for c in [".25",".50",".85"]:
        v = solve(b,I.mpf(c)*G,True)
        print(b,c,[(flooriv(z),ceiliv(z)) for z in
                   (log_mean(v,1),log_mean(v,k+1))])
```
