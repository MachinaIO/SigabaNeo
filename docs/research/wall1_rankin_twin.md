# What a Rankin test buys at the terminal cut

For the terminating Part 88 predicate the scalar extension cap is **sharp**, including its exponent and constant for the specified twin factors. For a stronger predicate, one extra minimum-area plane test in the shifted dual raises the 406 certificate from 0.12565615 to 0.26256097. It gives no certified gain at 506 with the plane cap below. This is a small *selected rank* (two), but the search dimensions are 617 and 517. No width-budgeted algorithm achieving this gain follows.

All entries below concern covolume-one Haar lattices in dimension 1023. Lower radii round down. Each holds with probability at least 0.99 simultaneously over passing bases at its fixed width, with an exact terminal SVP test. For a strengthened predicate the statement alone gives no probability of finding a passing basis.

| $b$ | Part 88 with sharpened caps, 1% | Plus dual plane test | Exact primal and shifted dual SVP | Upper ceiling for exact twin scalar method |
|---:|---:|---:|---:|---:|
|406|0.12565615|0.26256097|0.28191739|0.38502239|
|506|0.36242601|0.36242601|0.37809585|0.51838596|

The comparisons are 0.36920 and 0.81632. Part 88 originally obtained 0.12531282 and 0.36188705. The first column implements the later finite Hermite caps. The exact SVP column uses rank $k=n-b$ oracles on the named twin blocks. Exact SVP on the ordinary width-$b$ blocks of a slide tour does not imply this property. For the different predicate testing both orientations at **every** width-$b$ window, Part 86 propagates the endpoint inequalities directly. [Part 88](wall1_li_walter.md) · [finite Hermite caps](wall1_hermite_caps.md) · [Part 86](wall1_dual_pinning.md)

## A sharp determinant implication for the existing algorithm

Put $r=k+1$, $P=L_r$, $W=L_k$, $D=\det P$, $q=D/\det W$, and let $x$ be the first length. The shifted reversed dual is the lattice $B=P^*\cap b_1^\perp$ in the span of $P$, of determinant $x/D$. Its named normal has length $1/q$. Write $A,B_0$ for primal and dual HSVP factors. Then
$$x\le A(D/q)^{1/k},\qquad 1/q\le B_0(x/D)^{1/k},
\qquad D^{1/r}/q\le T=(A B_0^k)^{k/(k^2-1)}.$$
The last inequality follows by substitution. For $K_r$ the primitive extension coefficient in Part 88, Markov gives radius $S/T$ where $S=(.01/K_r)^{1/(nr)}$. This counts extensions once, without selecting an independent Haar quotient.

Sharpness for the stated HSVP tests has an elementary witness. Set $q=1$, $D=T^r$, $x=A D^{1/k}$, and take orthogonal basis lengths $x,(D/x)^{1/(k-1)},\ldots,(D/x)^{1/(k-1)},1$ in $P$. Both inequalities are equalities. Append $n-r$ orthogonal axes of length at least one for terminal SVP and rescale the whole lattice to determinant one. The ratio and all tests survive rescaling. Hence even an exact Rankin inequality, or Minkowski’s second theorem applied with all its hypotheses, cannot reduce the uniform $T$ for these tests. This is sharpness for the output predicate. The diagonal example need not occur on a reducer trajectory. Part 90 separately bounds the gain from shape filtering the actual first moment for its numerical factors. [Part 90](wall1_selfdual_sharpen.md)

## Exact lines and selected planes

Use the squared-covolume convention $\gamma_{d,j}=\sup_L \min_U (\det U)^2/(\det L)^{2j/d}$ over rank-$j$ primitive sublattices. Thus $\gamma_{d,1}=\gamma_d$. Exact SVP in $W$ and in $B$ permits $A=B_0=\sqrt{\gamma_k}$ in the formula above. A shortest first vector and a shortest last dual vector on the *same* block also bound its two endpoints by Hermite, with the same determinant in the two tests. More explicitly, on a projected block of rank $d$, determinant $v$ and endpoint heights $u,w$, one gets $u^d/\gamma_d^{d/2}\le v\le w^d\gamma_d^{d/2}$. For both orientations on every width-$b$ window, the Part 86 recurrence using all inherited shorter tests already certifies radii 0.12656799 and 0.36551297 with its original caps. Neither condition identifies an arbitrary intermediate prefix as a minimum-determinant sublattice. For instance, in dimension four use orthogonal basis lengths $1,H,1,H$ with $H>1$. Both endpoints are shortest in their respective orientations, yet the prefix plane has area $H$ and the minimum area is one. Minkowski’s theorem controls products of successive minima, which also requires an argument connecting those minima to the named flag.

Instead impose this additional test on $B$: the named normal belongs to a primitive minimum-area plane and is a shortest vector in that plane. The latter check is binary Gauss reduction. It follows that
$$q^{-1}\le \sqrt{\gamma_2}\,\gamma_{k,2}^{1/4}(x/D)^{1/k}.$$
Indeed the plane has area at most $\sqrt{\gamma_{k,2}}(\det B)^{2/k}$ and binary Hermite bounds its squared minimum by $\gamma_2$ times that area. Retain the smaller of this HSVP factor and the algorithm's factor. An exact plane minimizer is sufficient. An observed plane through the normal with area below the same certified threshold and with the same binary shortest test suffices as well. HKZ restricted to the two-plane supplies the binary test only.

For reproducibility the finite upper bound used here is
$$\gamma_{d,2}\le \gamma_d^{(d-2)/(d-1)}\gamma_{d-1}.$$
Take a shortest primitive line of length $l$ and lift a shortest projected vector back to the lattice. Their plane has squared area at most $l^2\gamma_{d-1}(\det L/l)^{2/(d-1)}$. Apply Hermite to $l$. This also proves the bound for the first plane of a primal HKZ basis irrespective of whether that plane minimizes area. Use $\gamma_2=2/\sqrt3$ and the finite Part 86 upper caps in the two high dimensions. The resulting upper bounds on the squared-area constants are 4586.502 at $d=617$ and 3278.056 at $d=517$, rounded upward. Duality gives $\gamma_{d,j}=\gamma_{d,d-j}$ by primitive annihilators. The more general nested-subspace inequality is $\gamma_{d,i}\le\gamma_{d,j}^{i/j}\gamma_{j,i}$ for $i<j$, obtained by minimizing twice. These inequalities concern existence unless a selection condition is supplied. I found no independently certified numerical record for $\gamma_{517,2}$ or $\gamma_{617,2}$ establishing the best published finite upper bound. Optimality of the explicit bounds used here is unverified. The exact low-dimensional results and the literature on $\gamma_{2j,j}$ do not supply those values. [Bounding basis reduction properties](https://doi.org/10.1007/s10623-016-0273-9) · [About the Rankin and Bergé-Martinet constants](https://arxiv.org/abs/2501.08105) · [Wen–Chang](https://arxiv.org/abs/2204.08021)

## Limits of the method

For the specified 1% HSVP predicate and fixed certified factors the first column is the exact optimum of the uniform scalar-cap calculation, up to rounding. For exact twin SVP one can bracket the optimum without assuming that two extremal Hermite shapes fit together. Choose any unit-covolume $P^*$ and a shortest normal in it. Its kernel in $P$ defines $W$; choose a shortest first vector of $W$. The named normal remains shortest in the shifted dual containing it. Complete the primitive flag, size-reduce, append sufficiently long perpendicular axes and rescale as above. This realizes $D^{1/r}/q=\lambda_1(P^*)$ before and after rescaling. Consequently the optimal $T$ for these exact twins lies between $\sqrt{\gamma_r}$ and $\gamma_k^{k/(2(k-1))}$. The lower endpoint is the exact optimal cap for the different test requiring the normal shortest in the whole of $P^*$, by the same construction. The scalar Markov method for either predicate therefore cannot exceed $S/\sqrt{\gamma_r}$. The primitive unoriented line mean in a unit lattice is $V_r t^r/(2\zeta(r))$. Below mean one there exists a lattice avoiding the ball, giving $\sqrt{\gamma_r}\ge(2/V_r)^{1/r}$ by taking limits. This yields the upward-rounded ceilings in the table. The 506 target is excluded even with perfect Hermite constants under these predicates. The 406 ceiling leaves its target open. [Primitive incidence normalization](wall1_li_walter.md) · [full-dual predicate](wall1_combined_reducer.md)

Changing the predicate can change the extremal problem. For instance the shortest normal of an arbitrary $P^*$ need not lie in a minimum-area plane of its shifted dual. The exact-twin ceiling is not proved here for that extra test. For arbitrary combinations of normalized shortest-flag tests admitting the orthonormal cubic basis, the common ceiling is $S$ since that basis forces $T\ge1$ (here $S<2.33287056,2.87913632$, respectively). A tighter universal optimum needs a specified class of allowed tests and passing or existence requirements. None of these deterministic ceilings bounds an actual output quantile or transfers the Haar statement to a finite modular ensemble. [Wall 1](../PROOF_GAP.md)

## Interval verification

Run from the repository root. The imported Part 86 setup uses interval arithmetic for the ball and zeta normalization and integer upper caps for Hermite. The endpoint assertions certify both the down-rounded radii and the up-rounded ceilings.

```python
from pathlib import Path
src=Path('docs/research/wall1_dual_pinning.md').read_text()
exec(src.split('\n```python\n')[1].split('def ceildiv')[0])
for b,H in [(406,'775.869497700'),(506,'1019.379685531')]:
    k=n-b
    r=k+1
    K=A[n]-A[r]-A[n-r]-I.ln(2*n)
    S=I.exp((-I.ln(100)-K)/(n*r))
    def h(d): return I.mpf(C[d])/(M*d)
    a=(k-1)*I.mpf(H)/(b*(b-1))+I.ln(I.mpf('1.01'))
    # shortest line in a minimum-area plane of the shifted dual
    p=(I.ln(I.mpf(4)/3)/4
       +((k-2)*h(k)/(k-1)+h(k-1))/2)
    assert I.exp(2*((k-2)*h(k)/(k-1)+h(k-1))) < I.mpf('4586.502' if b==406 else '3278.056')
    def R(x,y): return S*I.exp(-k*(x+k*y)/(k*k-1))
    def V(d): return I.exp(d*I.ln(I.pi)/2-I.loggamma(1+I.mpf(d)/2))
    vals=[R(a,a),R(h(k),h(k)),R(a,min(a,p)),S*(V(r)/2)**(I.mpf(1)/r),S]
    print(b,[int((10**8*v).a) for v in vals])
    assert (p<a if b==406 else p>a)
    expected={406:[12565615,28191739,26256097,38502238,233287055],506:[36242601,37809585,36242601,51838595,287913631]}[b]
    for v,j in zip(vals,expected): assert j < 10**8*v and 10**8*v < j+1
```

## Audit note (Nov 2026)

Independent audit: CORRECT WITH MINOR ISSUES. All numbers reproduce, including an independent mpmath rebuild, and rounding goes
the safe way. The sharpness example (i) and the ceiling construction (iv) were verified, and the Markov count stays a valid first
moment for every stronger predicate. Scope caveats:

* The plane-test and exact-twin columns are statements about a predicate. They need rank-617 / 517 conditions, above β, and no
  width-β algorithm is known to output them.
* The "observed plane below threshold" variant can be checked in polynomial time once a witness plane is given. Exact SVP on B
  always produces such a witness, so this variant is no stronger than the exact-twin predicate (0.2626 < 0.2819).
* The ceiling column is deterministic, rounded up, and not a 99% statement.
* Column 1 requires the implementation's η to use a Hermite value no larger than the new caps.
