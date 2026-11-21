# Basis multiplicity at Wall 1

At rank 1023 the terminal cut retains an enormous absolute first moment. There is a measurable source of overcounting: at width 800 and quarter GSA, counting each eligible primitive prefix once gives log mean **at most 152955**, while the Part 82 weighted upper-bound integral has log **at least 218002**. This gap of 65047 nats does not identify the number of bases of a typical lattice. In particular, the V7 and W2 factors are upper bounds on conditional survival. A lower bound on their integral need not witness even one genuinely surviving basis.

## Uncut versus bad mass

Use the oriented normalization of [Part 50](wall1_volume_method.md), the integer cap array of [Part 82](wall1_small_d_caps.md), and the negligible-boundary convention for size reduction. Write $J$ for profile mass with the full coefficient cube and $J_w$ for the Part 82 upper integral with width-three, optimized disjoint truncated V7, and W2 weights. All entries below are outward bounds in natural logs. The last two columns compare the **same** weighted integral with and without the terminal cut.

| width | uncut log J | uncut log J_w | log$J_w,total / J_w,bad$, .25 GSA | same, .85 GSA |
|---:|---:|---:|---:|---:|
|406|[820291,833098]|[812882,833098]|[0,37449]|[0,20216]|
|506|[587619,600415]|[580225,600415]|[0,41546]|[0,20190]|
|647|[388236,401016]|[380478,401016]|[0,40357]|[0,20538]|
|800|[249621,262396]|[241200,262396]|[0,44394]|[0,21196]|

For the unweighted integral at width 800 the quarter-cut upper endpoint 248264 is strictly below the uncut lower endpoint: the log gap is in [1357,37811]. Thus a small *additive* gap of order one cannot explain even these two unweighted masses. The bounds permit exponentially small bad fractions. For an indicator-defined relaxation with count $X$, unfolding measures lattices with weight $X$. Knowing its first moment cannot distinguish rare high counts from typical high counts. A second moment or direct control of the count distribution is needed. The basis searches in [Part 64](wall1_bad_bases_experiment.md) sample algorithm outputs with unknown selection probabilities.

**Certificate.** In the [Part 71](wall1_surviving_mass.md) recurrence take dent zero, width $b$, and the Part 82 cap table. The inward vector $v$ reserves $4d\epsilon$ per facet and limits each adjacent drop to .055. Independently perturb its first 1022 logs by at most $\epsilon=10^{-6}$, then recenter all 1023 logs. The facet error is at most $2(d-1)\epsilon$, the prefix volume is $(2\epsilon)^{1022}/1023$, and the score loss is below 2. The outward vector gives dominating centered prefix sums by the Part 77 maximum principle. Integrate its containing orthant. For the weighted lower bound take the explicit .85 replacement box of Part 82, which remains feasible without a cut. Weights are bounded by one. The comparisons subtract the Part 82 bad lower endpoints from the uncut upper endpoints. These calculations inherit the cap-input provenance caveat in the Part 82 audit.

## Exact reduced bases under Haar measure

Count modulo column signs, with the nearest-plane size-reduced representative of each primitive flag. Unfolding gives the exact mean
$$
 {K_n\over 2^{n-1}}\int e^{2\sum S_i}
 \int_{[-1/2,1/2]^{\binom n2}}\prod_i
 {\bf1}\{\lambda_1(B^{\rm proj}_{[i,\min(i+b,n))})=g_i\}\,d\mu\,dS .
$$
At full width it equals one: recursively the shortest primitive line in every quotient is unique almost surely. For each fixed primitive prefix and distinct projected lines, equality of squared lengths is a nonidentical algebraic condition on the Gram matrix (clear the prefix Gram determinant). Countably many null sets cover all ties, including half-integer lift ties. At smaller widths the product couples overlapping windows.

At width two one can integrate exactly up to one-dimensional quadrature. Put $a_j=j(n-j)$, $r_j=g_j/g_{j-1}$. Size reduction and the planar Gauss criterion give $r_j^2+\mu_{j-1,j}^2\ge1$. In adjacent log ratios the prefix-coordinate Jacobian is $1/n$ (the type A Cartan determinant is $n$). The sign-divided Haar mean is therefore
$$
 {K_n\over n2^{n-1}}\prod_{j=1}^{n-1}
 {2\over a_j}\int_0^{1/2}(1-u^2)^{-a_j/2}\,du .
$$

| rank | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| mean BKZ-2 flags |[1.003,1.005]|[1.024,1.026]|[1.090,1.093]|[1.264,1.269]|[1.709,1.719]|[2.964,2.989]|[7.459,7.554]|[31.625,32.211]|

For reproduction, use mpmath.iv at 40 decimals, the 2048 equal left/right rectangle sums on [0,1/2] (increasing integrand), and bound the zeta tail after 256 terms by the integrals from 257 and 256. Rank two equals one exactly. For any larger width these entries also bound the mean from above by inclusion.

**Growth depends on the width regime.** For each *fixed* $b\ge2$ the log Haar mean of exact BKZ flags is $\Theta_b(n^3)$. For a direct lower bound set $q=(1+.3^2)^{-1/(4b)}$, take all ratios in $[q,\sqrt q]$, and adjacent coefficients in [.3,.4]. In any window a vector with last nonzero coordinate at offset $l>0$ has squared length at least $4g_{i+l}^2$ if that coefficient has magnitude at least two. For magnitude one the preceding row has residual at least .3, giving at least $(1+.3^2)q^{2l}g_i^2>g_i^2$. This is an actual feasible coefficient box. Its log volume costs $O_b(n+\log n)$, and its minimum score is at least $|\log q|\sum_j a_j/2$. Stirling gives $\log K_n=-O(n^2\log n)$. The matching order upper bound follows from the width-two ratio floor and orthant integration in the log ratios. Kim and Venkatesh study concentration for Siegel-reduced bases and discuss the cubic log mean for LLL. Their concentration result does not cover the BKZ windows here. [Original paper](https://arxiv.org/abs/1608.00767)

For $b/n$ bounded away from zero this lower box loses to the normalization. The exact integral and the flag upper bounds below leave $\exp(\Theta(n^2))$ growth for a fixed fraction strictly between zero and one unresolved.

### Exhaustive finite examples

For a reproducible example let the rational Gram matrix be $G/100000$, with indices starting at zero, diagonal $100001+i$, and off-diagonal $6(((43(i+j+1)+71(i+1)(j+1))\bmod601)-300)$. Take leading principal blocks of ranks 3 to 5. The following counts exhaust all flags, including all clean-tour fixed points under exact tests. These chosen lattices are not Haar draws.

| rank | width 2 | width 3 | width 4 | width 5 or full if smaller |
|---:|---:|---:|---:|---:|
|3|2|1|—|1|
|4|3|2|1|1|
|5|5|2|2|1|
|8 (4+4)|9|4|1|1|
|10 (5+5)|25|4|4|1|

Gershgorin bounds every projected coordinate Schur complement between .955 and 1.0451 times identity (use the variational minimum over prefix coordinates). In remaining rank $r\le5$ the adjacent floor and determinant give $g_i^2\le1.0451(4/3)^{(r-1)/2}<2(.955)$. Thus every next projected head is a signed coordinate vector, inductively. In each window all vectors with two or more units of squared coordinate norm exceed every coordinate minimum. For each permutation and each prefix set $P$, compare the principal minors $\det G_{P+j}$ over the next $b$ entries: accept iff the first is smallest, allowing ties. This integer test uses the common denominator $\det G_P$. Size reduction gives a unique lift up to signs (the small off-diagonals put the coordinate lifts strictly inside the cell).

For the last two rows take an orthogonal sum of two copies with the second scaled in length by $D=10^{10}$; homothetic determinant normalization preserves all tests. Before the first column involving the second summand, any primitive prefix of the first has determinant at least $.955^{m/2}$ for summand rank $m$ by Cauchy–Binet. The first mixed column has projected length at least $\sqrt{.955}D$; the adjacent floor forces every remaining length to be at least $(\sqrt3/2)^9\sqrt{.955}D>D/4$. If it arrived early there would be at least $m+1$ such lengths, contradicting total determinant at most $1.0451^m D^m$. The first summand is therefore exhausted, and crossing tests reduce to those of its truncated tail because every nonzero second component is longer. Counts multiply. This construction tests exhaustiveness and exhibits multiplicity without extrapolating a Haar growth rate.

## Canonical witnesses and their cost

Let $\Phi=\sum_{j=1}^{n-1}\log\det L_j$ on sign-divided flags. Among exact bad flags choose a minimizer, breaking ties by a measurable ordering. Sublevel sets are finite on a fixed lattice: each exterior lattice bounds its nonzero wedge norms away from zero, so a product bound bounds every primitive prefix wedge separately. The selected count equals the existence indicator. For each integral unimodular move followed by size reduction one obtains the necessary disjunction “candidate fails a BKZ or terminal test, or $\Phi'\ge\Phi$.” For insertion of column $t$ at $s<t$ this last condition is
$$
 \prod_{j=s}^{t-1}(\|\pi_j b_t\|/g_j)\ \ge 1,
 \qquad \|\pi_j b_t\|^2=g_t^2+\sum_{h=j}^{t-1}\mu_{ht}^2g_h^2 .
$$
Indeed the changed prefixes replace their last column by $b_t$. Every insertion spanning at most $b$ columns already satisfies each factor inequality by the original SVP tests. Their extra suppression on exact bases is **zero**. For longer insertions one must check the alternative candidate's crossing windows and its terminal cut. Imposing the product inequality unconditionally would discard possible minima. Global HKZ minimization can change the bad terminal quotient.

A computable alternative is to identify bases by $W=L_k$, $k=n-b$. Its projected quotient has a shortest length independent of the completion. Choose a single bad exact completion per eligible $W$. For an upper bound, retain only $\log\det W\le u$ and $\lambda_1(\pi_W L)<\rho$. Here $u=U_k$ from the **cut** profile supersolution. By primitive disintegration the mean number of such unsigned prefixes is at most
$$
 \frac{K_n}{2nK_k K_b}e^{nu}
 \min(1,V_b\rho^b e^u/2).
$$
Indeed the split density in $s=\log\det W$ is $K_ne^{ns}/(2K_kK_b)$, the quotient has determinant $e^{-s}$ and normalized Haar shape, and Siegel on signed pairs bounds the conditional short-vector probability. This is the single-cut specialization of the [Part 65 primitive-chain method](wall1_one_sided_terminal.md). It also covers every profile-bad size-reduced basis since its terminal column supplies a short quotient vector without any BKZ assumption.

| width | log prefix mean upper, .25 GSA | same, .85 GSA | uncut log mean upper for **exact** BKZ flags modulo signs |
|---:|---:|---:|---:|
|406|714379|725613|814700|
|506|550400|564759|566694|
|647|344320|359418|359529|
|800|152955|169535|169910|

For the last column partition backward into consecutive pieces of width $b$ and a possibly shorter initial piece. Fixing this primitive chain fixes every internal flag of an exact basis almost surely: each projected piece is HKZ by truncation. For piece sizes $d_i$ and interior cuts $j$, write $a_j$ for the sum of the two neighboring sizes. Integrate the chain density over $S_j\le U_j$ from the uncut envelope. Dropping the chain orientation divisor gives the safe upper log bound
$$
 \log K_n-\sum_i\log K_{d_i}+\sum_j(a_j U_j-\log a_j).
$$
The trivial lower bound is one HKZ flag. Even the total exact mean upper at width 800 lies more than 47000 nats below the quarter-cut weighted residual after allowing for all $2^{1022}$ signs. This proves substantial slack between the exact and relaxed integrals, without quantifying how often a Haar lattice has any bad exact basis.

For a literal multiplicity statement, sample eligible prefixes with probability proportional to their counting intensity (normalize the measure on lattice–prefix pairs). At width 800 and quarter GSA the mean number of **sign-divided profile-bad** completions per sampled prefix is at least $\exp(224585-1022\log2-152955)>\exp(70921)$, by dividing the Part 82 unweighted bad lower bound by the prefix upper bound. This average gives neither a median nor a lower bound for the exact BKZ count.

### Reproducing the rank-1023 intervals

Execute the Part 82 Python block through the assignment of the lattice cap array inclusive, then the following. The recorded LCZ integer table can also be reused directly after its original certificate has been checked.

~~~python
for b in [406,506,647,800]:
    U = profile(b,0,True)
    v = profile(b,0,False)
    print(b, flooriv(A[n]+score(v)-2+(n-1)*I.ln(I.mpf(2)/10**6)-I.ln(n)),
          ceiliv(A[n]+score(U)-(n-1)*I.ln(2)))
    def prefix(V,j):
        return I.mpf(n*sum(V[:j])-j*sum(V))/(M*n)
    k = n-b
    cuts = [0]+list(range(k,0,-b))[::-1]+[n]
    sizes = [t-s for s,t in zip(cuts,cuts[1:])]
    z = A[n]-sum(A[d] for d in sizes)
    for i,j in enumerate(cuts[1:-1]):
        a = sizes[i]+sizes[i+1]
        z += a*prefix(U,j)-I.ln(a)
    print(ceiliv(z))
    G = I.exp((2*b-n-1)*(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1)))
    for c in ['.25','.85']:
        R = I.mpf(c)*G
        u = prefix(solve(b,R,True),k)
        z = A[n]-A[b]-A[k]+n*u-I.ln(2*n)
        p = b*I.ln(I.pi)/2-I.loggamma(1+I.mpf(b)/2)+b*I.ln(R)+u-I.ln(2)
        print(ceiliv(z+min(0,p)))
~~~
