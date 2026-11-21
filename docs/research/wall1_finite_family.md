# Finite families of terminal projections

For the plain independent-matrix CBD(3) ensemble of Part 39, a single predetermined plane has an optimal **typical-rank RMS Gaussian-heuristic crossing at 641**. This is a geometric comparison, not a necessary condition for SVP recovery. A fixed family can beat 647 rigorously: there exists one of at most $2^{575}$ coordinate planes giving **over 99% recovery at dimension 600** by exhaustive selection. This is a width bound with an exponential number of calls. At dimension 406, any fixed family needs **at least 679 bits of log-cardinality** for 99% probability of even containing a plane passing the unique-terminal-pair criterion. This last result uses no Gaussian heuristic. It bounds the support size, not the conditional design information.

## Geometry of a predetermined rational plane

Use $d=1024$, $m=511$, $n=512$, $q=3329$, $u=(w,1)=(e,s,1)$ and the syndrome $D_A(x,y,t)=x-te+A(y-ts)$ modulo $q$. For a prefix plane of dimension $k=d-D$ put $S=P\cap\mathbb Z^d$, $T=S\bmod q$, $Q=\pi_{P^\perp}$, $G=Q\mathbb Z^d$. Saturation gives $\dim T=k$ and $G$ has determinant $1/\det S$ by completing a basis of $S$ to a unimodular basis and projecting the complement. The projected lattice is the kernel in $G$ of the induced surjection onto $\mathbb F_q^m/D_A(T)$. Thus
$$
 \det Q L_A=q^{m-\rho}/\det S,\qquad \rho=\dim D_A(T).
$$
Equivalently $[S:S\cap L_A]=q^\rho$. Using a nonsaturated generating sublattice of $q\mathbb Z^d$ changes neither the plane nor its projection. The rank need not be fixed by $P\cap q\mathbb Z^d$. For example deleting a single secret axis gives rank zero if its column vanishes and one otherwise.

For any fixed $Q$ the exact squared-length law assigns mass $64^{-1023}\prod_i\binom6{3+w_i}$ to the value $(w,1)^tQ(w,1)$ for each $w\in\{-3,\ldots,3\}^{1023}$, adding coincident masses. Its mean is $1.5D-0.5Q_{dd}$. Writing $B$ for the horizontal principal block and $v$ for the horizontal part of the last column, independence and the CBD fourth cumulant $-3/4$ give variance $4.5\operatorname{tr}(B^2)-0.75\sum B_{ii}^2+6\|v\|^2$ (the linear and quadratic terms are uncorrelated by symmetry). This includes oblique planes and loss of the embedding axis. For each planting, the exact competitor first moment sums the membership probabilities of all other signed quotient pairs in the closed projected ball, as in [Part 39](wall1_projected_reference.md). A first moment bounds failure from above.

For the typical rank claim, condition on $u$. With $Y=y-ts$, $X=x-te$, put $l=\dim Y(T)$, $a=\dim X(T\cap\ker Y)$. Then $a+l=k-\mathbf1_{\bar u\in T}$ and $\rho=a+\operatorname{rank} M$ for a uniform $(m-a)\times l$ matrix, by the independent-column argument in [the interior calculation](wall1_interior.md). The chance of nonmaximal matrix rank is at most $q^{-|m-a-l|}/(q-1)$ by union over projective kernel lines on the smaller side. For a predetermined plane, $\Pr(\bar u\in T)\le(5/16)^{D-1}$: impose the $D$ linear constraints on the horizontal variables at height one and solve for at least $D-1$ independent pivot coordinates. Each specified residue has mass at most $20/64$. Thus except for these explicit events the rank is $\min(m,k)$.

At that rank the largest possible GH radius is
$$
 g_D=\exp\big((\max(D-513,0)\ln q+\ln\Gamma(1+D/2))/D\big)/\sqrt\pi .
$$
Indeed $\det S\ge1$ by integral minors. The smallest possible RMS radius is $\sqrt{1.5D-0.5}$. Both extrema are attained together by horizontal coordinate prefixes on the maximal-rank event (for $k\le511$ one can use sample axes with deterministic rank). The RMS here uses the unconditional plant law. Scanning integer $D=1,\ldots,1024$ with these two formulas gives the first strict crossing at 641. At 406, 640 and 641 the pairs (GH, RMS) are respectively (4.919, 24.668), (30.789, 30.976) and (31.127, 31.000). There is no single analogous minimum for a realized planting and a rare rank defect. GH neither bounds the first minimum from above nor excludes a short marked vector when the comparison fails.

## A finite family below 647

Allow deletion of any $424$ horizontal coordinates, retaining $599$ and the height. Let $i$ deleted coordinates be secret axes; the other $424-i$ are sample axes. Eliminate the deleted samples. In the $87+i$ remaining sample equations quotient out the span of the $i$ deleted secret columns. These columns have full rank except with probability at most $q^{-87}/(q-1)$. Conditional on full rank their span is uniform and independent of the other columns. The projected lattice consists exactly of the retained integral tuples satisfying the residual syndrome modulo that span, with covolume $q^{87}$. Every solution extends; the deleted secrets are unique modulo $q$ by full column rank, then the deleted errors are determined. Centering recovers the original CBD lift for the plant.

Fix a plane and planting with retained squared radius at most 345. For a competing tuple with nonzero retained secret discrepancy modulo $q$, membership has probability $q^{-87}$ given full rank. For zero secret discrepancy and nonzero sample discrepancy it is $(q^i-1)/(q^{87+i}-1)\le q^{-87}$. Both discrepancies zero forces an integral multiple of the plant since $\sqrt{345}\sqrt{10}<q$. The height excludes any competing such multiple. Consequently the conditional first moment is at most $N_{600}(345)q^{-87}/2<2^{-30}$. For a reproducible upper bound use
$$
 N_D(J)\le e^{tJ}(1+2\sum_{j\ge1}e^{-tj^2})^D,\qquad t=D/(2J).
$$
At $(600,345)$ the base-two log before division by two and after subtracting $87\log_2 q$ is below $-29.20$ (sum through 20 and bound the remaining series by $e^{-441t}/(1-e^{-43t})$).

The strict first-moment inequality can also be checked entirely with integers. Put $z=21/50$, $C=1+2\sum_{j=1}^4z^{j^2}+2z^{25}/(1-z^{11})$. The tail bound follows from successive square gaps at least 11. Cross multiplication gives $2^{29}C^{600}<z^{345}3329^{87}$.

With probability above $1-0.003073-0.000838$, the horizontal plant has at least 280 zeros and 430 entries of absolute value one. The two bounds are binomial CDFs through 279 and 429 with 1023 trials and probabilities $20/64$ and $30/64$. A uniform 599-subset then has probability at least
$$
 f=\binom{280}{255}\binom{430}{344}/\binom{1023}{599}>2^{-572}
$$
of retaining exactly the indicated 255 zeros and 344 unit entries, giving squared radius 345 including height. Sample $2^{575}$ subsets independently once. The probability that none qualifies on such a plant is below $e^{-8}$. By averaging there is a fixed family with joint plant miss probability below $0.003911+e^{-8}$; duplicates can be discarded. The entire coordinate family is an explicit alternative. Conditional on the plant, choose the first qualifying subset for the proof. This witness is independent of the design, so its rank and first-moment bounds apply directly.

For an observable selector, solve each terminal SVP, orient height-one outputs and lift them on full rank, keeping the shortest candidate in the ambient norm. One may require a unique terminal pair on each accepted plane by enumerating the closed ball at its first minimum. A successful witness contributes the plant. Ambient ambiguity costs less than $2^{-1900}$ for these parameters by the ambient uniqueness estimate of [Part 36](wall1_lower_bound.md) (or apply the ambient integer-ball bound at the actual radius). Hence recovery exceeds 99%. The alternative explicit family has $\binom{1023}{599}<2^{996}$ members. Neither count is a lower bound on the calls needed. This proof controls a good witness, not the worst fixed-plane failure. It does not certify a single inexpensive reduction trajectory.

## A rigorous small-family obstruction at 406

Here $k=618$. Even conditional on any plant, $a+l\ge617$. The rank estimate gives $\Pr(\rho<m\mid u)\le q^{-106}/(q-1)$. On full rank $QL_A=G$, which is deterministic. If $G$ has more than one shortest pair, the unique-pair criterion is impossible. Otherwise fix its shortest pair $\pm g$. Each affine equation $Q(w,1)=\pm g$ specifies at least $D-1$ independent horizontal pivot coordinates after conditioning on the others. Thus for every fixed rational plane the unconditional criterion success is at most
$$
 s_* =2(5/16)^{405}+q^{-106}/(q-1)<2^{-678.61}.
$$
For any selector from $N$ fixed planes success is at most $Ns_*$ by the union bound; 99% requires $\log_2 N>678.59$ (679 whole bits). This argument allows unlimited selection computation. It concerns terminal uniqueness, not early capture. Applying binary divergence to success against the *unconditional* independent plane law likewise requires $I((A,U);P)\ge p\log_2(1/s_*)-H_2(p)$. This includes information about the plant.

## Limits of the information conclusion

For an arbitrary selector the union bound on failure is also valid, $p_{\rm fail}\le\sum_P\Pr(E_P)$, often sharper than the Part 38 relaxation. In Part 38 the reference averages the fixed-plane conditional failures with weights depending on $u$. A maximum of *unconditional* fixed-plane failures need not bound that reference. Controlling failure from above cannot by itself give a necessary information cost for success.

In particular, a plant-informed selector can have zero conditional design information even at 406. Whenever there is a horizontal one and a zero, use those two coordinates for a quotient normal $(1,2)$ in that order. From the unused coordinates choose 405 disjoint equal-value pairs and use normals $(1,-1)$ on them. There are at least $(1021-7)/2$ pairs by grouping by the seven possible values. Take $P$ perpendicular to these disjoint normals. In $G$ the orthogonal coordinate spacings are $1/\sqrt5$ and $1/\sqrt2$ respectively, by primitivity. The projection of the plant is one step on the unique shortest axis, so remains the unique shortest pair in every $QL_A\subset G$ containing it. The exceptional probability is at most $(49/64)^{1023}+(44/64)^{1023}$ by the one-coordinate masses. Deterministic tie choices make $I(A;P\mid U)=0$. This is a counterexample for the terminal criterion with plant side information; its quotient does not supply a lift algorithm. It also illustrates why the unconditional RMS calculation cannot be applied after plant selection.

Thus there is a strong cardinality barrier at 406 and a sharp predetermined-plane RMS benchmark, but neither proves a universal recovery threshold near 647 or a positive lower bound on conditional design information. Access to a good plane from public input at modest cost, and the selected-plane law of slide reduction, remain distinct open issues.
