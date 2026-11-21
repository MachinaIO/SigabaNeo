# What an information bound on prefix selection would prove

Fix the planted ensemble of [the finite-radius theorem](usvp_planted.md). Write
$U=(e,s,1)$, let $A$ be the uniform design independent of $U$, and let
$P$ be a random rational prefix plane selected from the input and private
coins. The output of interest is capture as a row or terminal recovery. A
property of the plane alone can certify the latter if the projected plant is
nonzero and its signed pair is the entire set of shortest projected vectors.
A plane alone does not specify the output rows.

## A conditional information bound for any finite selector

Let $E(A,U,P)$ be a bad event. For example it can be failure of the
sufficient terminal criterion above, including a vanished projection and
ties with a different line. For fixed $U=u$, draw a reference plane from
the actual marginal law of $P$ given $u$, independently of a fresh design.
Write $h$ for the probability of $E$ under this reference experiment and
$p$ for its probability under actual selection, both conditional on $u$.
In bits,
\[
 D_{\rm Ber}(p\Vert h)\le I(A;P\mid U=u).
\]
Indeed the divergence between the actual joint distribution and the product
of its marginals is exactly the mutual information. Partitioning the outcomes
into $E$ and its complement and applying the log-sum inequality on each
part proves the claim, including zero-mass cases by continuity. The same
argument averaged over $u$, followed by a second log-sum inequality, gives
the corresponding inequality for unconditional $p,h$ and $I(A;P\mid U)$.

For $0<h<1$, expanding binary divergence gives
\[
 p\le \frac{I(A;P\mid U=u)+H_2(p)}{\log_2(1/h)}
 \le \frac{I(A;P\mid U=u)+1}{\log_2(1/h)} .
\]
Thus, *if* a reference failure bound of $2^{-128}$ and a conditional
information bound of one bit were proved for the same selector, actual
failure would be at most $1/64$. These numbers illustrate the implication.
The ambient first-moment bound in [the lower-bound note](wall1_lower_bound.md)
does not supply its reference hypothesis. Projected competitors live in
$\pi_{P^\perp}L_A$, and a short projected vector can have only long ambient
lifts.

## Zero information about the plant permits maximal selection bias

The three-plane example of [the interior note](wall1_interior.md) makes the
information bound exact. Take its fixed plant, uniform scalar design over
$\mathbb F_3$, and planes $P_0,P_1,P_2$. Its congruence calculation
gives interior failure for $P_v$ exactly on $A=v$. For any
$0\le r\le1$, select $v=A$ with probability $r$, and otherwise
choose one of the other two labels uniformly. The marginal label is uniform
by symmetry. Hence
\[
 h=1/3,\qquad p=r,\qquad I(U;P)=0,\qquad
 I(A;P\mid U)=\log_2 3-H_2(r)-(1-r)=D_{\rm Ber}(r\Vert1/3).
\]
The entropy calculation uses the conditional label masses
$(r,(1-r)/2,(1-r)/2)$, permuted according to the design. At $r=1$
the selector changes the event probability from one third to one, while
at $r=1/3$ it leaves the reference law intact. This is a statement about
the interior obstruction, not the probability of missing capture. Each
plane is a possible saturated prefix plane as in the cited construction.

## Scope and cost

A fixed plane independent of the design conditional on the plant has zero
information cost in this theorem. For a plane resulting from a random change
of basis, independence of the *coins* from the design does not establish
independence of the resulting plane. Even the cardinality of the support of
the coins alone gives no upper bound on how many planes different inputs can
produce with the same coins.

To apply the theorem to a terminal block requires a reference estimate for
the whole terminal bad event and a bound on design information for the actual
selector. Treating failure of this sufficient criterion as failure of the
algorithm can overcount failures through early capture. Conversely, if the aim
is actual row capture, identifying a shortest quotient class leaves a lift
ambiguity by the prefix lattice. The information theorem prescribes no SVP
calls and proves no running time or proper block width for a recovery
algorithm. A full-dimensional HKZ first step would still charge dimension
$d$ even if every later block had smaller width.
