# Rank-two components with overlapping affine relations

This paper bound handles distinct inputs on an affine line, including four or
more inputs and hence multiple overlapping relations. It extends the admissible
components in Part 254 to all rank-two components. The remaining unbounded class
has a connected component of rank at least three and nullity at least two.
This is still a partial moment calculation, not a complete BKZ probability bound.

## A uniform envelope for a collinear support

Use Part 252's fixed fibers B_y, densities rho_y and joint probabilities P(U).
For a support T of h distinct collinear inputs, and any positive multiplicities
e_y, compare its centered product moment with the independent Bernoulli model.
Expand each factor using a_e(rho) J_y + (-rho)^e. Since |a_e|<=1 and
rho^e<=rho, the absolute correction is bounded by the common envelope

\[
 L(T)=\sum_{\substack{U\subseteq T\\|U|\ge3}}
       \left|P(U)-\prod_{y\in U}\rho_y\right|
                          \prod_{y\in T\setminus U}\rho_y.     \tag{1}
\]

Subsets of size zero, one or two have no discrepancy: distinct augmented inputs
(1,y) on a line are pairwise independent. The bound holds for every multiplicity
vector, even when densities exceed one half. Crucially, the factors outside U
remain weighted by rho; replacing those weights by unrestricted output counts
would lose the cancellation that Part 252 restored.

Let Q_3 and B_3 be the full-point circuit and input-dependency count bounds of
Part 250, and put epsilon_3=Q_3 q^(-2m)+B_3 q^(-3m). Then, over **ordered**
h-tuples of distinct collinear inputs,

\[
 \sum_T L(T)\le\eta_h,
 \qquad
 \eta_h=\left(2^h-1-h-{h\choose2}\right)q^{h-3}\epsilon_3.
                                                                  \tag{2}
\]

To prove this, fix a subset U of the h positions of size j>=3. Select its first
three positions as anchors. For the joint-probability term, each compatible output
assignment on U makes its full points collinear: the affine map on the input line
is determined by two distinct inputs. Its three anchor full points are a circuit,
so there are at most Q_3 ordered anchor triples. Each remaining input in U has
at most q positions on that line, with its output uniquely determined, giving
at most q^(j-3) completions. Every compatible assignment costs q^(-2m).
Each of the h-j inputs outside U is summed with weight rho_y<=1 over at most q
positions on the same input line. Dropping all distinctness and candidate-membership
restrictions in these completion bounds can only increase the nonnegative sum.
This bounds the joint part by Q_3 q^(-2m) q^(h-3).

For the independent-product term, the three anchor candidate points have dependent
inputs and distinct full residues. Their weighted sum is at most B_3 q^(-3m).
Every other input, inside or outside U, contributes a sum of rho_y along the fixed
line, bounded by q. This bounds the independent part by B_3 q^(-3m) q^(h-3).
Finally sum over all 2^h-1-h-binomial(h,2) choices of U. This proves (2) without
asserting independence of the h values on the line.

## Combining the new components

A distinct collinear support of size at least three has rank two; its circuits
are all triples. It is a connected matroid component. Size three is already
covered by Part 254's circuit activity. For h>=4, add eta_h to the old activity:

\[
 \widetilde\epsilon_3=\epsilon_3,\qquad
 \widetilde\epsilon_h=\epsilon_h+\eta_h\quad(h\ge4).
\]

Circuits of size h>=4 and rank-two components of size h>=4 are disjoint classes.
The component expansion from Part 254 applies because (1)--(2) provide a common
absolute envelope for every positive multiplicity pattern. Thus its generating
function bound, with epsilon replaced by tilde-epsilon, covers every support
whose components are circuits, rank-two components, or coloops.

At draw 13, order 12, the normalized correction remains below 2.468e-54. Terms
with at least one activated rank-two component of size at least four are below
4.506e-98. The latter is computed using the nonnegative coefficient expression

\[
 12![z^{12}]e^{F(z)}e^{G(z)}(e^{H(z)}-1),\qquad
 H(z)=\sum_{h=4}^{12}\eta_h(e^z-1)^h/h!,
\]

then dividing by rho*mu^12. No subtraction of nearly equal interval bounds is
used. As in Part 254, powers of mu after normalization are nonpositive, so the
lower bound on the candidate count has the correct direction.

The unresolved correction now comes from supports containing a connected component
of rank >=3 and nullity >=2. Its contribution cannot be omitted. Later draw
probabilities and selected projections are also still unresolved. In particular,
this does not establish a numerical upper bound for the full draw-13 exit event.

## Verification

Run `python3 docs/research/scripts/wall1_affine_rank_two.py`. Over F_5 the script
enumerates all 25 affine maps of a line, 32 configurations of nonuniform output
fibers, and supports of sizes four and five. It checks 576 exact rational
multiplicity corrections against (1), and 64 aggregate bounds (2). It then checks
the concrete degree-12 bound with outward 80-digit interval arithmetic. The new
lemmas are paper proofs, not Lean-formalized; finite checks are not a simulation
of the selected width-506 process.
