# Combining independent circuit components

This paper bound extends Part 253 beyond supports with a single linear relation.
It covers supports whose augmented-input matroid is a direct sum of circuits and
coloops. At draw 13 and order 12, their total correction to the independent model,
normalized by rho*mu^12, is below 2.468e-54. A component with nullity at least two
is not covered. Therefore the complete void probability is still unbounded here.

## Component expansion

Keep the fixed input fibers of Part 252. For an indexed tuple with distinct
support T, use its input matroid, with rank taken over F_q on the vectors (1,y).
Assume each component is either a circuit C or a coloop. Distinct component spans
form a direct sum. The restrictions of a uniform affine row map to those spans
are independent: extend bases of the component spans to an ambient basis.
The same holds simultaneously for all output rows.

For multiplicities e_y, the moment on each circuit equals

\[
 M_C=M_C^0+d_C,\qquad
 M_C^0=\prod_{y\in C}b_{e_y}(\rho_y),\qquad
 d_C=\left(P(C)-\prod_{y\in C}\rho_y\right)
                  \prod_{y\in C}a_{e_y}(\rho_y),
\]

where a_e,b_e are the functions from Part 253. The whole tuple moment is the
product of these circuit factors and of the coloop moments. Subtract the
independent tuple moment and expand: choose a nonempty subset of circuit
components at which to use d_C, and use the independent factors everywhere else.
Call the chosen circuits *activated* in this expansion.

On an activated circuit every multiplicity must be positive, and |a_e|<=1.
Every unactivated input contributes b_e; a singleton vanishes, and otherwise
|b_e(rho)|<=rho. Thus all inputs outside the activated circuits may be counted
as arbitrary blocks of size at least two, weighted by their individual rho.
Their support restrictions can be dropped in a nonnegative upper bound.

## Exponential generating function bound

Let epsilon_j bound the sum of |P(C)-product rho_y| over ordered j-tuples of
inputs forming a circuit. Part 253 supplies

\[
 \epsilon_j=Q_j q^{-m(j-1)}+B_j q^{-mj}\quad(j\ge3).
\]

Let Delta_sep be the sum of actual-minus-independent tuple moments over the
supports described above. As a formal power series truncated after degree k,
define

\[
 F(z)=\mu(e^z-1-z),\qquad
 G(z)=\sum_{j=3}^{k}\frac{\epsilon_j}{j!}(e^z-1)^j.
\]

Then

\[
                |\Delta_{\rm sep}|
          \le k![z^k]e^{F(z)}\bigl(e^{G(z)}-1\bigr).       \tag{1}
\]

Here each ordinary input block has size at least two, giving F. Each activated
circuit consists of j nonempty input blocks. The ordered circuit sum is divided
by j!, giving its term in G. A collection of activated circuits is unordered,
which gives the exponential of G; at least one must be chosen. Equivalently,
partition the k labeled positions into input blocks, group selected input blocks
into activated circuits, and assign inputs. Canonically ordering blocks by their
least position identifies the ordered circuit count without an additional
factorial. Summing input assignments on the other blocks is at most a power of
mu. Products of the epsilon_j bound the activated circuit assignments even after
allowing overlaps. Allowing repeated labels only enlarges this nonnegative sum.
Every original component expansion has a unique position partition and activated
subcollection, so it is included in this upper enumeration.

The degree-k coefficient of e^F G is precisely the bound computed in Part 253:
its coefficients use H_(k,j,b). In (1) this same expression also covers single
activated circuits in tuples that have other, unactivated circuit components.
Those other components have been absorbed into the unrestricted ordinary blocks.
The terms e^F sum_(a>=2) G^a/a! cover two or more activated circuits. They should
not be described as the whole contribution of supports having multiple circuits,
since such supports also occur in the single-activation terms.

## Evaluation and remaining class

All coefficients in (1) are nonnegative. After division by rho*mu^k, each
monomial has a power mu^(b-k), where b counts ordinary blocks and b<=k/2.
It is therefore valid to use Part 250's lower bound for mu. Finite polynomial
convolution through degree 12 and outward 80-digit interval arithmetic give

- the whole right side of (1), divided by rho*mu^12, below 2.468e-54;
- its terms with at least two activated circuits below 4.174e-96.

The calculation uses finite sums of nonnegative terms; the tiny second value
is not obtained by subtracting nearly equal interval estimates.

Let Delta_conn be the correction from all remaining supports, namely those
having at least one component of nullity at least two. Combining with the
independent baseline only gives

\[
 \Pr(b_{13}>0.280)\le 2.845\cdot10^{-13}+2.468\cdot10^{-54}
                         +|\Delta_{\rm conn}|/(0.280\mu^{12}).
\]

The last term is open. For example, four distinct collinear inputs have rank two
and form such a component; the direct-sum argument does not apply. Neither this
remaining count nor the later selected-projection obligations are removed by
(1). There is no new complete BKZ failure bound.

## Verification

Run `python3 docs/research/scripts/wall1_affine_circuit_components.py`.
The exact fixture consists of two three-point affine lines over F_3 whose
augmented spans form a direct sum. It enumerates all 81 affine maps, tests 64
choices of fiber sets, and verifies component factorization and 192 rational
moment inequalities at orders 6, 8, 12. It then checks the degree-12 interval
bound using the existing Part 250 and Part 253 verifiers. This is a paper result
with finite regression checks, not a Lean formalization or a simulation of the
selected width-506 process.
