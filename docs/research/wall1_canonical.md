# A canonical flag can forget capture

Even the complete ordered flag of a canonical HKZ basis can lose information needed for the corrected event. Two deterministic, presentation-independent HKZ rules can select identical flags on every input and give opposite answers on the same marked lattice. The ambiguity occurs in the lift of a projected shortest vector, after the shortest-line decision has already been made.

## A binary example in dimension four

Use the Euclidean metric, terminal width two, and the lattice
\[
L=\{x\in\mathbb Z^4:x_1+x_2+x_3=0\pmod 2,\quad x_4=0\pmod 2\}.
\]
Take the primitive mark \(u=(1,0,-1,0)\). Write
\[
a=(1,-1,0,0),\quad b=(0,1,-1,0),\quad
c=(1,0,1,0),\quad h=(0,0,0,2).
\]
Compare the ordered bases \((a,b,c,h)\) and \((a,b+a,c,h)\). The first has absolute determinant four, the index of the congruence kernel, and the second differs by an integral column addition. Their ordered prefix sublattices agree at every rank.

Both bases are HKZ reduced. The minimum squared norm is two because the lattice contains no coordinate unit vector and contains \(a\). The orthogonalized vectors after \(a\) are
\[
b^*=(1/2,1/2,-1,0),\qquad c^*=(2/3,2/3,2/3,0),\qquad h.
\]
After projecting off \(a\), the image of \(c\) equals \(c^*-b^*/3\). A vector with a nonzero fourth coordinate has squared norm at least four. In the remaining plane a vector with coefficient \(j\) on the image of \(c\) has squared norm
\[
(3/2)(i-j/3)^2+(4/3)j^2,\qquad i,j\in\mathbb Z.
\]
For \(|j|=1\) the minimum is \(3/2\), for \(|j|\ge2\) it exceeds \(3/2\), and for \(j=0\) the shortest nonzero choice again gives \(3/2\). After the second projection the lattice has orthogonal basis \((c^*,h)\), with squared lengths \(4/3,4\). This verifies projected shortestness at every step. The nonzero size-reduction coefficients have absolute values \(1/2,1/2,1/3\) for either lift.

Since \(u=a+b\), its terminal projection vanishes for both bases. The first basis misses capture and the second captures in position two. The mark is ambient shortest, with ties.

## Realization by canonical rules

Fix ambient coordinates. At each step choose an oriented shortest vector in the projected lattice using a fixed priority order for ties. Use priorities favoring the successive orthogonal vectors displayed above (including \(a\) at step one), with ordinary lexicographic ordering as fallback among the finitely many oriented minimizers. Lift the selected vector to a size-reduced representative by reducing coefficients from the latest previous basis vector back to the first. At a half-integer choose a fixed endpoint. These operations depend only on the embedded lattice and the chosen conventions. Shortest projected vectors are primitive, so each selected prefix extends to a basis and the next projection is discrete.

Use the positive endpoint at ties except at step two, where the two rules use opposite endpoints. At step two the lifts are exactly \(b\) and \(b+a\). At step three the positive endpoint gives \(c\) for both. More generally, changing the lift adds a prefix vector, leaving the enlarged prefix lattice identical. Induction therefore gives identical flags on every input, including the same oriented projected vectors. On the point mass at the displayed marked lattice, every intrinsic flag count has identical distribution for the two rules while their corrected success probabilities are zero and one.

This example isolates the zero-projection stratum. To infer capture there, a count must retain the chosen representatives or prove a property of the specified lift convention. On the narrower event that the mark generates the unique ambient shortest line, every HKZ rule captures at step one. That observation uses full-dimensional shortestness. It gives no smaller-width implementation or success estimate for the verified slide output. The example is a binary congruence kernel with a tied minimum, and supplies no failure probability for the registered fixed-plant distribution.
