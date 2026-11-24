# A nearest-input witness set need not be saturated

This exact example supplements `wall1_winner_coupled_replicas.md`.
It uses J={0}, canonical nearest incoming representatives, and an actual
shortest horizontal graph winner. It demonstrates a strict improvement from
saturating witness hits under the quotient kernel. The radius is arbitrary;
no production radius or selected-history reachability is asserted. Genuine
ties occur and the specified deterministic rule is part of the example.

Take q=5 and let K have the rational Euclidean basis

    e1=(1/10,0), e2=(7/250,12/125), M=5K.

Its Gram matrix is (1/100)[[1,7/25],[7/25,1]]. Identify H=K/M with F5^2
using these basis coordinates. Choose u=0, so W_0=(M,0)+Z(0,1). Resolve
nearest-representative ties by lexicographic integer coordinates (x,y), and
winner ties by (x,y,j). The checker also verifies that physical-coordinate
lexicographic nearest ties give the same representatives in this fixture.

The actual shortest winner is w=(-5e1,0), with squared norm 1/4. Its direction
is horizontal and its projection deletes the first physical coordinate.
Consequently a vector x e1+y e2 has projected squared norm

    (144/15625) y^2.

The quotient map f:H -> H' kills exactly F5*(1,0). H' has five marks,
parametrized by the second coordinate modulo 5.

Set the toy outgoing radius squared to b^2=1/20. In mark (3,3), the canonical
nearest representative is -2e1+3e2, whose squared norm is 241/2500. It ties
with 3e1-2e2; the stipulated lexicographic rule chooses the former. Its
projection has squared norm 1296/15625>b^2, so this J={0} witness misses.
In the same quotient fiber, mark (0,3) has nearest representative -2e2,
whose projected squared norm is 576/15625<b^2, so its witness hits.

The exhaustive rational check gives the complete witness hit set

    B=H minus {(3,3)},   |B|=24,   B+ker(f)=H.

Thus the unsaturated witness void bound is 1/25, whereas the saturated bound
is zero. In fact the actual outgoing void is zero: the exact projected
nearest distance in a mark (x,y) is (144/15625)*|y|_5^2, whose maximum is
576/15625<b^2. Equal quotient fibers justify computing this fraction either
on the five outgoing marks or by uniform pullback to the 25 incoming marks.

## Exhaustive bounds and verification

The Gram matrix is at least (9/1250) times the identity. Every residue has a
centered representative |x|,|y|<=2 with squared norm at most 256/2500.
Every nearest representative therefore satisfies x^2+y^2<=128/9, so the
finite box [-3,3]^2 contains every candidate that can tie or improve it.
The script exhausts this box with exact rational comparisons.

For the winner, 5e1 is an available vector of squared norm 1/4. Every
competitor at that radius has integer height j=0 and x^2+y^2<=625/18<36.
Enumerating [-5,5]^2 with x,y divisible by 5 therefore includes every possible
winner. The minimum has value 1/4 and lexicographically first vector -5e1.
The vector is primitive in W_0. These bounds prove completeness rather than
merely exhibiting short representatives.

Run `python3 docs/research/scripts/wall1_fiber_saturation_fixture.py`.
The execution log is `/tmp/wall1_fiber_saturation_fixture.log`.
This refutes an unconditional assertion that canonical nearest-input
witness hits are always saturated. It does not claim that nonsaturation
persists without ties, nor quantify its frequency in production histories.
