# Zero-void transport obstruction at q=3329 and width 506

This is a counterexample to an all-state zero-preserving multiplicative
transport claim at the actual modulus and width. It is not a counterexample
to the probability budget for the actual selected-history ensemble. Its
quotient rank is25. The determinant argument below excludes this state
from the first406 freezes of the prescribed exact width506 restart.

## The incoming cubic-grid state

Let q=3329. Define scalar check-column lists

    A = (1,2,3,4,5,6,7,15,30,45,60,75,90,105,
         225,450,675,900,1125,1350,1575),
    B = (1062,53,895,434,402,699,981,747,1567,
         1399,1381,769,516,568,278,1348,117).

Form a block-diagonal25-by505 check matrix H from20 copies of A and5
copies of B; 20*21+5*17=505. Put K=Z^505 and M=ker(H mod q).
Every row has a nonzero pivot and disjoint support, so H has rank25,
K/M is F_q^25 and det(M)=q^25. Row rescaling and a coordinate permutation
give a systematic presentation without changing the Euclidean lattice.

For a scalar list h, define

    D_h(v)=min{sum_i z_i^2 : sum_i h_i z_i=v mod q}.

The exact integer dynamic program in `scripts/wall1_q3329_zero_void.py`
certifies max D_A=3 and max D_B=4. For A the numbers of residues at
distances squared0,1,2,3 are(1,42,600,2686). For B the analogous
counts at0,1,2,3,4 are(1,34,500,2182,612). The respective residues114
and6 attain the maxima. Therefore the incoming maximum squared coset
distance is20*3+5*4=80.

## The actual shortest append and projected distances

Choose the fresh mark U=(1,0,...,0), the first column of the first A
block. The appended lattice is

    W_U={(x,j) in Z^506 : Hx=jU mod q}.

All columns of H are nonzero and distinct up to sign: within each block
the listed values are distinct in[1,1664], and different blocks have
disjoint support. Thus M has no vector of squared norm1 or2. The mark U
is nonzero, so W_U has no unit vector. Its only shortest line is generated
by w=(e_1,1), of squared norm2. Indeed every norm2 integer vector has
two signed unit entries; horizontal ones are excluded, and the column
matching U is unique up to sign. The signed tie convention does not alter
this line or its orthogonal projection P_w.

For any pulled-back test mark v, all lifts satisfy Hx-jU=v. With
x'_1=x_1-j and x'_i=x_i for i>1,

    ||P_w(x,j)||^2 = (x'_1)^2/2 + sum_(i>1)(x'_i)^2,
    Hx'=v.

Every integral x' is attained, for example with j=0. Hence projected
coset distances are exactly those of the same block code with the first
coordinate's cost halved. Uniform marks remain uniform: w lies in the
kernel of the syndrome map, which therefore descends to the projection,
with quotient still F_q^25.

The dynamic program also certifies that the first A block still has
maximum squared distance3 after halving this coordinate cost, attained
at114. Using twice-cost integers, its histogram at0,...,6 is
(1,2,40,58,542,416,2270). Other blocks are unchanged. In particular the
mark with20 entries114 and5 entries6 has projected distance squared80.
In fact exactly2270*2686^19*612^5 marks attain this maximum, by the
three scalar histograms and separation of the blocks.

## Correct dimension-dependent radius

Use the actual appended dimension506 and scale

    g=(q^25/V_506)^(1/506), T=(1.1g)^2,
    R^2=T-1, B^2=T*2^(-1/506)-1.

The checker bounds pi with rational arithmetic and verifies, after raising
positive quantities to integer powers,

    81 < T < 81*2^(1/506).

Consequently R^2>80 and B^2<80. The scale is g approximately8.1852,
outside any additional g>=549
restriction used in earlier rectangle investigations. Thus no such
restricted claim is contradicted here. Incoming void is exactly zero, and
the displayed mark is uncovered after the genuine shortest projection.
The same holds for -U by changing the sign of the appended coordinate.
Thus, with delta=.280 and Phi(p)=min(1,p/delta),

    E_U Phi(P'_U) >= 2/(delta*q^50) > 0 = C*Phi(P)

for every finite C. This lower bound only uses one uncovered mark on each
of two fresh-mark branches. It is extremely small and does not contradict
the allowed production exceptional-probability budget.

## Verification scope

The dynamic program minimizes costs over successive coordinates modulo q.
All costs are nonnegative. At a certified cost ceiling, a coordinate whose
individual cost exceeds the ceiling cannot occur in a better solution.
Discarding such choices is therefore exact, not a heuristic search. Finite
costs for every residue supply upper bounds; the same exhaustive recurrence
excludes all smaller costs. Halved costs are handled by doubling all costs.

This state is unit-generated and has qK contained in M contained in K,
quotient rank at most400, and the actual width506 radius exponent. These
generic properties alone therefore do not prove multiplicative transport.
The actual draw14--404 selected process cannot reach this particular
state, by the determinant floor below. The all-state counterexample
therefore leaves open a multiplier restricted to reachable histories.

There is an algebraic embedding into an original rank400 graph: take
the check matrix diag(I_375,H) on Z^880 and project off the first375
coordinate axes. Its kernel on those axes is qZ^375; the resulting pair
is precisely (K,M) above. Normalizing pivot columns makes this a systematic
rank400 presentation. This only proves compatibility with a static raw
projection. It does not make the proposed flag a valid shortest-selected
flag: its q-length axis vectors compete with much shorter relations in
the remaining blocks. In particular this embedding cannot be used to
assign a positive probability to the state in the actual selected process.

The scalar distances were independently recomputed, and the shortest-line,
projection, and static-embedding arguments independently reviewed. The
checker uses exact integer and rational arithmetic for its conclusions;
floating radii are display-only. No Lean formalization is claimed.

## Deterministic exclusion from the prescribed restart

This elementary floor is weaker than the sharper determinant recurrences
already studied, but suffices to exclude the example without a probability
gate. Let D_f be the retained determinant after f freezes, with D_0=q^400,
height-one appends, and exact SVP in every full506-dimensional window.
The appended determinant is D_(f-1). The cube form of Minkowski's theorem
gives a nonzero vector of length at most sqrt(506)*D_(f-1)^(1/506): apply
the theorem to cubes [-r,r]^506 for r>D_(f-1)^(1/506), and take a limit.
The actual shortest vector is primitive, and projection divides determinant
by its length. Therefore

    D_f >= D_(f-1)^(505/506)/sqrt(506).

Iterating, with a=(505/506)^f, yields

    log2 D_f >= 400*a*log2 q - 253*(1-a)*log2(506).

For all0<=f<=406, exact integer comparison gives
9*505^406>4*506^406, hence a>4/9. Since2^11<q<2^12 and506<2^9,

    log2 D_f > (4/9)*400*11 - 253*(5/9)*9
              =6215/9 >684 >57*log2 q.

In particular D_f>q^57 throughout these freezes, whereas the example has
determinant q^25. This proves nonreachability, not just failure of the
specific static embedding to supply a shortest flag. It is valid for the
stated forward restart; no assertion about arbitrary later BKZ tours or
other initializations is made. The exact integer comparisons are included
in the checker. Since det(P Z^N)<=1, the same argument also forces the
actual quotient rank to be at least58 in this range. This coarse floor
does not estimate the void probability on the remaining states.
