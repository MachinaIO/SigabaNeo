# Exact dual rank accounting for shared affine completion coefficients

This supplies the finite-field coefficient sum inside Equation13 of
`wall1_mixed_gram_kernel.md`. It handles the coefficient matrix shared by
all input coordinates without replacing it by independent row choices.
The rank of the dual completion matrix determines the image size and the
constant fiber size exactly. Production is unchanged.

## Affine pushforward theorem

Work over F_q. Let r>=1, k,n>=0, let B be a fixed k-by-n matrix of rank t,
and write d=r-1. Let V range over all r-by-k coefficient matrices with
each column summing to one. Put

    s=1_k^T B,
    E=[e2-e1,...,er-e1], an r-by-d matrix.

Every admissible V has a unique representation

    V=e1*1_k^T+E X,       X in F_q^(d by k).

Consequently the image of V -> VB is exactly the affine set

    e1*s + {E Y : each row of Y belongs to rowspace(B)}.     (1)

It contains q^(dt) matrices, and every image has exactly q^(d(k-t))
preimages. Proof: each row map x->xB has image rowspace(B), dimension t,
and kernel dimension k-t. The d row maps act independently. Multiplication
by E is injective because its bottom d rows form the identity. This proves
both the image description and the fibers, including t=0, r=1, k=0 or n=0.

Let T0 be any fixed r-by-n offset and f any nonnegative function on
r-by-n residue matrices. Then the **unnormalized sum** is

    sum_(affine V) f(T0+VB)
      =q^(d(k-t))*sum_(Y rows in rowspace(B)) f(T0+e1*s+EY). (2)

The **uniform average** is instead

    q^(-dk)*sum_(affine V) f(T0+VB)
      =q^(-dt)*sum_(Y rows in rowspace(B)) f(T0+e1*s+EY).    (3)

The factor q^(d(k-t)) in (2) cannot be dropped. Rank compression reduces
the number of different tests, but every surviving test has that many
original coefficient charts. In particular t=0 evaluates f only once
and multiplies by q^(dk) in the sum; at t=k the map is injective and gives
no coefficient-count reduction. This is not independence of the n input
coordinate columns: their rows must jointly belong to rowspace(B).

## Fixed anchor offset and the joint dual Gaussian

In Equation13 write W=[A,V] and partition the integer dual frequencies,
shared across the n input coordinates, into B_anchor and B_completion.
Their shapes are respectively a-by-n and k-by-n. Reduce them modulo q and
apply (2) with

    B=B_completion mod q,       T0=A B_anchor mod q.

For the positive definite basis quadratic form D, the relevant test is

    f(T)=sum_(Z in Z^(r by n))
       exp(-pi^2*sum_(nu=1)^n
          (Z_nu+T_nu/q)^T D^(-1)(Z_nu+T_nu/q)).           (4)

Here columns are indexed by nu, and any integer lift of T may be used.
Changing a lift by a multiple of q reindexes Z, so f is genuinely a
function of the residue matrix. It is nonnegative and convergent.

The remaining dual factor
exp(-pi^2*sum_nu b_nu^T Lambda^(-1)b_nu/q^2) is independent of V and stays
outside the coefficient sum. The coefficient-invariant prefactor in
Equation13, raised to the nth power, also stays unchanged. Thus one may
sum the coefficient matrices first using (2), then sum all integer dual
frequencies. All summands are nonnegative, so this interchange is valid.
The affine anchor offset is kept inside f throughout; it is not averaged
away or replaced by zero.

This gives an exact rank-stratified route for the joint dual kernel:
each fixed dual frequency matrix has t=rank_Fq(B_completion), contributes
q^(d(k-t)) times a sum over d copies of its rowspace, and retains its
original frequency penalty. A useful upper bound still needs the Gaussian
mass of those rowspaces and their frequency penalties. Rank t alone does
not specify their orientation, so it does not turn (4) into an independent
product over coordinate columns or into the zero-frequency term.

At the production values r=11,k=6, unrestricted V has q^60 choices.
For dual rank t the exact image size is q^(10t) and the fiber size is
q^(60-10t). Their product is q^60 for every t. Any numerical saving must
come from bounding the Gaussian test on that affine image, not by ignoring
its fibers.

## Distinct and pinned restrictions

If H distinct affine coefficient columns are forbidden and the k new
columns must be distinct, the number of eligible V is

    Q_res=(q^d-H)_k,

provided H<=q^d; it is zero when too few columns remain. For the restricted
sum, nonnegativity gives the valid relaxation

    sum_(V eligible) f(T0+VB)
        <= sum_(all affine V) f(T0+VB),                      (5)

and the right side is evaluated exactly by (2). Constant fibers generally
do not survive the restrictions. The exact restricted formula uses
multiplicities m(T)=#{eligible V:VB=T}, with
0<=m(T)<=q^(d(k-t)); replacing them all by the unrestricted fiber size
is an upper-bound step.

For Q_res>0 the corresponding restricted average satisfies only

    average_eligible f <= (q^(dk)/Q_res)*average_all f.       (6)

There is no general inequality with the factor q^(dk)/Q_res removed.
For q=3,r=2,k=n=1,B=(1), pin e1 and choose f(V)=1{V!=e1}.
The restricted average is one, while the unrestricted average is 2/3.
For q=3,r=2,k=2,n=1,B=(1,1)^T, distinct columns avoiding e1 leave exactly
two V, both with VB=(2,0)^T. The unrestricted image has three equally
weighted elements. This directly exhibits nonuniform restricted fibers.

The production mixed-chart Gaussian sum is unnormalized in V, so (5),
followed by (2), is the appropriate safe relaxation. No extra division by
Q_res or q^60 should be introduced unless the original expression was
explicitly an average.

## Exact finite checks

Run `python3 docs/research/scripts/wall1_dual_coefficient_rank.py`.
The checker exhausts q=2,3, r=1,2,3 and k,n=0,1,2: 414 dual matrices
and 8958 affine coefficient configurations. It checks image sets, uniform
fiber counts, offsets, sums and averages with exact finite Gaussian tests,
and 414 pinned/distinct restricted sums. It also checks the two explicit
restricted-average/fiber counterexamples. All identities and inequalities
use integer or rational arithmetic. No infinite theta truncation, numerical
production estimate, or new selected-history claim is made.
