# Suppressing proper-subset terms in the final centered product

**Follow-up:** [Part 261](wall1_affine_two_constraints.md) supplies the missing
positive count and proves the draw-13 paper bound. The explicit remainder below
records the reduction used in that proof; later history probabilities remain open.

This paper deduction converts Part 259's remaining signed ten-input term into a
positive count of fully compatible ten-point configurations. Proper-subset terms
are below 6.927e-293 after normalization, and compatible full configurations with
a three-element circuit contribute below 4.803e-59. The remaining positive count
has rank 4--7, no three-element circuit, and a four-element circuit. It is not
bounded here, and the later selected-projection obligations remain open.

## A rank deficit forced by the absence of coloops

Let T be a support of h inputs with augmented rank r and no coloop. For any
proper subset U of size j and rank t, put w=h-j-r+t. Then w>=1.
Indeed w>=0 because adjoining h-j vectors increases rank by at most h-j. If
w=0, all those vectors are independent modulo span(U); deleting any one of them
lowers the full rank by one. Each would be a coloop, a contradiction. Connected
supports of more than one element have no coloops, so the lemma applies to every
support remaining in Part 259.

In the circuit-anchor proof of Part 256, choose r-t outer basis-extension inputs.
There are w further outer positions left in the fixed rank-r affine input span.
Their density-weighted sums satisfy the stronger bound

\[
                  \sum_{y\text{ in that span}}\rho_y
                            \le q^{r-1}\rho_{\max}.
\]

Previously rho_y<=1 was used at this step. Retaining the actual rho_max gives a
factor rho_max^w in every proper-subset term. This applies both to the joint and
the independent-product terms; the other parts of the anchor argument are unchanged.

## Proper-subset bound

Define

\[
\begin{split}
 E^{\rm proper}_{h,r}={}&\sum_{j=3}^{h-1}{h\choose j}
 \sum_{\substack{2\le t\le\min(j-1,r)\\w=h-j-r+t\ge1}}
 \sum_{c=3}^{t+1}
 {j\choose c}{j-c\choose t-c+1}{h-j\choose r-t}\\
 &\quad\cdot\epsilon_c\mu^{r-c+1}
 q^{(t-1)(j-t-1)+(r-1)w}\rho_{\max}^{w}.
\end{split}                                                     \tag{1}
\]

For ordered coloop-free supports of size h and rank r, this bounds the sum of
all absolute proper dependent-subset discrepancies, weighted by the outside
fiber densities. The proof is Part 256's count with the strengthened outer
completion bound. A restricted support family can only make this nonnegative
sum smaller. It is not necessary to assume a conditional random law for a span.

Use h=10 and sum r=4,...,7. Part 257's integer-ball bound supplies rho_max.
All powers of mu after division by rho*mu^10 are negative. Outward interval
arithmetic therefore gives

\[
     \sum_{r=4}^{7}E^{\rm proper}_{10,r}/(0.280\mu^{10})
                                                   <6.927\cdot10^{-293}.   \tag{2}
\]

## The full-incidence term is all that remains

For a distinct ten-input support, let W_T=E product_y(J_y-rho_y). Subtracting
the independent model, whose centered product is zero, gives exactly

\[
 W_T=P(T)-\prod_{y\in T}\rho_y
 +\sum_{\substack{U\subsetneq T\\U\text{ dependent}}}
 (-1)^{10-|U|}\left(P(U)-\prod_{y\in U}\rho_y\right)
                            \prod_{y\in T\setminus U}\rho_y.
\]

Consequently W_T is at most P(T) plus the absolute proper-subset sum. Dropping
the negative product term is valid for this one-sided upper bound. This argument
uses the signed term in the polynomial expansion directly; one cannot infer it
by simply replacing |W_T| with P(T).

If the support contains a three-element circuit, every compatible full output
assignment has a full-point three-circuit at those positions. Choose its three
positions, extend to rank r with r-2 full candidate points, and complete the
remaining 9-r positions in the resulting affine full-point span. Part 250 gives

\[
 \sum_{\substack{T\text{ ordered},\,|T|=10,\,\operatorname{rank}T=r\\
                  T\text{ contains a three-circuit}}}P(T)
 \le {10\choose3}{7\choose r-2}
       Q_3 q^{-2m}\mu^{r-2}q^{(r-1)(9-r)}.                \tag{3}
\]

The verifier safely replaces Q_3 q^(-2m) by the larger epsilon_3. Summing ranks
4--7 and normalizing by rho*mu^10 makes (3) less than 4.803e-59.

Now let N_r count ordered ten-tuples of full candidates in the fixed raw ball
whose inputs are distinct, have rank r, form a connected matroid, contain a
four-circuit but no three-circuit, and whose full augmented rank is also r.
The last condition is precisely compatibility of all output assignments.
Each such tuple has joint incidence probability q^(-mr). Its full-point and
input matroids coincide, since the output assignment extends linearly.

Returning to the adjusted square H from Part 258, the resulting statement is

\[
 \Pr(b_{13}>0.280)\le2.432\cdot10^{-12}
       +\frac{\sum_{r=4}^{7}N_rq^{-mr}}
                    {14400\cdot0.280\,H(0;\mu)^2}.       \tag{4}
\]

The constant includes the already proved reference, Bernoulli, small-component,
nine-input, rank-three/eight, and no-four-circuit charges, as well as (2)--(3).
The positive count in (4) remains open. It must retain more than one relation:
the existing single-circuit completion bound is insufficient. Neither this
reduction nor the tiny proper-subset correction is a complete draw-13 exit bound.
Draws 14--404 and the later projection issue are unchanged.

## Verification

Run `python3 docs/research/scripts/wall1_affine_proper_subset.py`.
It checks 17148 proper-subset rank deficits on coloop-free subsets of F_3^2,
then checks (2)--(3) and the combined constant in (4) with outward interval
arithmetic using the existing Gaussian and integer-ball bounds. This is a paper
proof with finite regression checks; it is not Lean-formalized and does not
simulate the selected width-506 process.
