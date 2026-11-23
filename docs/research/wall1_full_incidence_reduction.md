# Reducing draw-14 component errors to connected full incidences

This paper reduction replaces the large proper-subset envelope in Part 276 with
an error below 4.107e-197, including its mixtures with full-incidence terms,
**provided the full-incidence transfer reaches the stated target**. That target
is not proved. No new unconditional draw-14 or later-history bound follows yet.
The proof uses the actual q=3329 geometry, with exact finite regression checks
and outward interval evaluation, but is not Lean-formalized.

## Ordered counts and a dependent-set generating function

Use the fixed raw candidate ball and input fibers of Parts 250 and 252. Write
rho_y for a fiber density, mu=sum rho_y, and P(T) for joint incidence on distinct
inputs T. For h>=3 define

\[
 F_h=\sum_{\substack{(y_1,\ldots,y_h)\text{ distinct}\\
              \text{augmented input matroid connected}}}P(\{y_1,\ldots,y_h\}).
\]

All counts here are ordered. Let M_j be the same sum of P(T) over all dependent
j-input supports, and D_j the corresponding sum of product_y rho_y. Independence
of evaluations on direct-sum input spans gives

\[
 M_j\le j![z^j]e^{\mu z}
            \left(\exp\left(\sum_{h=3}^{24}F_h z^h/h!\right)-1\right)
               =:\widehat M_j \qquad (j\le24).                 \tag{1}
\]

Indeed a matroid decomposes uniquely into connected components. Its singleton
components contribute their densities; its other components have size at least
three because the augmented inputs are distinct. A dependent support has at
least one nonsingleton component. Partition the ordered positions among these
components and multiply their joint probabilities, which factor on direct sums.
Dropping distinctness and direct-sum restrictions between independently chosen
components only increases the sum. This gives the exponential generating function
in (1), including all disconnected dependent supports.

For the independent product there is a simpler estimate:

\[
                    D_j\le j q^{j-2}\rho_{\max}\mu^{j-1}.       \tag{2}
\]

Every dependent support has a position whose augmented input is in the span of
the others. Union over its j possible positions. Given the other inputs, that
span meets the affine hyperplane with first coordinate 1 in at most q^(j-2)
points. Summing the redundant input's density costs at most q^(j-2) rho_max;
the remaining unrestricted weighted sums cost mu^(j-1).

## Proper subsets: retain one redundant outer input

For a connected h-input support T and a proper dependent subset U of size j,
choose the first position outside U. Connectedness implies no coloops, so this
input lies in the span of the other h-1 augmented inputs. Fix all those other
inputs first. Sum the chosen outer input with its density weight, at cost at
most q^(h-2) rho_max. Sum the other h-j-1 outer inputs unrestricted, at cost
mu^(h-j-1). The discrepancy on U does not involve any outer input. Hence

\[
 \sum_{\substack{T\text{ ordered, connected}\\|T|=h}}
 \sum_{\substack{U\subsetneq T\\U\text{ dependent}}}
 |P(U)-\prod_U\rho_y|\prod_{T\setminus U}\rho_y
 \le q^{h-2}\rho_{\max}
       \sum_{j=3}^{h-1}{h\choose j}\mu^{h-j-1}(M_j+D_j).       \tag{3}
\]

The binomial chooses the positions of U. No further factor h-j is needed: for
each such choice the omitted outer position is fixed deterministically. This
argument avoids re-anchoring U on one circuit and completing all its points in
a single affine span, which caused the large loss in the previous envelope.

For each positive multiplicity pattern on T, the discrepancy from independent
Bernoulli variables is bounded by the envelope L(T) in Part 256. Split its full
subset term using |P(T)-product rho|<=P(T)+product rho and apply (1)--(3).
The summed connected activity is therefore at most F_h+E_h, where

\[
 E_h= hq^{h-2}\rho_{\max}\mu^{h-1}
 +q^{h-2}\rho_{\max}\sum_{j=3}^{h-1}{h\choose j}\mu^{h-j-1}
   (\widehat M_j+jq^{j-2}\rho_{\max}\mu^{j-1}).                  \tag{4}
\]

This is an unconditional symbolic bound. It retains the unknown full incidences
in (1), rather than claiming a small numerical error independently of them.

## Transfer and all mixed density errors

Let c_j(mu) be the coefficient of z^j in K_12(mu+z;mu)^2, and let c_j^+(mu)
be its coefficientwise absolute majorant. For activities A_h define

\[
 B_A(z)=\sum_{k=3}^{24}\frac{z^k}{k!}
                    \sum_{h=3}^k A_h S(k,h),\qquad
 G(z)=\mu(e^z-1-z),
\]

truncating all series at degree 24. Define the conservative normalized transfer

\[
 \mathcal T(A)=\frac{(12!)^2}{0.280\mu^{24}}
       \sum_{k=3}^{24}c_k^+(\mu)k![z^k]e^{G(z)}(e^{B_A(z)}-1). \tag{5}
\]

This uses D_12(mu)^2>=mu^24/(12!)^2. Equations (1)--(4) and the existing component
transfer give a total dependency correction at most T(F+E). Positivity and
linearity of B give the exact difference formula

\[
 \mathcal T(F+E)-\mathcal T(F)
 =\frac{(12!)^2}{0.280\mu^{24}}\sum_k c_k^+(\mu)k![z^k]
             e^{G(z)+B_F(z)}(e^{B_E(z)}-1).                    \tag{6}
\]

Unlike a proper-only transfer, (6) includes all products of full-incidence and
proper-subset errors. There is no subtraction of nearly equal numerical bounds.

For the actual draw-14 ball, the existing lower count and integer-ball upper
count give

\[
 58.15006220912<\mu<118.02042612281<119.
\]

Temporarily suppose F_h<=mu^h for 3<=h<=24. Evaluate every positive numerator
monomial in (1), (4), and (6) at the mean upper bound, and the denominator at the
mean lower bound. The existing fiber bound supplies rho_max. Outward interval
arithmetic proves

\[
                  \mathcal T(F+E)-\mathcal T(F)<4.107\,10^{-197}. \tag{7}
\]

## The mild caps follow from the desired transfer bound

The temporary caps introduce no additional obligation if T(F)<=3.01e-12:

* For 3<=h<=9 the existing circuit, rank-two and rank-extension envelopes already
  imply F_h<mu^h. Each envelope includes the full joint-probability term; its
  ratio to mu^h has only negative powers, so the lower mean suffices to check it.
* For 10<=h<=24, c_24=1/(12!)^2 and positivity in (5) imply
  T(F)>=S(24,h) F_h/(0.280 mu^24). Thus

\[
 \frac{F_h}{\mu^h}
 \le\frac{0.280(3.01\,10^{-12})119^{24-h}}{S(24,h)}<1.          \tag{8}
\]

The last inequalities are checked as exact rational inequalities for all 15
values of h. The largest right side is below 0.890, at h=10. The hypothesis
T(F)<=3.01e-12 is still unproved: (8) is an implication, not a certificate of it.

Combining the reference term, independent Bernoulli error, and (7) gives the
following useful conditional conclusion:

\[
 \mathcal T(F)\le3.01\,10^{-12}
 \quad\Longrightarrow\quad
 \Pr(b_{14}>0.280)<9.131\,10^{-13}+\mathcal T(F).               \tag{9}
\]

In particular, a sufficient remaining vertical-history obligation is

\[
 \mathcal T(F)+\Pr(\max_{15\le i\le404}b_i>0.280)
                                         \le3.0088\,10^{-12}. \tag{10}
\]

It implies the premise in (9), and its sum with 9.131e-13 is below the earlier
3.922e-12 history allowance. Counting the connected full incidences F_h sharply
enough, controlling subsequent selected projections, and the other BKZ success
conditions remain open. This reduction removes the need to bound proper-subset
terms by the unsuccessful one-circuit envelope; it does not supply the missing
multi-relation full-incidence counts.

Run `python3 docs/research/scripts/wall1_full_incidence_reduction.py`. It checks
84 exact rational inequalities over three nonuniform fiber configurations on
F_3^2 (including zero and full fibers), then the actual-parameter interval bounds
and exact cap implications. These finite regressions support, but do not replace,
the general arguments above.
