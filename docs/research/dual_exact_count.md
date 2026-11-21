# Exact dual-list moments for a punctured uniform design

At the 511-sample shape of [Part 39](wall1_projected_reference.md), the unguessed pure dual lattice has **no informative frequency at any radius** with probability greater than 0.99999990. This holds simultaneously for all sample prefixes. The corresponding primal embedding has a planted vector even on this event. Below are the exact list and Fourier moments for the plain independent-matrix model, including the case of a prescribed block of known secret coordinates. Module structure is outside this model.

## Theorem 1. Integer counts and projective multiplicity

Write $D=m'$ for the number of retained rows and $k$ for the number of retained secret columns. In the pure dual construction these dimensions determine the lattice $L=\{v\in\mathbb Z^D:A^Tv=0\pmod q\}$, where the retained matrix has independent uniform entries in the prime field. Fix the rows and columns before drawing the design. Removing columns gives a relation for the residual after their contributions have been correctly subtracted.

Choose one sign of each nonzero integer point in the closed ball of radius $R$, and omit zero residues. The resulting set $B$ has size
$$
 M=(C_D(\lfloor R^2\rfloor)-C_D(\lfloor R^2/q^2\rfloor))/2,
 \quad C_D(j)=\sum_{i=0}^j[t^i](\sum_{a\in\mathbb Z}t^{a^2})^D .
$$
Indeed the omitted integer points are precisely $q$ times the smaller ball, and negation acts freely on the rest. For each projective line $l$ in the field space let $c_l$ count elements of $B$ reducing into that line. Put $p=q^{-k}$. For the list size $X=|B\cap L|$,
$$
 EX=pM,\qquad \operatorname{Var} X=p(1-p)\sum_l c_l^2 .
$$
A column annihilates a fixed line with probability $1/q$, and two distinct lines with probability $1/q^2$, by surjectivity onto two coordinates. Independence across columns gives pairwise independent line indicators. Summing those indicators with weights $c_l$ proves both identities. For $M>0$ and $0<\theta<1$, Paley–Zygmund gives
$$
 \Pr[X\ge\theta pM]\ge
 \frac{(1-\theta)^2}{1+(1-p)\sum_l c_l^2/(pM^2)}.
$$
Chebyshev also bounds the lower-tail failure by $(1-p)\sum_l c_l^2/((1-\theta)^2pM^2)$. Both bounds apply to an exhaustive radius list. Repeated lifts and scalar multiples enter the squared multiplicities even after identifying signs.

**Numerical obstruction.** The expected number of annihilated projective lines in the entire space is $(q^D-1)q^{-k}/(q-1)$. Markov therefore bounds the probability of *any* informative frequency, independently of the radius. At $D=511,k=512,q=3329$ this is less than $1/(3329\cdot3328)<9.03\times10^{-8}$. Zero extension sends every prefix relation into the full left kernel. Thus puncturing cannot improve this probability. At 512 rows the corresponding upper bound is $1/3328$. These obstructions concern pure dual relations without guessing. Guessing columns changes $k$, and an augmented dual embedding would change the lattice itself.

## Theorem 2. Exact conditional score moments

Condition on the design and the correctly subtracted columns. Let $S=B\cap L$, $N=|S|$, and use the sum of cosines at these frequencies, evaluated on a single right-hand side. Assume independent CBD(3) errors independent of the design. Write
$$
 F(w)=\prod_{j=1}^D\cos^6(\pi w_j/q).
$$
One difference of independent fair bits has Fourier transform $|(1+\exp(2\pi i w_j/q))/2|^2$. Three differences per coordinate and independence give the displayed expression. The secret term vanishes modulo $q$ for every surviving frequency. The mean is $H=\sum_{v\in S}F(v)$, and the variance is
$$
 V_E=\tfrac12\sum_{u,v\in S}(F(u-v)+F(u+v))-H^2 .
$$
This follows from the cosine product identity. Under a uniform right-hand side the mean is zero and the same second-moment formula uses $F(w)=\mathbf1_{w=0\bmod q}$, by character orthogonality. Denote this variance by $V_U$. If $R<q/2$, distinct sign representatives have distinct residues up to sign, so $V_U=N/2$.

For $H>0$ the midpoint test has acceptance-probability gap at least $1-4(V_E+V_U)/H^2$, by Chebyshev in the two experiments. Thus $H^2\ge16(V_E+V_U)$ suffices for gap $3/4$. This is an inspectable criterion for a particular list. The CBD norm law alone cannot evaluate the pair sum, since it discards the coordinate phases. Even one-dimensional frequencies 1 and 2 have dependent cosines, with the second equal to twice the square of the first minus one. Taking $R$ arbitrarily large repeats residues and can increase the integer count without adding a single new character. Independent Gaussian draws with a fixed instance, as in [Pouly–Shen](https://eprint.iacr.org/2023/1508), use a different concentration argument.

## Scope of a cost comparison

For the 511-row unguessed family, on the full-row-rank event every dual score is constant in the right-hand side. The average distinguishing gap of a test using only these scores and the design is consequently below $9.03\times10^{-8}$, even with free exhaustive listing. For a constant-gap target such as $3/4$, the feasible set over all prefixes and radii in this family is empty.

A direct provable listing bound for a fixed radius is $O(D^2 k\,(2\lfloor R\rfloor+1)^D)$ elementary integer operations for $D,k\ge1$, by scanning the enclosing box and testing the norm and modular equations (operand lengths depend on $D,k,q,R$). Explicit output takes at least one write per vector. The heuristic sieve exponent $0.2925D$ gives 149.47 leading bits at $D=511$. It prices neither exhaustive output at arbitrary radius nor a successful test at this dimension.

For guessed columns or additional samples, the two theorems alone give no optimized numerical constant-advantage cost. One still needs a quantitative bound on the CBD pair sum or another score-tail argument, and the cost and null acceptance probability for searching the guesses. Correct-guess conditional moments cannot certify the maximum over guesses. The corrected Pouly–Shen estimate of 238 bits uses 1023 equations and 19 guessed coordinates. The repository reproduces 237.98 modeled bits, or 262.92 with its explicit polynomial charges, versus 149.88 for its dual estimator. None is a certified all-vectors enumeration cost. [Cost decomposition](pouly_shen_cost.md) · [Fixed-instance bounds](pouly_shen_tight.md) · [Rounded-score analysis](matzov_rigorous.md)
