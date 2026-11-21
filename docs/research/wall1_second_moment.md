# Second moments for the selected terminal block

Fix the planting, sample the matrix as in [the planted ensemble](usvp_planted.md), and let the algorithm draw its coins conditionally on that input. Assume it returns a basis almost surely. All expectations below use this joint law, including the choice of prefix. There is a sharp two-moment bound for the selected block, but independent reruns on the same input do not in general estimate its factorial second moment.

## A sharp interval from three scalar quantities

Let Q be the projected lattice and v the projected plant. Let G mean that v is nonzero and primitive in Q. On G count in N the unoriented primitive lines other than the line of v whose generator has length at most ‖v‖. Set N=0 off G. The closed ball counts ties as failures. Each count is finite by discreteness of Q. Assume finite second moment. Write

    g = Pr(G),    μ = E[N],    h = E[N(N−1)].

By the [corrected criterion](wall1_planted_flags.md), the recovery probability is exactly g − Pr(N>0). If μ=0 it equals g. Otherwise set k=floor(1+h/μ), so k≥1. Then

    max(0,g−μ) ≤ Pr(recovery) ≤ g − (2kμ−h)/(k(k+1)).

Indeed 1 on the positive integers is bounded above by N, and bounded below by (2kN−N(N−1))/(k(k+1)), since (N−k)(N−k−1)≥0 at every integer. At zero both polynomials vanish. This proves the bounds without a hypothesis about independence of distinct lines. Ordinary Cauchy–Schwarz gives the simpler lower bound μ²/(μ+h) on failure *inside G*. Thus a second-moment lower bound on occupancy points in the direction of **failure**.

The upper bound on recovery is attained by an abstract count law for every feasible triple (g,μ,h). Assign masses (kμ−h)/k and (h−(k−1)μ)/(k+1) at k and k+1 inside G, respectively. Both are nonnegative by the definition of k. Their sum is the displayed lower bound on occupancy, hence at most g by the inequality already proved for the feasible law. Fill the remaining mass on G and its complement with zeros. Direct substitution gives μ and h. This sharpness concerns what the three scalars imply without further geometric information.

## Two kinds of pair sampling

Condition on a matrix A and write m(A)=E[N|A]. For counts N₁,N₂ from two independent seeds on that matrix, E[N₁N₂]=E[m(A)²]. In contrast, h counts ordered pairs of distinct competing lines **in one output**. Subtracting and using conditional variance gives exactly

    h − E[N₁N₂] = E[Var(N|A)] − μ.

There is no independence assumption on lines within one basis. In particular the second moment of the mean of r independent reruns conditional on the input yields the unconditional variance formula

    Var((N₁+⋯+Nᵣ)/r) = Var(m(A)) + E[Var(N|A)]/r.

This follows by conditioning on A and summing the r conditional variances. For the deterministic verified slide loop the second summand vanishes identically. For a randomized variant, transferring any probability estimate to that loop would require an argument relating their outputs.

## A small exact planted example

Take m=n=1, q=3, e=s=0, and use the full terminal block of dimension three. The plant is the last unit vector and the congruence is x+Ay=0 modulo 3. Every nonzero vector has length at least one. The vectors of length one are signed coordinate vectors. The x axis never qualifies, the y axis qualifies exactly when A=0, and the planted axis always qualifies. Hence G is certain and N is Bernoulli(1/3), for every choice of a fully reduced output and every tie rule. In particular

    μ=1/3,    h=0,    E[N₁N₂]=1/3,    Var(m(A))=2/9.

The interval gives recovery exactly 2/3. Arbitrarily many reruns leave the unconditional variance of their average at 2/9. This example isolates the pair-sampling error even with exact reduction. It uses an empty prefix, and the exceptional input has tied ambient minima. Conditioning on ambient uniqueness would remove that input.

## Remaining selected-prefix estimate

For a nonempty adaptive prefix the first bound would certify 99% recovery if (1−g)+μ≤0.01. A necessary condition for that same target, when μ>0, is (1−g)+(2kμ−h)/(k(k+1))≤0.01. These statements count the same-line defect exactly once. Evaluating h requires the joint inclusion probabilities of two different primitive lines at the radius of the projected plant for the *same selected prefix*, weighted by the probability that the algorithm returns that prefix on that matrix. Neither independent seeds nor two independent matrices supply those probabilities through their cross-product. No estimate of g, μ or h at a nontrivial GSA block size follows here.


## Independent audit (Nov 2026)

Verdict: **correct** (bounds, sharpness checked algebraically and on 2000 random laws; q = 3 example gives recovery exactly 2/3 with μ = 1/3, h = 0, E[N₁N₂] = 1/3). Nit: the example uses β = d (empty prefix).
