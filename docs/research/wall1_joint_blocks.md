# Joint failure of coordinate blocks: shared rows, list decoding, and the multi-block ceiling

Parts 131–132 left three structural questions about A-independent coordinate blocks for plain LWE. This note answers them using one tool, a *witness calculus* that turns every joint membership probability into a finite-field rank count.

1. **Blocks on shared rows with disjoint secret deletions.** Part 132 showed that these blocks are not conditionally independent. The right replacement is an exact conditional covariance identity (Theorem 1) and a k-block bound (Theorem 2): conditional on the plant, joint failure is at most the product of the per-block first moments plus *circuit terms*. A circuit term is exponentially small in the deletion size j. Conditional negative dependence is false (Proposition 3, an explicit example). Sharing the error rows makes the averaged bound no better than the disjoint-row product (Proposition 4).
2. **List decoding.** For list-then-verify, the statistic that suffices is the first moment of the primal ball count at the list radius (Theorem 6). For coordinate-plane designs, exact finite-field counting gives this first moment unconditionally (Theorem 5). With list decoding, the joint failure of any family of blocks is a pure norm event plus a sum of first moments, so no joint estimate over the design is needed (Theorem 7). Cost still requires an output-sensitive enumeration oracle.
3. **Ceiling.** For conditionally independent blocks, joint failure is $E_s[\varphi(s)^k]$. It is pinned between explicit secret-norm tails (Lemma 8, Theorems 9–10). A Paley–Zygmund bound gives the first rigorous *lower* bound on the true failure of exact-SVP blocks. The conjectured sharp asymptotic is
$$P_k\approx\Pr\big(\|s\|^2+1+Q_{\|e_R\|^2}(1/k)\ge\rho^*\big),$$
where $Q$ is a lower quantile and $\rho^*$ is a Gaussian-heuristic-type threshold. At the recorded 646 design this formula matches the exact bound within 15% for $2\le k\le10^6$. The bound's floor is $3.43\cdot10^{-11}$. Shared-row families have a far higher floor: the plant-norm tail, ≈ 0.0124 at k = 1.

Throughout: plain LWE $b=As+e$ over prime $q$, $A\in\mathbb F_q^{m\times n}$ uniform, $e,s$ iid centred with support $[-\eta,\eta]$ (CBD(η)), with $(m,n,q,\eta)=(511,512,3329,3)$ as the running example. All statements are for general parameters unless a number is quoted. Ties count as failures.

## 0. Setting and notation

A *coordinate block* is a pair $(R,J)$ with $R\subseteq[m]$ a set of $r$ kept rows and $J\subseteq[n]$ a set of $j$ deleted secret coordinates. Its retained coordinates are $S=R\sqcup([n]\setminus J)\sqcup\{t\}$. Let $\Lambda_R=\{(x,y,t)\in\mathbb Z^R\times\mathbb Z^n\times\mathbb Z:\ x+A_Ry\equiv tb_R\}$. The block lattice is $\Lambda_{R,J}=\pi_S(\Lambda_R)$. Its dimension is $D=r+n-j+1$, and its covolume is $q^{r-\operatorname{rank}A_{R,J}}$ (Part 40). The projected plant is $v=\pi_S(u)$ with $u=(e_R,s,1)$. Write $\rho=\|v\|^2$ and $R_v=\|v\|$. The Part 39 block is the case $J=\varnothing$.

For $z=(x,y',t)\in\mathbb Z^S$ define the discrepancies $X(z)=x-te_R\in\mathbb F_q^R$ and $Y'(z)=y'-ts_{J^c}\in\mathbb F_q^{J^c}$. Define the witness set
$$E(z)=\{W\in\mathbb F_q^n:\ W|_{J^c}=Y'(z)\},$$
an affine space of size $q^j$. Let $C^\pm$ be one representative of each signed pair of nonzero integer points with $\|z\|\le R_v$, excluding $\pm v$. Its size is $n_{\rm c}\le(N_D(\rho)-1)/2$, where $N_D(\rho)=\#\{z\in\mathbb Z^D:\|z\|^2\le\rho\}$. Failure is $F=\{\Lambda_{R,J}\cap C^\pm\ne\varnothing\}$.

**Hypothesis (H)** for a block and a plant: $R_v\sqrt{1+B^2}<q$ and $2R_v<q$, where $B=\|(e_R,s)\|_\infty$. As in Part 39, the first condition forces every $z$ in the ball with $X(z)=0$ and $Y'(z)=0$ to lie in $\mathbb Z v$. Hence every $z\in C^\pm$ has nonzero discrepancy. The second condition makes two ball points congruent mod $q$ equal. Both conditions hold for every CBD(3) plant at the radii used here, since $R_v\le\sqrt{2000}$.

The **first moment** of the block is $\mu:=n_{\rm c}\,q^{j-r}$. For $j=0$ this is Part 39's $(N_D(\rho)-1)/(2q^r)$, up to the $-3$ versus $-1$ convention. A block with $r=r_0+j$ rows and $j$ deletions has the same $D$ and the same $q^{r-j}$ as a Part 39 block with $r_0$ rows. So its first moment is the same function of $\rho$.

## 1. Witness calculus

**Lemma 1 (witnesses).** For every $z\in\mathbb Z^S$:
$$\#\{W\in E(z):A_RW=-X(z)\}=\mathbf 1\{z\in\Lambda_{R,J}\}\cdot q^{\,j-\operatorname{rank}A_{R,J}}.$$
In particular, $z\in\Lambda_{R,J}$ if and only if $z$ has a witness.

*Proof.* $z\in\pi_S\Lambda_R$ if and only if some $y_J\in\mathbb Z^J$ gives $x+A_R(y',y_J)\equiv tb_R$. Subtract $tb_R=t(e_R+A_Rs)$. The condition becomes $X(z)+A_RW=0$ with $W=y-ts$. Here $W|_{J^c}=Y'(z)$, and $W|_J$ runs over all of $\mathbb F_q^J$ as $y_J$ runs over $\mathbb Z^J$. For fixed $W|_{J^c}$, the solutions in $W|_J$ form either the empty set or a coset of $\ker A_{R,J}$, which has size $q^{j-\operatorname{rank}}$. ∎

Write $\tilde N=\sum_{z\in C^\pm}\#\{W\in E(z):A_RW=-X(z)\}$ for the *witness count*. Then $\tilde N\ge1$ if and only if $F$ occurs, and $\tilde N=N:=\#(\Lambda_{R,J}\cap C^\pm)$ when $A_{R,J}$ has full column rank.

**Lemma 2 (row-wise rank formula).** Take blocks $(R_i,J_i)$, vectors $W_i\in\mathbb F_q^n$ and targets $X_i\in\mathbb F_q^{R_i}$. Then
$$\Pr_A\big(A_{R_i}W_i=-X_i\ \forall i\big)=\mathbf 1\{\text{consistent}\}\prod_{a\in\cup R_i}q^{-\operatorname{rank}\{W_i:\ a\in R_i\}}.$$
"Consistent" means: for each row $a$, every linear relation $\sum_{i\ni a}c_iW_i=0$ implies $\sum_{i\ni a} c_iX_i[a]=0$.

*Proof.* The rows $A_a$ are independent and uniform on $\mathbb F_q^n$. For a fixed row $a$, the map $A_a\mapsto(\langle A_a,W_i\rangle)_{i\ni a}$ is uniform onto its image, which has dimension equal to that rank. ∎

With disjoint rows, every rank above is 1, and Lemma 2 recovers the conditional independence of Part 132. With fully shared rows ($R_i=R$), the exponent is $-r\cdot\operatorname{rank}(W_1,\dots,W_k)$.

**Corollary (single block, no rank conditioning).** Under (H):
- $\Pr(F\mid u)\le E[\tilde N\mid u]\le\min\{1,\mu\}$.
- Exactly, $E[\tilde N\mid u]=q^{-r}(n_{\rm c}q^j-n_0)$, where $n_0=\#\{z\in C^\pm:Y'(z)=0\}$.

The first item removes the full-rank conditioning that Part 40 used for secret-deleting blocks. *Proof.* Every $z\in C^\pm$ has nonzero discrepancy. If $Y'(z)=0$, the witness $W=0$ needs $X(z)=0$ and contributes nothing. Every nonzero witness contributes $q^{-r}$ by Lemma 2. ∎

## 2. Shared rows, disjoint secret deletions

Fix a row set $R$ ($|R|=r$) and pairwise disjoint $J_1,\dots,J_k\subseteq[n]$. Block $i$ is $(R,J_i)$, with data $v_i,R_i:=\|v_i\|,C_i^\pm,\mu_i,\tilde N_i$. Condition on $u$ throughout, so the only randomness is $A_R$. Assume (H) for every block.

### 2.1 Exact conditional covariance

For two blocks on the common rows $R$ (here $J_1,J_2$ may be arbitrary), define three counts over pairs of nonzero witnesses $((z_1,W_1),(z_2,W_2))$, with $z_i\in C_i^\pm$ and $W_i\in E_i(z_i)\setminus\{0\}$:
- $M_i=\#\{(z_i,W_i)\}$, the number of nonzero witnesses of block $i$;
- $\mathrm{Par}=\#\{$pairs with $W_2\in\mathbb F_q^*W_1\}$;
- $\mathrm{Dep}=\#\{$pairs with $W_2=\lambda W_1$ and $X(z_2)=\lambda X(z_1)$ for some $\lambda\in\mathbb F_q^*\}$.

**Theorem 1.** $E[\tilde N_i\mid u]=q^{-r}M_i$, and
$$E[\tilde N_1\tilde N_2\mid u]=q^{-2r}(M_1M_2-\mathrm{Par})+q^{-r}\mathrm{Dep}.$$
Hence
$$\operatorname{Cov}(\tilde N_1,\tilde N_2\mid u)=q^{-r}\big(\mathrm{Dep}-q^{-r}\mathrm{Par}\big),\qquad \Pr(F_1\cap F_2\mid u)\le E[\tilde N_1\tilde N_2\mid u].$$

*Proof.* Zero witnesses contribute nothing (Corollary). For a pair of nonzero witnesses, Lemma 2 gives $q^{-2r}$ if the two are independent, and $q^{-r}\mathbf 1\{X_2=\lambda X_1\}$ if $W_2=\lambda W_1$. ∎

So the conditional covariance is exactly $q^{-r}$ times the excess of $X$-consistent parallel witness pairs over their uniform expectation $q^{-r}\mathrm{Par}$. This is the "weaker statement" that replaces independence. It is an identity, not an estimate, and every term is a finite count determined by $u$.

### 2.2 The k-block circuit bound

For $S\subseteq[k]$ with $|S|\ge2$, put $l=\max S$, $I=S\setminus\{l\}$ and $j_I=\sum_{i\in I}j_i$. Define
$$\kappa_S=(2\lfloor R_l\rfloor+1)\,(q-1)^{|I|}\,\frac{N_{j_I}(R_l^2)}{q^{j_I}}.$$

**Theorem 2.** Under (H), for every plant $u$,
$$\Pr\Big(\bigcap_{i=1}^kF_i\ \Big|\ u\Big)\ \le\ \prod_{i=1}^k\mu_i\ +\sum_{S\subseteq[k],\,|S|\ge2}\kappa_S\prod_{i\in S\setminus\max S}\mu_i .$$
The bound also holds with $[k]$ replaced by any subfamily $T$, since $\bigcap_{[k]}\subseteq\bigcap_T$. In particular, blocks with $\mu_i\ge1$ may be dropped. No rank condition on $A_{R,\cup J_i}$ is needed.

*Proof.*
1. **Witness tuples.** If every $F_i$ occurs, then by Lemma 1 there is a valid tuple $(z_i,W_i)_{i\le k}$ with $z_i\in C_i^\pm$, $W_i\in E_i(z_i)$ and $A_RW_i=-X(z_i)$. All $W_i\ne0$, as in the Corollary.
2. **Full-rank tuples.** By Lemma 2 each has probability $q^{-rk}$. The number of such tuples is at most $\prod_i n_{{\rm c},i}q^{j_i}$. So their total contribution is at most $\prod\mu_i$.
3. **Reduction to circuits.** A rank-deficient tuple of nonzero vectors contains a *circuit*: a minimal dependent subset $S$ with $|S|\ge2$. Let $l=\max S$ and $I=S\setminus l$. Then $W_I$ is independent and $W_l=\sum_{i\in I}\lambda_iW_i$ with every $\lambda_i\ne0$. By Lemma 2, a valid circuit sub-tuple has probability $q^{-r|I|}$ and requires $X(z_l)=\sum\lambda_iX(z_i)$. So it suffices to count the circuit configurations $(z_I,W_I,\lambda,z_l)$.
4. **Counting circuits.** Fix $z_I$, $\lambda\in(\mathbb F_q^*)^I$ and the height $t_l$ of $z_l$, which has $2\lfloor R_l\rfloor+1$ possible values.
   - $x_l\equiv t_le_R+\sum\lambda_iX(z_i)$ is determined.
   - On a coordinate outside $\cup_{i\in I}J_i\cup J_l$, the value $y_l\equiv t_ls+W_l$ is determined by the fixed parts $W_i|_{J_i^c}=Y_i'(z_i)$.
   - On $J_i$ with $i\in I$, we have $J_i\subseteq J_{i'}^c$ for every $i'\ne i$, because the deletion sets are disjoint. So $W_l|_{J_i}=\lambda_iW_i|_{J_i}+(\text{fixed})$, where $W_i|_{J_i}\in\mathbb F_q^{J_i}$ is the only free part of $W_i\in E_i(z_i)$.

   Hence $(W_i|_{J_i})_{i\in I}\mapsto z_l|_{\cup_IJ_i}$ is injective, coordinatewise affine with nonzero slopes. Since $2R_l<q$, a short $z_l$ is determined by its residues. So the number of free choices compatible with $\|z_l\|\le R_l$ is at most $N_{j_I}(R_l^2)$. The total count is at most $\prod_{i\in I}n_{{\rm c},i}\cdot(q-1)^{|I|}(2\lfloor R_l\rfloor+1)N_{j_I}(R_l^2)$. Multiplying by $q^{-r|I|}=\prod_{i\in I}q^{j_i-r}\cdot q^{-j_I}$ gives $\kappa_S\prod_{I}\mu_i$. ∎

The pairwise terms dominate: $\kappa_{\{i,l\}}=(2\lfloor R_l\rfloor+1)(q-1)N_{j_i}(R_l^2)/q^{j_i}$. Since $N_j(\rho)$ grows only polynomially in $j$ at fixed $\rho$, $\kappa_S$ decays like $q^{-(1-o(1))j_I}$ once $j\log q\gg\log N_j(\rho)$. The same counting applied to one block gives a single-block second moment, used in §4:
$$E[\tilde N^2\mid u]\le\mu^2+(q-1)(2\lfloor R_v\rfloor+1)\mu .\tag{2.1}$$

*Remarks.*
- **Overlapping deletion sets.** If the $J_i$ overlap, the gain in $\kappa_S$ is only over $J_i\setminus J_l$. With $J_i\subseteq J_l$ there is no gain, and the circuit term is of first-moment size.
- **Partially overlapping rows.** For row sets that partly overlap, Lemma 2 shows a circuit pays a deficit only on the rows in $\bigcap_{i\in S}R_i$.
- **Not sharp.** The factor $(q-1)^{|I|}(2R+1)$ counts all $(\lambda,t_l)$. Only those that make $z_l$ short matter (Conjecture A).

### 2.3 Sign of the dependence

**Proposition 3 (conditional negative dependence fails).** Take $q=31$, $r=3$, $n=4$, $e_R=(1,0,-1)$, $s=(1,-1,0,1)$, and blocks $J_1=\{1\}$, $J_2=\{2\}$. Both blocks have $\rho=5$, $n_{\rm c}=895$ and (H). Then:
- **Exact (Theorem 1):** $M_i=27699$, $\mathrm{Par}=592619$, $\mathrm{Dep}=4593$. So $E\tilde N_1E\tilde N_2=0.86449$, $E[\tilde N_1\tilde N_2]=1.01799$ and $\operatorname{Cov}=+0.15351>0$.
- **Monte Carlo ($2\cdot10^5$ draws of $A$):** $\Pr(F_i\mid u)\approx0.5622$ for each block and $\Pr(F_1\cap F_2\mid u)\approx0.3297$, compared with $0.5622^2=0.3161$. The difference is more than 8 combined standard errors. The Monte Carlo $E[\tilde N_1\tilde N_2]\approx1.0103$ is consistent with the exact value.

So the failure events are positively correlated given $u$. Here the bound of Theorem 2 is $23.4$, which is trivial: $q$ is small. The exact dependent term $q^{-r}\mathrm{Dep}=0.154$ is 150 times smaller than its bound $\mu\kappa$. (Scratch scripts `toy.py` and `toyexact.py`.)

**Proposition 4 (shared errors cost the averaging gain).** Fix $s$, and suppose every factor $g_i=\min(1,\mu_i)$ depends on $e_R$ only through $\|e_R\|^2$. This is the case for shared rows, and each $g_i$ is nondecreasing. Then $E_{e_R}[\prod g_i]\ge\prod E_{e_R}[g_i]$. This is Chebyshev's sum inequality for nonnegative functions of a single real variable that are monotone in the same direction. Hence the shared-row bound $E_u[\min(1,\prod g_i+\Delta)]$ is never better than the product of per-block averages over independent error blocks. Here $\Delta$ is the circuit sum of Theorem 2. ∎

Its ceiling (§4.3) is the probability that the shared norm pushes *every* block past threshold.

## 3. List decoding: the statistic that suffices, and when it is exact

### 3.1 Exact primal ball counts for coordinate planes

Let $\rho_J=\operatorname{rank}A_{R,J}$ for a uniform $r\times j$ matrix. Its law is the Landsberg rank distribution (see the [interior note](wall1_interior.md)). For a radius $\varrho$, split the closed-ball points $z\in\mathbb Z^S$, $\|z\|\le\varrho$, into three classes:
- $Z_0$: points with $X=Y'=0$;
- $N_{\ne}$: points with $Y'\ne0$;
- $N_{Y0}$: points with $Y'=0$ and $X\ne0$.

**Theorem 5 (exact first moment).** For every plant $u$ and every $\varrho$:
$$E_A\big[\#(\Lambda_{R,J}\cap \bar B(\varrho))\ \big|\ u\big]=Z_0+N_{\ne}\,\frac{E[q^{\rho_J}]}{q^{r}}+N_{Y0}\,E\Big[\frac{q^{\rho_J}-1}{q^r-1}\Big].$$
If $\varrho\sqrt{1+B^2}<q$, then $Z_0=\#\{tv:|t|\,\|v\|\le\varrho\}$. Restricting each class to $t=\pm1$ gives the exact expected number of height-±1 points. For $j=0$ the formula reads $Z_0+N_{\ne}q^{-r}$, the Part 39 count at an arbitrary radius.

*Proof.*
- If $Y'\ne0$, then $A_{R,J^c}Y'$ is uniform on $\mathbb F_q^r$ and independent of $A_{R,J}$. A uniform vector, shifted by the fixed $X$, lies in a subspace of dimension $\rho_J$ with conditional probability $q^{\rho_J-r}$.
- If $Y'=0$ and $X\ne0$, then $z\in\Lambda_{R,J}$ if and only if $X\in\operatorname{col}A_{R,J}$. The law of $A_{R,J}$ is invariant under $\mathrm{GL}_r$, so given its rank the column space is uniform among subspaces of that dimension. It contains a fixed nonzero vector with probability $(q^{\rho_J}-1)/(q^r-1)$.
- If $X=Y'=0$, the point is always in the lattice. ∎

This is the "selected primal ball count" Part 131 asked for, in the case where the plane is A-independent. The rectangular counterexample of Part 131 does not apply here. That counterexample shows that a minimum and a determinant do not control occupancy. Theorem 5 averages over the design instead of using such invariants. It is exact and unconditional, and it needs no Gaussian heuristic and no uniform-translate assumption (compare [list_success](wall1_list_success.md)).

### 3.2 List-then-verify

**Procedure LIST$(R,J,\varrho;V)$.**
1. Output all points of $\Lambda_{R,J}\cap\bar B(\varrho)$. This uses an exact enumeration oracle (assumption below).
2. For each point of height $\pm1$, orient it to $t=+1$ and read the candidate $(\hat e_R,\hat s_{J^c})$.
3. If $\operatorname{rank}A_{R,J}=j$, solve $A_{R,J}\hat s_J=b_R-\hat e_R-A_{R,J^c}\hat s_{J^c}$ (Part 40).
4. Decode $\hat s$ to its representative in $[-\eta,\eta]^n$, if one exists.
5. Accept if every reserved row $a\in V$, with $V\cap R=\varnothing$ and $|V|=v$, has centred residual $b_a-\langle A_a,\hat s\rangle$ in $[-\eta,\eta]$.

**Theorem 6 (what suffices).** Conditional on $u$:
$$\Pr(\text{LIST does not output exactly }s)\le\mathbf 1\{\|v\|>\varrho\}+\frac{q^{j}-1}{(q-1)q^r}+\Big(\frac{2\eta+1}{q}\Big)^{v}E\big[\#\{\text{height-}\pm1\text{ points in }\bar B(\varrho)\}\mid u\big].$$
For any $L>0$, the list size exceeds $L$ with probability at most $E[\#(\Lambda_{R,J}\cap\bar B(\varrho))]/L$.

*Proof.*
- If $\|v\|\le\varrho$, the plant is listed. On full rank, the lift is the true $s$, which always passes verification (Part 132).
- Rank deficiency of $A_{R,J}$ is bounded by a union over the $(q^j-1)/(q-1)$ projective kernel lines, each of probability $q^{-r}$.
- Given $s$, the list depends only on the rows in $R$. The reserved rows are independent of them, so each wrong residue passes with probability $((2\eta+1)/q)^v$ (Part 132). Take the expectation over the list.
- The list-size bound is Markov's inequality. ∎

So the statistic that suffices is the first moment of the selected primal ball count at the list radius, restricted to heights ±1 for false acceptance and unrestricted for output size. No uniqueness, minimum, determinant or second moment is needed. Each piece is also necessary for this decoder:
- the radius event is exactly the miss event;
- the output size is at least the occupancy;
- [list_success](wall1_list_success.md) and Part 131 show that a minimum and a determinant do not determine occupancy.

For coordinate planes, Theorem 5 supplies every term exactly.

**Cost (not proved).** Step 1 assumes an oracle that enumerates $\Lambda\cap\bar B(\varrho)$ at a cost bounded by a function of $D$ times the occupancy at some radius $c\varrho$. Theorem 5 gives that occupancy's mean as well. Fincke–Pohst/Kannan enumeration does not fit this form: its tree levels are projections in a reduced basis, which are not coordinate planes. In the coordinate basis with the $q e_x$ vectors first, the upper levels are sample-deleted lattices covered by Theorem 5, but the deepest levels are $\mathbb Z^{n-j+1}$-type with astronomically large counts. A proven output-sensitive oracle is therefore an assumption, on the same footing as the "one exact SVP call" of Part 39.

### 3.3 List decoding removes the need for any joint design estimate

**Theorem 7 (linearization).** Take any finite family of coordinate blocks $(R_i,J_i,\varrho_i)$. Row sets may overlap arbitrarily, but every $R_i$ must avoid a common reserved set $V$. Run LIST on every block and output the accepted candidate. Then
$$\Pr(\text{fail})\le\Pr_u\big(\forall i:\ \|v_i\|>\varrho_i\big)+\sum_i\Big[\frac{q^{j_i}-1}{(q-1)q^{r_i}}+\Big(\tfrac{2\eta+1}{q}\Big)^{v}E[\#\text{cand}_i]\Big].$$
Conversely, $\Pr(\text{fail})\ge\Pr_u(\forall i:\|v_i\|>\varrho_i)$.

*Proof.* Take a union bound over blocks of the rank and false-acceptance events. Success needs only one block that lists its plant. If no block lists the plant, the true secret is never produced. ∎

The design randomness enters only additively, through first moments, so no conditional independence or covariance is needed. The joint failure is the deterministic norm event $\{\forall i:\|v_i\|>\varrho_i\}$. For disjoint rows it equals $E_s\big[\prod_i\Pr_{e}(\|e_{R_i}\|^2>\varrho_i^2-1-\|s_{J_i^c}\|^2)\big]$.

## 4. The ceiling of the multi-block method

### 4.1 Two-sided k-th moments

**Lemma 8.** Let $\varphi\in[0,1]$ be a random variable and $k\ge2$. Then
$$\tfrac14\Pr(\varphi\ge1-\tfrac1k)\ \le\ E[\varphi^k]\ \le\ \inf_{a>0}\big[\Pr(\varphi\ge1-\tfrac ak)+e^{-a}\big],$$
and $E[\varphi^k]\downarrow\Pr(\varphi=1)$ as $k\to\infty$. Moreover $k\mapsto E\varphi^k$ is log-convex, so $E\varphi^{k+1}/E\varphi^k$ is nondecreasing.

*Proof.* On $\{\varphi\ge1-1/k\}$ we have $\varphi^k\ge(1-1/k)^k\ge1/4$. Also $\varphi^k\le e^{-k(1-\varphi)}$. Log-convexity follows from Cauchy–Schwarz. ∎

For blocks that are conditionally iid given a shared variable $G$, joint failure is $E[\varphi(G)^k]$, where $\varphi(G)$ is the conditional failure. So **joint failure is governed by the probability that the shared randomness makes a single block's conditional failure at least $1-1/k$**. This is the general structural law. For disjoint rows, $G=s$ (Part 132).

### 4.2 A lower bound on the true failure

**Theorem 9 (Paley–Zygmund converse).** Use strict competitors, $\|z\|<\|v\|$. Let $\mu^<=n_{\rm c}^<q^{j-r}$, $\delta=q^{-r}n_0^<$ and $c=(q-1)(2\lfloor R_v\rfloor+1)$. Under (H), the probability that the block has a strictly shorter competitor (so an exact SVP call does not return $\pm v$) satisfies
$$\Pr(F^<\mid u)\ \ge\ \frac{(\mu^<-\delta)^2}{(\mu^<)^2+c\mu^<}\ \ge\ 1-\frac{c+2\delta}{\mu^<}.$$

*Proof.* Apply Paley–Zygmund to $\tilde N^<$. Its exact mean is $\mu^<-\delta$ (Corollary). Its second moment is at most $(\mu^<)^2+c\mu^<$ by (2.1): independent witness pairs give at most $(\mu^<)^2$, and a dependent pair is fixed by $(z,W,\lambda,t')$. ∎

Hence, for **any** family of coordinate blocks,
$$\Pr\Big(\bigcap_iF_i^<\Big)\ \ge\ E_u\Big[\Big(1-\sum_i\frac{c_i+2\delta_i}{\mu_i^<(u)}\Big)^+\Big].$$
For disjoint rows this sharpens by conditional independence to $E_s\big[\prod_iE_{e_{R_i}}[(1-(c_i+2\delta_i)/\mu_i^<)^+]\big]$. These bounds hold for the actual exact-SVP procedure, not only for a certificate.

### 4.3 Ceiling formulas

Write $\rho(\beta)=\min\{\rho:\mu(\rho)\ge\beta\}$ and $\rho^<(M)=\min\{\rho:\mu^<(\rho)\ge M\}$. For equal blocks both are functions of $(D,r-j)$ alone. Let $Q^+(p)=\max\{x:\Pr(\|e_R\|^2<x)\le p\}$, the lower quantile of the block's error norm. Let $\bar c$ be the maximum of $c+2\delta$ over the radii in play.

**Theorem 10 (disjoint rows, exact-SVP blocks, k equal blocks).** Let $f(\sigma)=E_{e_R}\min\{1,\mu(\|e_R\|^2+\sigma+1)\}$ be Part 131's per-secret bound, and let $p(\sigma)$ be the true conditional failure. Then:
1. **Exact representation.** $P_k=E_s[p(\|s\|^2)^k]$, and $E_s[g^k]\le P_k\le B_k:=E_s[f^k]$, where $g$ is Theorem 9's conditional lower bound averaged over $e_R$.
2. **Floor.** $B_k\downarrow\Pr(\|s\|^2+1\ge\rho(1))$ as $k\to\infty$. Also $B_k\ge B_3(B_3/B_2)^{k-3}$ for $k\ge3$ (log-convexity).
3. **Closed-form bracket.** For every $a>0$,
$$\tfrac14\Pr\big(\|s\|^2+1+Q^+(\tfrac1{2k})\ge\rho^<(2k\bar c)\big)\ \le\ P_k\ \le\ B_k\ \le\ \Pr\big(\|s\|^2+1+Q^+(\tfrac{2a}k)\ge\rho(\tfrac ak)\big)+e^{-a}.$$
4. **Row budget.** The design needs $kr\le m-v$ rows.

*Proof of 3.*
- **Lower.** We have $g(\sigma)\ge(1-\frac1{2k})\Pr_e(\|e\|^2+\sigma+1\ge\rho^<(2k\bar c))$. If $\Pr_e(\|e\|^2<\rho^<(2k\bar c)-\sigma-1)\le\frac1{2k}$, then $g\ge1-\frac1k$. Apply Lemma 8.
- **Upper.** For every $\beta\in(0,1)$, splitting on $\{\mu\ge\beta\}$ gives $f(\sigma)\le\Pr_e(\|e\|^2+\sigma+1\ge\rho(\beta))+\beta$. With $\beta=a/k$, the event $f\ge1-a/k$ forces $\Pr_e(\|e\|^2<\rho(a/k)-\sigma-1)\le2a/k$, that is $\sigma\ge\rho(a/k)-1-Q^+(2a/k)$. Apply Lemma 8. ∎

**Shared rows (Theorem 2 family).** The method's bound satisfies $B^{\rm sh}_k\ge\Pr_u(\min_i\mu_i(u)\ge1)$. The true failure satisfies $P^{\rm sh}_k\ge(1-k\bar c/M)\Pr_u(\min_i\mu_i^<(u)\ge M)$ for every $M$. For equal blocks with $r=r_0+j$, each $\|v_i\|^2$ has the law of a single $r_0$-row block's $\|v\|^2$, and
$$\min_i\|v_i\|^2=1+\|e_R\|^2+\|s_K\|^2+\textstyle\sum_lS_l-\max_lS_l,\qquad S_l=\|s_{J_l}\|^2,\ K=[n]\setminus\cup J_l.$$
So the shared-row floor is the single-block plant-norm tail $\Pr(\|v\|^2\ge\rho(1))$. It is lowered only by the extreme-value fluctuation $\max_lS_l-E S_l=O(\sqrt{j\log k})$ and by the shift $O(\log(k\bar c))$, and it does **not** tend to 0 with k.

**List decoding (Theorem 7).** The failure is exactly the norm event, up to the additive first moments. Each block's threshold moves from $\rho(1)$ to $\varrho_i^2\approx\rho(L)$, where $L$ is the expected list budget.

**Unified statement.** Every multi-block scheme built from A-independent coordinate blocks has joint failure comparable to
$$\Pr_u\big(\forall i:\ \|v_i\|^2\ge\theta_i\big).$$
- For exact SVP, $\theta_i\in[\rho_i(\cdot),\rho_i^<(2k\bar c)]$, up to the explicit factors of Theorem 10.
- For list decoding with budget $L$, $\theta_i\approx\rho_i(L)$, and the two-sided statement is exact.

The design matrix contributes only the factor $\prod\mu_i$, which vanishes geometrically, and the circuit terms. The ceiling is set by the norm of the plant coordinates shared by all blocks: the secret alone for disjoint rows, and $(e_R,s_K)$ plus most of $s$ for shared rows.

### 4.4 Numbers at the recorded 646 design

Width 646: $r=133$, $n=512$, CBD(3). Computed by scratch scripts (`bk.py`, `lb.py`, `ceil.py`) in exact integer ball counts with float CBD laws. These values are not audited.

- **Reproduction.** $B_1,B_2,B_3=0.014905,\ 0.005908,\ 0.003682$, matching Part 131. Further values: $B_4=0.002709$, $B_8=0.001404$, $B_{64}=3.14\cdot10^{-4}$, $B_{1024}=7.55\cdot10^{-5}$, $B_{10^6}=6.50\cdot10^{-6}$.
- **Thresholds and floor.** $\rho(1)=1082$. The floor is $\Pr(\|s\|^2\ge1081)=3.43\cdot10^{-11}$. The single-block norm part is $\Pr(\|v\|^2\ge1082)=0.01243$ of $B_1=0.01491$.
- **Lower bounds on the true failure** (Theorem 9 with conditional independence): $9.09\cdot10^{-4}$ ($k=1$), $2.34\cdot10^{-4}$ ($k=2$), $1.20\cdot10^{-4}$ ($k=3$), $2.93\cdot10^{-8}$ ($k=10^6$).
- **Consequences.**
  - With 133-row blocks, the Part 39 bound cannot certify failure below $3.4\cdot10^{-11}$ for any number of blocks.
  - The true failure of exact-SVP blocks is above $2^{-64}$ for every $k\le10^6$.
  - Within $m=511$, the row budget caps $k\le3$.
  - The true single-call failure at 646 lies in $[9.09\cdot10^{-4},\,0.0149]$.
- **Closed-form bracket.** Theorem 10.3 is valid but loose, because thresholds differ by about 50 in $\rho$ and the tails are steep. For example, at $k=64$ it gives $[2.0\cdot10^{-7},\,4.0\cdot10^{-3}]$. The direct representations are much sharper.

## 5. Conjectures

**Conjecture A (diagonal dominance).** In Theorems 1–2 the dependent count is dominated by $\lambda=\pm1$ with equal heights: pairs that glue to a single short vector of $\Lambda_R$. Then the pairwise term is $O(\mu\,N_j(R^2)q^{-j})$ without the factor $(q-1)(2R+1)$. Evidence: in Proposition 3 the bound overestimates $q^{-r}\mathrm{Dep}$ by a factor of 150. Obstacle: Hadamard excludes modular coincidences $z_2\equiv\lambda z_1+\mu u$ only when $R_1\|u_{\rm common}\|R_2<q$, and at $(511,512,3329)$ we have $R^3\approx3\cdot10^4>q$.

**Conjecture B (sharp ceiling law).** For disjoint rows,
$$B_k\ \text{and}\ P_k\ \asymp\ \Pr\big(\|s\|^2+1+Q_{\|e_R\|^2}(1/k)\ge\rho^*\big),$$
with $\rho^*=\rho(1)$ for $B_k$, and $\rho^*$ within $O(1)$ of $\rho(1)$ for $P_k$. That is, the $\log(k\bar c)$ shift in Theorem 9 is an artifact. Evidence: with $\rho^*=1082$ the formula gives $0.00602, 0.00324, 0.00119, 2.76\cdot10^{-4}, 5.53\cdot10^{-6}$ against $B_k=0.00591, 0.00368, 0.00140, 3.14\cdot10^{-4}, 6.50\cdot10^{-6}$ for $k=2,3,8,64,10^6$. Asymptotically, Cramér's theorem gives $Q(1/k)\approx r\,x_k$ with $I(x_k)=\ln k/r$, where $I$ is the lower-tail rate function of a CBD square. $Q$ reaches 0 only at $k\approx(64/20)^r$.

**Conjecture C (selected planes).** For BKZ- or slide-selected planes, the primal analogue of Theorem 5 holds in mean up to a $2^{o(D)}$ factor. This is not implied by anything here. Part 131's counterexample shows it cannot follow from minimum or determinant information.

## 6. What is rigorous, and the remaining gap

**Rigorous** (general parameters; (H) only as stated):
- the witness calculus (Lemmas 1–2) and the single-block bound without rank conditioning;
- the exact conditional covariance (Theorem 1);
- the k-block circuit bound for shared rows with disjoint secret deletions (Theorem 2);
- the failure of conditional negative dependence (Proposition 3, an explicit finite example with an exact moment computation);
- the averaging penalty of shared errors (Proposition 4);
- the exact primal ball first moment for coordinate planes (Theorem 5);
- the sufficiency of that statistic for list-then-verify (Theorem 6) and the linearization over blocks (Theorem 7);
- the two-sided k-th moment law (Lemma 8);
- the Paley–Zygmund lower bound on true failure (Theorem 9);
- the floor and bracket formulas (Theorem 10).

The §4.4 numbers are scratch computations; only $B_1$–$B_3$ were previously recorded.

**Remaining gaps.**
1. **Sharpness of the circuit terms** (Conjecture A). Theorem 2 is useful only when $j$ is moderately large, because of the crude $(\lambda,t)$ count.
2. **The bracket in Theorem 10.** The upper and lower thresholds differ by $O(\log(kqR))$ in $\|v\|^2$, about 50 units at 646. Closing it, as in Conjecture B, needs a sharper lower bound on true failure than Paley–Zygmund with the crude dependent count.
3. **Cost.** List decoding needs a proven output-sensitive enumeration oracle. Exact SVP calls likewise have no proven cost here (Part 39).
4. **Structural ceiling.** A-independent coordinate blocks cannot beat the norm event of the shared plant coordinates. Disjoint rows are limited by the row budget $kr\le m-v$ and, as $k\to\infty$, by the secret-norm tail. Shared rows are limited by the plant-norm tail, which is comparable to a single block's failure. List decoding trades this tail for list size at rate $\log L\approx(D/2\rho)\,\Delta\rho$. None of this reaches the adaptive (BKZ-selected) planes, where the open problem of Parts 105–130 remains.

## Audit

**Verdict: MINOR CAVEATS.** Every theorem's proof was checked line by line against PROOF_GAP Wall 1 (Parts 39, 40, 92, 101, 131, 132, 134) and the Lean files `MultiBlock*.lean`. No proof is wrong in substance. The §4.4 numbers and Proposition 3 were recomputed independently: exact integer ball counts by the theta-power recurrence $kP_k=\sum_{t\ge1}2(Dt^2-(k-t^2))P_{k-t^2}$ (checked against the closed form at $\rho=3$), float CBD laws, and a separate Monte Carlo. The scripts are in the auditor's scratch directory and are not committed.

**Confirmed.**
- **Lemma 1, Lemma 2 and Theorem 1.** Lemma 1 is the coset count. Lemma 2 is the row-wise rank count. Theorem 1 is an identity: zero witnesses never count under (H), independent pairs contribute $q^{-2r}$, and parallel pairs contribute $q^{-r}\mathbf 1\{X_2=\lambda X_1\}$.
- **Theorem 2.**
  - The circuit reduction is sound: by minimality all $\lambda_i\ne0$ and $W_I$ is independent.
  - Disjointness gives $J_i\subseteq J_{i'}^c$, so $W_I|_{\cup J_i}\mapsto z_l|_{\cup J_i}$ is injective and coordinatewise affine.
  - $2R_l<q$ bounds the free choices by $N_{j_I}(R_l^2)$.
  - The algebra gives exactly $\kappa_S\prod_I\mu_i$, and no rank condition is used.
  - (2.1) is the same count with no gain, because the second block's $J$-part is deleted.
- **Proposition 3, recomputed exactly.** $\rho=5$, $n_{\rm c}=895$, $n_0=46$, $M_i=27699$, $\mathrm{Par}=592619$, $\mathrm{Dep}=4593$, $E\tilde N_1E\tilde N_2=0.864486$, $E[\tilde N_1\tilde N_2]=1.017992$, $\operatorname{Cov}=0.153506$. Theorem 2's bound is $23.399$, and $\mu\kappa/(q^{-r}\mathrm{Dep})=146$.
  - Independent Monte Carlo ($2\cdot10^5$ draws, different seed): $\Pr(F_1)=0.5636$, $\Pr(F_2)=0.5639$, $\Pr(F_1\cap F_2)=0.3307$ against a product of $0.3178$, about 12 standard errors apart. Positive conditional correlation is confirmed. The MC estimate of $E[\tilde N_1\tilde N_2]$ is heavy-tailed: 1.026 here and 1.010 in the note, both consistent with the exact 1.0180.
- **Proposition 4.** This is Chebyshev's sum inequality for nonnegative nondecreasing functions, by induction on k. Also $\min(1,\prod g+\Delta)\ge\prod g$.
- **Theorem 5.** The three cases are correct, including $\mathrm{GL}_r$-invariance for the column space given the rank. The explanation of why Part 131's rectangular counterexample does not apply is correct: that example refutes a deterministic implication from a minimum and a determinant, while Theorem 5 is an average over the design.
- **Theorem 6.** Correct. The independence of the list from the reserved rows is the content of `candidate_congr` and `verify_exact` in Lean. Counting both signs of each height-±1 point only loosens the bound by a factor of 2.
- **Lemma 8 and Theorem 9.** Both are correct, including $(\mu-2\delta)/(\mu+c)\ge1-(c+2\delta)/\mu$.
- **Theorem 10.** Items 1–4 and the two bracket derivations are correct. The floor limit uses $\Pr(\|e_R\|^2=0)>0$.
- **Conjectures A–C.** All three are clearly labelled as conjectures and are not used in any proof.
- **Recomputed §4.4 numbers.**
  - $\rho(1)=1082$.
  - $B_1,\dots=0.0149054,\ 0.0059079,\ 0.0036819,\ 0.0027085,\ 0.0014043\ (k=8),\ 3.144\cdot10^{-4}\ (64),\ 7.552\cdot10^{-5}\ (1024),\ 6.496\cdot10^{-6}\ (10^6)$.
  - Floor $\Pr(\|s\|^2\ge1081)=3.4265\cdot10^{-11}$, and $\Pr(\|v\|^2\ge1082)=0.012426$.
  - Theorem 9 lower bounds: $9.0946\cdot10^{-4},\ 2.3422\cdot10^{-4},\ 1.2048\cdot10^{-4},\ 2.9312\cdot10^{-8}$.
  - Conjecture B values: $0.006022,\ 0.003239,\ 0.001191,\ 2.758\cdot10^{-4},\ 5.526\cdot10^{-6}$.
  - The $k=64$ bracket is $[2.2\cdot10^{-7},\,3.9\cdot10^{-3}]$ with $\bar c=3328\cdot75$ at radius $\sqrt{1400}$ ($\delta$ is negligible). This is consistent with the note's $[2.0\cdot10^{-7},4.0\cdot10^{-3}]$, which depends on the choice of $\bar c$ and the grid for $a$.
- **Lean.** `MultiBlock.lean`, `MultiBlockProduct.lean`, `MultiBlockVerify.lean` and `MultiBlockAttack.lean` contain no `sorry`. They cover only disjoint-row, $J=\varnothing$ blocks: `multiblock_exact`, the verification bounds, and the end-to-end `attack_success`. They agree with the note's uses of Part 132. None of Theorems 1–10 is formalized, and the note does not claim otherwise. This audit did not rebuild the Lean.

**Issues and corrections.**
1. **Corollary, first bullet.** "$\Pr(F\mid u)\le E[\tilde N\mid u]\le\min\{1,\mu\}$" is false as written, since $E\tilde N$ can exceed 1. *Correction:* $\Pr(F\mid u)\le\min\{1,E[\tilde N\mid u]\}\le\min\{1,\mu\}$.
2. **Justification of (H).** "$R_v\le\sqrt{2000}$" does not hold for every CBD(3) plant. At 646 the maximum is $\|v\|^2=9\cdot645+1=5806$, and at full width it is 9208. The conclusion still holds, because $\sqrt{10\cdot9208}\approx303<q/2$.
3. **Theorem 10.1 notation.** The true conditional failure depends on all of $s$, not only on $\|s\|^2$: a competitor's norm involves $\|y'+ts\|^2$. Lean's `condFailure` is accordingly a function of $s$. *Correction:* write $P_k=E_s[p(s)^k]$. The sandwich $E_s[g^k]\le P_k\le B_k$ is unaffected, because $g$ and $f$ depend only on $\|s\|^2$; note that $\delta$ does too, since $j=0$.
4. **Theorem 7, converse.** "If no block lists the plant, the true secret is never produced" needs the radius condition $\varrho_i\sqrt{1+B^2}<q$ for every block. Otherwise a point $z\neq\pm v$ congruent to $v$ could yield $s$. This condition should be added as a hypothesis. It holds at the radii in play.
5. **§4.4 lower bounds.** These use the weaker linear form $1-(c+2\delta)/\mu^<$. The Paley–Zygmund form of Theorem 9 gives the stronger valid values $1.192\cdot10^{-3}$, $3.066\cdot10^{-4}$, $1.568\cdot10^{-4}$ and $3.059\cdot10^{-8}$ for $k=1,2,3,10^6$. The single-call interval sharpens to $[1.19\cdot10^{-3},\,0.0149]$. The stated values are valid, but they are not what the displayed PZ inequality gives.
6. **"Within 15%" for Conjecture B (summary and §5).** This is slightly false. A scan of every $k\le5000$ and 3000 log-spaced $k\le10^6$ gives a worst ratio of $0.829$, at $k=21$; already at $k=8$ the ratio is $0.848$. *Correction:* "within 18%". The conjecture's evidence is otherwise unchanged.
7. **Unlabelled heuristics.**
   - The shared-row floor asymptotics: "$O(\sqrt{j\log k})$" and "does not tend to 0 with k". Disjoint deletions force $k\le n/j$ in any case, so $k\to\infty$ is not available.
   - The rate "$\log L\approx(D/2\rho)\Delta\rho$".
   - The word "comparable" in the Unified statement.

   These are heuristics, not theorems, and should be marked as such. The exact parts are rigorous: the min-norm identity and $B^{\rm sh}_k\ge\Pr_u(\min\mu_i\ge1)$.
8. **Large k is hypothetical.** "Above $2^{-64}$ for every $k\le10^6$" and $B_{10^6}$ refer to hypothetical designs with $kr$ fresh rows. Within $m=511$ only $k\le3$ is realizable, as the note itself says. The sentence should say this explicitly.
9. **Wording.** "The first rigorous lower bound on the true failure" should be softened. Part 134's Theorem 2 already lower-bounds failure, though for plant-blind reducers, which is a different object. The claim is accurate only for exact-SVP coordinate blocks.

None of the issues affects the main conclusions:
- the exact covariance identity and the k-block circuit bound;
- the failure of conditional negative dependence;
- the sufficiency of first moments for list decoding, with an exact formula for coordinate planes;
- the floor $3.43\cdot10^{-11}$ of the disjoint-row bound at 646;
- the rigorous lower bound on the true failure of exact-SVP blocks.
