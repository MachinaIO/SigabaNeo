# What every coordinate block can see

Let $q=3329$. Let $G$ have as rows the input parts of the integer frozen vectors, reduced modulo $q$, and let $C=\operatorname{row}(G)\subseteq\mathbb F_q^n$ have rank $r$. Write $x$ for the input part of $w$ reduced modulo $q$. A block means **any** $k$-subset of the $n$ available input coordinates, as in Part 244. Assume $1\le k\le n$. In applying this notation to a frozen graph lattice, use generators of the integral frozen graph lifts.

## Exact local criterion

**Lemma 1.** Let $D_k$ be the span of the vectors of Hamming weight at most $k$ in $\ker G=C^\perp$. The set $U_k$ of vectors passing every block test satisfies
\[
 U_k=D_k^\perp,\qquad
 \dim(U_k/C)=n-r-\dim D_k.
\]
Thus the undetected residues form exactly $q^{n-r-\dim D_k}$ cosets of $C$, including $C$ itself.

**Proof.** On a block $J$, $x_J$ is in the row span of $G_J$ exactly when it annihilates every column relation of $G_J$. Extending those relations by zeros gives the elements of $\ker G$ supported on $J$. Every support of size at most $k$ fits in some $J$. Taking the intersection of all the annihilators and then taking dimensions gives both claims. For a prescribed family of blocks, the same proof retains only the relations supported inside a member of that family. In particular the theorem about all subsets cannot be applied unchanged to consecutive windows.

**Lemma 2.** A matrix for $D_k$ can be formed with one row for each minimally dependent column set of size at most $k$. Use the coefficients of its dependence, extended by zeros. Equivalently, a residue $x$ fails a test exactly when appending $x$ as a row increases the rank on some block of size at most $k$.

**Proof.** A minimally dependent set has a one-dimensional space of dependencies. Given any nonzero relation supported on at most $k$ positions, choose a minimally dependent subset of its support. Subtract a multiple of that subset's relation to cancel one nonzero entry. Induction on the support size gives the claimed generating set. The rank formulation follows from membership in the restricted row span. Counting the dependent blocks can overcount the dimension because their relations can be linearly dependent.

**Corollary.** Choose any column basis $B$ of size $r$. For each $j\notin B$, express column $j$ in this basis and let $t_j$ be the number of nonzero coefficients. The fundamental relation with coefficient one at $j$ has weight $1+t_j$. These $n-r$ relations form a basis of $\ker G$, since their restrictions outside $B$ are distinct coordinate units. Consequently
\[
 \dim(U_k/C)\le \#\{j\notin B:1+t_j>k\}.
\]
This gives a rank-pattern certificate for a small excess dimension even if $k\le r$. In particular $k\ge r+1$ always gives $U_k=C$. Short relations from other bases can give equality $U_k=C$ earlier than the displayed upper bound certifies.

## Sharpness, including short integer vectors

For $1\le k\le r<n\le3329$, choose $n$ distinct field elements $a_j$. Take $G_{ij}=a_j^i$ for $0\le i<r$. Every $r$ columns have nonzero Vandermonde determinant. Every $k$-block therefore has full column rank, so $U_k=\mathbb F_q^n$ and the excess dimension is the full $n-r$. Each coordinate unit lies outside $C$, since a polynomial of degree less than $r$ vanishing on $n-1\ge r$ distinct points is zero. At $k=r+1$ the excess dimension drops to zero. At the same rank the coordinate subspace spanned by the first $r$ units already has $U_1=C$. Both examples lift to integer matrices.

Even a bound on the lengths of **both** the witness and the generators allows many exceptional directions. Partition $m(k+1)$ coordinates into $m$ groups of size $k+1$. Inside each group with last index $b$, take all $k$ generators $e_i-e_b$ for $i\ne b$. Their integer lengths are $\sqrt2$. Their row span imposes exactly one zero-sum equation per group. Every nonzero dual relation is constant and nonzero on at least one whole group, so $D_k=0$ and $\dim(U_k/C)=m$. One coordinate unit per group gives $m$ independent quotient classes with integer representatives of length one. Orthogonal projection off the real frozen span gives each of those representatives length $1/\sqrt{k+1}$, since its projection equals the group indicator divided by $k+1$. At block size $k+1$ all $m$ equations become visible. This example concerns Euclidean length and congruence alone. It makes no claim about the probability of a particular frozen flag in the notes.

## Consequences for interpreting the width-506 allowances

The length cutoffs in the notes apply to projected vectors. Even a raw unit vector can be outside the global span while passing every local test, as above. The coset count in Lemma 1 counts residues, with no weighting by the law that selects a frozen flag and a short witness. In particular dividing this count by $q^{n-r}$ would calculate a probability under a uniform quotient residue hypothesis. The shortest-vector comparison supplies no such hypothesis. For two or three witnesses, failure to gain the full required rank on a block can also occur when one witness individually increases rank there. Failure of the tuple test is a larger event than all witnesses satisfying Lemma 1.

The following numbers record the budget arithmetic already available in Parts 243–244. The third column describes the room after reserving the detected charge. It gives no estimate of the actual size of the undetected class. [Generalized deletion, width-506 budgets](wall1_generalized_deletion.md) · [Proof gap, Parts 243–244](../PROOF_GAP.md)

| Quantity | Previously bounded contribution | Room for the complement |
|---|---:|---:|
| Unpaid $Z_1$ probability | $<3.93\times10^{-19}$ combined for detected triples and planes | $>4.0202996\times10^{-12}$ |
| Residual mean score | $<1.31\times10^{-8}$ for pair detection at heights 9–30 | $\ge5.1098\times10^{-7}$ |
| Extra prefix rejection probability on score-accepted designs | $<4.949\times10^{-6}$ for a detected varying-cutoff violation | $\ge0.00354128$ |

The rank criterion and length cutoffs alone give no additional numerical charge below any of these allowances. Distributions on abstract integer flags and witnesses can concentrate entirely on the short counterexample. For the selected random graph lattice, the contribution of the undetected cases remains unquantified.

## Reproducible checks

Run the embedded Python from the repository's scripts directory. This keeps the check and proof in the single requested file.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_undetected_span.md | python3 -B -)
```

```python
from decimal import Decimal as D
from itertools import combinations

q = 3329

def rank(rows):
    basis = {}
    for row in rows:
        v = [a % q for a in row]
        for j in sorted(basis):
            scale = v[j]
            v = [(a - scale*b) % q for a, b in zip(v, basis[j])]
        j = next((i for i, a in enumerate(v) if a), None)
        if j is not None:
            inv = pow(v[j], -1, q)
            basis[j] = [a*inv % q for a in v]
    return len(basis)

def passes(G, x, k):
    for J in combinations(range(len(x)), k):
        rows = [[row[j] for j in J] for row in G]
        if rank(rows) != rank(rows + [[x[j] for j in J]]):
            return False
    return True

n, r = 8, 3
G = [[pow(j, i, q) for j in range(n)] for i in range(r)]
units = [[int(i == j) for i in range(n)] for j in range(n)]
for x in units:
    assert rank(G + [x]) == r + 1
    assert passes(G, x, r) and not passes(G, x, r + 1)

k, m = 3, 2
short = [[a-b for a, b in zip(units[i], units[last])]
         for last in [3, 7] for i in range(last-k, last)]
witnesses = [units[0], units[4]]
assert rank(short + witnesses) - rank(short) == m
assert all(sum(a*a for a in row) == 2 for row in short)
for x in witnesses:
    assert passes(short, x, k) and not passes(short, x, k+1)

assert D('4.0203e-12') - D('3.93e-19') > D('4.0202996e-12')
assert D('5.2408e-7') - D('1.31e-8') == D('5.1098e-7')
assert D('.003546229') - D('4.949e-6') == D('.00354128')
print("Block tests, counterexamples and three budget differences passed.")
```
