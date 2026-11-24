# Auxiliary frequency basis packing by deficient flats

This lemma concerns independent auxiliary Gaussian frequency columns, not
selected BKZ vectors. Let B have n independent columns in Fq^k, whose
coordinates are independent with maximum atom at most M<1. A codimension-c
subspace has column probability at most M^c by pivot-coordinate conditioning.
Assume n>=Lk.

Edmonds' base-packing criterion implies that L disjoint size-k column bases
fail to exist precisely when some proper subspace W has fewer than
L codim(W) columns outside it. For a full-rank matrix this is the vector
matroid base-packing theorem. If rank(B)<k, W=span(B) supplies the witness
with zero outside columns. Columns are indexed: repeated or zero columns
cause no exception. See Theorem10 in de Vos and Grilnberger,
[Dynamic Matroids: Base Packing and Covering](https://drops.dagstuhl.de/storage/00lipics/lipics-vol388-esa2026/html/LIPIcs.ESA.2026.57/LIPIcs.ESA.2026.57.html#Thmtheorem10).
This uses an established combinatorial theorem; it is not a new Lean proof.

Shrink W to the span of its inside columns. The inside index set is unchanged,
and codimension can only increase, preserving the strict deficit. For dimension
t=k−c, choose t actual independent generating columns. Union over their index
sets, and condition only on these columns' values. Remaining columns are still
independent. Their outside probability is at least1−M^c. Thus

    p_bad <= Σ_(c=1)^k binom(n,k−c)
                     Pr[Bin(n−k+c,1−M^c)<=Lc−1].

There is no conditioning on the remaining columns belonging to the selected
flat. That restriction is dropped before applying the union bound. The CDF
is monotone in its outside probability; its individual summands need not be.
Alternatively union over all codimension-c subspaces, obtaining

    p_bad <= Σ_(c=1)^k [k choose c]_q
                     Pr[Bin(n,1−M^c)<=Lc−1].

Each c contribution bounds its same witness event, so their per-c minimum
may be summed. Finally minimize with1 and all previous packing bounds.

## Efficient interval CDF upper bound

For p=M^c and b=Lc−1<N, write T_j=binom(N,j)(1−p)^j p^(N−j).
For 1<=j<=b, T_(j−1)/T_j=jp/((N−j+1)(1−p))<=r_b.
If r_b<1, Σ_(j=0)^b T_j<=T_b/(1−r_b); otherwise use1.
The implementation verifies the interval upper endpoint of r_b is below1
before division. This bounds the complete CDF, including b=0.

## Connection to Holder moments

For each fixed B, choose L disjoint bases if they exist. They may depend on B,
but not on the independent uniform coefficient matrix V. The existing Holder
lemma therefore applies unchanged. Full-rank packing failure and deficient-rank
contributions remain in the completion upper bound; none is discarded.

The finite search also adds order13 to the full-coordinate grid. For the
Part441 leader, this reproduces the tested dense order/gamma search minimum;
no claim of global optimality is made. Fine-grid and Chernoff-only diagnostics
showed only modest local gains, motivating this combinatorial refinement.

## Validation and Part 442 full run

Independent mathematical audits approve the fixed-generator conditioning and
basis choice depending only on B. Exact checks cover2246 small-field multisets,
nonuniform product distributions, and308 CDF/geometric cases. Both full
production runs exit0 with2106 exact cumulant checks and18 frontier interval
reconstructions. The through24 transfer envelope is
1.0573537484468597210660298258456e-12, below the3.01e-12 local target.
The size24 leader is now rank7/girth4. Through17 remains below3.219e-17.
Logs: `/tmp/wall1_matroid_cumulants.log`, `/tmp/wall1_matroid_frontier.log`.

This numerical target concerns the complete fixed-reference incidence transfer.
It does not prove an actual selected-history law. The latter requires the
separate conditional winner-coupled moment and an initial selected-state
moment described in `wall1_winner_coupled_replicas.md`.

The certificate rerun `/tmp/wall1_matroid_certificate.log` also exits0.
It asserts the transfer target before using its temporary-cap implication,
then verifies baseline+transfer+error<1.971e-12. The computed total upper
endpoint is1.970450899541598349754851061493e-12. Existing pointwise projection
domination transfers this raw certificate to the actual draw14 projection
under the original uniform matrix law, without conditioning on that projection.
No later selected-history estimate follows from this unconditional bound.
