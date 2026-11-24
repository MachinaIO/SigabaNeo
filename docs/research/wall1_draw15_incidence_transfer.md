# Draw15 full-incidence transfer for the fixed raw candidate family

This calculation concerns the fixed raw candidate ball, with dimension519,
400 output coordinates,119 input coordinates and q=3329. Let A be the
uniform raw matrix and v an independent uniform raw coset. Write Z(A,v)
for the number of input fibers hitting this coset inside the centered raw
ball of squared radius

    R^2=1.21*(q^385/V_506)^(2/506)-2.

The probability studied here is Pr_(A,v)(Z(A,v)=0), equivalently the mean
raw-coset void fraction over A. It is not the probability over A that this
fraction exceeds.280, and it is not the void of the selected projected lattice.

## Geometry-specific incidence cover

The new entry point `wall1_draw15_incidence_transfer.py` constructs this
geometry explicitly. Its candidate mean upper bound is

    M=2*V_519*(R^2+519/4)^(519/2)/q^400 <9.287185,

and its maximum fiber density is less than1.192e-300. The compatible
circuit counts are recomputed at dimension519; no draw14 numerical count
or polynomial normalization is substituted.

The two-relation cover in `wall1_general_two_relations.py` now accepts this
explicit state. All exclusion flags remain false. Its one- and two-relation
anchor alternatives cover every connected input-matroid rank/girth stratum
through size24. The free-point factors use the upper mean M, not a lower
normalization parameter. The three direct integer counts use the proved
[odd-dimension extension](wall1_odd_relation_counts.md), and modular aliases
remain included. The dual completion uses119 input coordinates or519 full
coordinates, with the full-coordinate branch retaining the119 fallback.

This is the complete two-relation cover, not all subsequent refinements
used to sharpen draw14. Those refinements are unnecessary if this cover's
signed transfer error is already small enough. The original draw14 entry
point and its numerical assertions remain available unchanged by default.

## Signed cumulant transfer

Let F_j be the actual ordered connected full-incidence sum and let
Fbar_j be the new cover. The existing repeated-input cumulant estimate
supplies errors e_j with |kappa_j-F_j|<=e_j, hence

    |kappa_j|<=C_j=Fbar_j+e_j,  2<=j<=21,

where Fbar_2=0. All arguments in the error majorant are nonnegative;
substituting M and the complete Fbar_j therefore gives a valid upper bound.
Let

    b_k=[t^k] exp(sum_(j=2)^21 C_j*t^j/j!).

The coefficients b_k bound the absolute correction coefficients of the
factorial-cumulant expansion, without assuming any sign for kappa_j.
For the[degree21 lower witness](wall1_draw15_lower_witness.md), its fixed-mean
Poisson-padding error is bounded by sum_(k=2)^21 |w_k(10)| b_k.
Without padding, use

    W_k=sum_(j=k)^21 |a_j|*j!/(j-k)!*M^(j-k).

These bound |w_k(mu)| simultaneously for every0<=mu<=M. Thus

    Pr_(A,v)(Z=0) >0.0000647-sum_(k=2)^21 W_k b_k.

The source computes both errors with outward interval arithmetic and
asserts its numerical targets. The full actual-law lower bound depends on
the complete incidence cover, not on a truncation of its rank strata.

## Interpretation

A positive lower bound for this averaged raw void rules out obtaining a
smaller upper bound for this same observable, even with signed reference
corrections. It does not rule out a better projected-candidate proof:
projection can produce hits from long raw lifts. In particular the
pointwise domination of projected void by raw void does not transfer a
raw lower bound to the projected observable. No BKZ failure lower bound,
security-cost conclusion or completed BKZ proof follows.

This is a paper-and-interval calculation; no new Lean theorem is asserted.

## Verified result

The complete run and independent rerun pass. The fixed-mean error is below
8.744e-30, and the uniform-mean error is8.74353098619...e-30, hence below1e-25.
The latter also bounds the factorial discrepancy Delta of the lower-witness
note: expand each factorial-moment difference through the correction series
and interchange the finite sums after taking absolute values. Consequently

    Pr_(A,v)(Z(A,v)=0)>0.00006469.

The independent run is recorded at /tmp/wall1_draw15_independent_audit.log.
The file `wall1_draw15_incidence_transfer_checks.json`
preserves that output and hashes of the local Python sources and log.
The review also reran240 exact cumulant-transfer and1,866 connected-support
and error checks. Separate regressions verified that the default518 input/full
completion results agree with their preceding implementation, that519 uses119
for its fallback, and that passing118 at519 is rejected.
