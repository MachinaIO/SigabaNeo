# Several equal pair sums: a restricted family beyond size thirteen

This paper calculation extends Part 283's direct count to k equal pair sums.
It bounds a particular family of connected 14-point configurations, not all
14-point configurations. The full BKZ proof and the draw-14 bound remain open.
The arguments below are not formalized in Lean or independently audited.

## Integer and modular counts

Let S be the integer points of the N-dimensional ball of radius R, with N even,
and r(s) the number of ordered pairs in S with sum s. For k>=2, write G_k for
sum_s r(s)^k. The shifted-ball bound obtained from half of each unit cube is
2 V_N (u+N/4)^(N/2). Applying it to the pair intersection, then using layer-cake
integration to sum over s, gives

```
G_k <= 2^(k+1+N) pi^((k+1)N/2) (kN/2)!
       / ((N/2)!^k ((k+1)N/2)!)
       * (R^2+5N/16)^((k+1)N/2).
```

For modular equality, the real kernel has squared Gram--Schmidt lengths
2 (k times) and k/2. Set K_beta=theta(2 beta)^k theta(k beta/2), where
theta(x)=sum_(z in Z) exp(-x z^2). A layer is indexed by v in Z^k/Z1 and
has squared perpendicular distance
q^2/2 * (sum v_i^2-(sum v_i)^2/k).

Fixing v_k=0 bounds the layer sum by theta(beta q^2/(2k))^(k-1).
Alternatively choose min(v)=0 and max(v)=M. There are exactly
(M+1)^k-2M^k+(M-1)^k such vectors, at most 2^(kM), and their variance is at
least M^2/2. With x=beta q^2/4 and M^2>=1+3(M-1), the layer sum is at most
1+delta, where delta=2^k exp(-x)/(1-2^k exp(-3x)), if its denominator is positive.
Consequently the additional modular count is at most

```
exp(2k beta R^2) K_beta^N
 * min(theta(beta q^2/(2k))^((k-1)N)-1, (1+delta)^N-1).
```

The second alternative is omitted when its denominator is nonpositive.
The verifier uses beta=(k+1)N/(4kR^2). No nonzero modular layers are discarded.

## Connected configurations containing an anchor

Require an anchor on 2k distinct positions whose augmented input rank is
exactly k+1 and which consists of k signed equal pair sums. The affine
row-sum condition allows 1+2^(k-1) sign types: ordinary sums, or oriented
differences modulo simultaneous reversal. The symmetric ball gives the same
count bound for each type.

Let A_k be the sum of the integer and additional modular bounds divided by
q^(m(k+1)). For connected h-point configurations of rank r containing such
an anchor, the Part 282 basis-extension count gives the upper activity

```
choose(h,2k) (2k)!/(2^k k!) * (1+2^(k-1)) * A_k
 * choose(h-2k,r-k-1) mu^(r-k-1)
 * q^((r-1)(h-r-k+1)) / (r-k),
```

summed over k+1<=r<=h-k+1. The denominator counts the at least r-k choices
of an extension basis in the contraction of a connected support. It is not
an assumed average multiplicity. Degenerate anchors of lower rank are not
covered by this formula.

Apply the existing positive factorial-cumulant transfer C to this family
activity alone. At the draw-14 parameters (q=3329, m=400, N=518), the interval
verifier obtains:

| k | h | log10 of family-only transfer upper bound |
|---|---|---|
| 4 | 14 | -41.5553546144... |
| 5 | 14 | -81.2353670050... |
| 6 | 14 | -125.8821366103... |
| 7 | 14 | -182.7477468314... |
| 12 | 24 | -237.0131547542... |

In particular the k=4, h=14 bound is below 3e-42. The k=12, h=24 bound is
below 1e-237, including aliases; its alias/main upper-bound ratio exceeds
113, so aliases cannot uniformly be called negligible.

These are restricted-family bounds. Other connected configurations and
mixed terms with them are unbounded here. The admitted full-class transfer
through size thirteen remains below 2.175e-13 (Part 283); this calculation
does not replace the remaining mixed charge M with a numerical bound.

Validation: `python3 docs/research/scripts/wall1_multiple_pair_sums.py` passes
75 finite integer/modular energy comparisons, 20 exact layer-range checks,
and interval assertions for the two displayed threshold bounds. These
regressions check calculations, not a formal proof of the general formulas.
