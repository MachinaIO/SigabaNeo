# Base packing from conditional atoms, allowing correlated coordinates

The generating-column bound of wall1_matroid_packing.md does not require
independent columns if a stronger conditional atom hypothesis is available.
This extends the auxiliary counting tool to anisotropic Gaussian weights.
It does not assert a Gaussian law for actual BKZ states.

## Conditional-flat version of the bound

Let C_1,...,C_n be possibly dependent columns in F_q^k. Suppose, after
fixing every other column at any positive-probability value, every fixed
codimension-c subspace W has conditional mass at most M^c, for all1<=c<=k.
The same bound holds after any partial revelation of the other columns:
such a law is a mixture of the complete conditional laws.

For n>=Lk, the probability that these columns do not contain L disjoint
bases is at most

    min(1, sum_(c=1)^k binom(n,k-c)
        BinCDF(Lc-1; n-k+c, 1-M^c)).                    (1)

Here the CDF counts columns outside W. By the base-packing witness criterion,
failure has a deficient subspace of dimension k-c spanned by k-c actual
columns and fewer than Lc columns outside it. Fix those generator indices
first and condition on their values. If they are not independent, skip that
choice. Otherwise W is fixed. Expose the remaining columns successively.
At each step the conditional probability of falling outside W is at least
1-M^c, so sequential Bernoulli domination gives the displayed lower-tail
bound. Union over generator choices and c proves(1), including deficient
total rank. No conditioning on the remaining columns being in W is used.

The old geometric-CDF upper bound is still applicable to this binomial CDF.
Independence of partially exposed column coordinates is not asserted.

## A shift-uniform discrete-Gaussian atom bound

Let a>0 and epsilon(a)=2 exp(-pi^2/a)/(1-exp(-3pi^2/a))<1. A scalar
integer Gaussian proportional to exp(-b(z-mu)^2), with0<b<=a and any real
mu, has every residue probability modulo q bounded by

    M=min(1,(sqrt(a/pi)+1/q)/(1-epsilon(a))).             (2)

For the numerator of a residue probability, each Gaussian superlevel interval
contains at most its length/q+1 points of that residue class. Integrating
these levels bounds the numerator by1+sqrt(pi/b)/q. Poisson summation and
the absolute nonzero Fourier tail bound the denominator below by
sqrt(pi/b)*(1-epsilon(b)). Since epsilon(b)<=epsilon(a), (2) follows.
When epsilon(a)>=1, use only the trivial atom bound1.

## Joint Gaussian application and its precise scope

For an unrestricted integer random vector with density proportional to
exp(-(x-mu)^T Omega (x-mu)), Omega positive definite, fixing all but one
entry gives a shifted scalar Gaussian with parameter Omega_ii. If all
diagonal entries are at most a, (2) therefore applies uniformly to every
complete scalar conditional law. Reshape the vector into a k-by-n array.
This need not have independent rows or columns.

To bound a column's mass in W, use c pivot entries in equations for W.
Condition on the nonpivot entries and all other columns. The c pivot
residues are uniquely specified. Expose those residues one at a time;
each probability is at most M, by mixing complete scalar conditionals.
Their joint probability is at most M^c. Averaging over nonpivot entries
proves the required conditional-flat hypothesis. Mixing over integer values
also proves it when other columns are fixed only modulo q.

This includes independent anisotropic Gaussian rows and correlated Gaussian
arrays whenever their full precision diagonal has a certified bound. It
does NOT justify dropping modular support restrictions, truncation to a
cylinder, or winner/saturation conditioning. Those can change the conditional
law. A proposed Gaussian majorization must be applied to an unrestricted
auxiliary sum, with its normalization and the counting comparison proved
separately. For a parametrized constraint code, these must be the actual
unrestricted integer coordinates; a linear image needs its own modulo-q
rank and atom argument. A semidefinite projected norm alone does not define
a normalizable full Gaussian. No production radius, precision bound or history probability is
certified here.

The exact checker uses two independent parity-biased binary rows, whose
coordinate columns are dependent but whose complete scalar atom bound is
known. It counts all column multisets with their exact correlated weights
and verifies ten packing bounds, including a nontrivial bound below1.
The general proof above, independently audited, supplies the extension;
these finite laws are regression checks rather than Gaussian experiments.
