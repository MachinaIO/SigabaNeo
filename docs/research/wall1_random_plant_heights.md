# Projected CBD vectors at fixed height

Condition on the design and reducer coins as in [Part 47](wall1_decoupled.md). Let \(P\) be the resulting horizontal orthogonal projector of rank \(d=\beta-1\), let \(Y\) have independent CBD(3) coordinates, and put \(v=(PY,1)\).

**Fixed-direction theorem.** For nonzero \(x\in\operatorname{im}P\) and deterministic \(a\ge0\),
\[
\Pr(\langle x,PY\rangle\le-a)
\le \inf_{s\ge0} e^{-sa}\prod_j\cosh(sx_j/2)^6
\le e^{-a^2/(3\|x\|^2)}.
\]
Indeed \(Px=x\), and a CBD(3) coordinate is distributed as half the sum of six independent uniform signs. Independence gives the product exactly before the Chernoff inequality. Using \(\log\cosh z\le z^2/2\) and choosing \(s=2a/(3\|x\|^2)\) gives the last bound.

At height one the collision event has the deterministic threshold \(a=\|x\|^2/2\), including equality. At height \(k>1\) its threshold is \((\|x\|^2+(k^2-1)\|v\|^2)/(2k)\). Substitution of the mean squared norm into the fixed-direction theorem is unjustified. A lower bound on the squared norm gives the correct inclusion on the event where that lower bound holds. An upper norm cutoff alone gives the opposite direction for this substitution.

**Norm theorem.** For \(0<t<1/3\),
\[
\Pr(\|v\|^2\ge 1+h)\le e^{-th}(1-3t)^{-d/2}.
\]
To see this, take an independent standard Gaussian \(G\) on \(\operatorname{im}P\). Conditional on \(Y\), the exponential moment of \(\sqrt{2t}\langle G,Y\rangle\) is \(\exp(t\|PY\|^2)\). Integrating first over \(Y\) instead bounds the same moment by \(\mathbb E\exp(3t\|G\|^2/2)=(1-3t)^{-d/2}\). Markov's inequality finishes the proof.

For example, at rank 100 and radius 18 the upper-tail bound is below \(5\cdot10^{-9}\). The following interval check uses \(t=1/6\) and \(h=323\).

~~~python
from mpmath import iv
iv.dps = 40
bound = iv.exp(-iv.mpf(323)/6) * 2**50
assert bound < iv.mpf(5)/10**9
~~~

**Scope.** These are conditional one-direction and norm estimates. A certificate for the shortest pair still needs a bound on the union over all competing lattice points and heights. A width certificate would also have to account for the exceptional designs in the null-minimum estimate. For instance, two successive guarantees of 0.99, the second conditional on the first, give a joint lower bound of 0.9801. Projected uniqueness and successful lifting are separate events in Part 47.
