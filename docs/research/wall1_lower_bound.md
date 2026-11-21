# A lower bound on necessary width cannot follow from full reducedness alone

At the plain shape \((m,n,q)=(511,512,3329)\), there is a single deterministic basis selector, using only the public lattice, whose output is fully BKZ-2 reduced and succeeds with probability greater than \(1-2^{-1900}\) for **each fixed** error and secret with coordinates bounded by 3. This selector uses full-dimensional SVP. Thus the width used to certify its output and the width needed to compute it are different parameters. The result rules out a small-success theorem uniform over fully reduced output bases at this shape. It leaves the canonical slide algorithm open.

## From ambient uniqueness to a simultaneous statement about widths

Use the planted distribution and notation of [the ambient second-minimum estimate](usvp_planted.md). Put \(u=(e,s,1)\), \(r=\|u\|\), \(d=m+n+1\), and \(B=\|(e,s)\|_\infty\). For every prime \(q>r\sqrt{1+B^2}\), except on an event of probability at most
\[
 \epsilon=\frac{V_d(r+\sqrt d/2)^d}{2q^m},
\]
there exists **one basis** that succeeds and is fully BKZ-\(\beta\) reduced simultaneously for every \(2\le\beta\le d\). Here \(V_d\) is the Euclidean unit ball volume. Conditional on ambient uniqueness the existence statement is deterministic.

Indeed, for each fixed integral \(z=(x,y,t)\) in the closed radius-\(r\) ball outside \(\mathbb Zu\), membership requires \(A(y-ts)=te-x\) over the field. If the argument of \(A\) is zero, membership forces all coordinate discrepancies to be multiples of \(q\). Each has absolute value at most \(r\sqrt{1+B^2}<q\), so this is impossible. Otherwise independent uniform rows give membership probability \(q^{-m}\). Union-bound over sign *pairs*. Unit cubes centered on the candidate points fit in the radius-\(r+\sqrt d/2\) ball, giving the displayed bound. In the absence of any such pair the only nonzero points of length at most \(r\) are \(\pm u\).

Select an HKZ basis recursively, taking an exact shortest vector in the full projected quotient at each step. Such a vector is primitive there, so lifting it extends the current primitive prefix. Size-reduce each lift by previous basis vectors. Ties can be settled deterministically, for instance lexicographically among shortest projected vectors and then among minimum-norm lifts before size reduction. This rule needs no plant. Each projected block starting at that row contains the selected shortest vector and is contained in the full projected quotient. Its minimum therefore equals the selected length at every width. The first row captures on ambient uniqueness. This applies the HKZ observation of [the literature note](wall1_literature.md) to the corrected capture-or-terminal event.

For the stated shape, \(d=1024\), \(r^2\le9208<96^2\), and \(96\sqrt{10}<3329\). Integrating \(\exp(-d\|x\|^2/2)\) over the unit ball gives \(V_d\le(2\pi e/d)^{d/2}\) by comparison with the full Gaussian integral. Hence
\[
 \epsilon\le\tfrac12
 \left(112\sqrt{2\pi e/1024}\,/\,3329^{511/1024}\right)^{1024}
 <\tfrac12(0.26)^{1024}<2^{-1900}.
\]
The same probability bound holds after averaging an independent planting distribution on this support. All probabilities here are over unconditioned uniform designs for the fixed plant.

## A width-two instance where even basis selection is immaterial

Take \(m=n=1,q=31,e=s=1,A=(4)\). Then \(u=(1,1,1)\) and the lattice equation is \(x+4y-5t=0\pmod{31}\). Every fully exact BKZ-2 basis captures in its first row. To check this directly, let \(g_1,g_2,g_3\) be its Gram–Schmidt lengths. Rounding the second vector of each projected pair along the first gives \(g_i^2\le g_{i+1}^2+g_i^2/4\) by pair reducedness. The last nonzero basis coefficient of \(u\) contributes at least its corresponding \(g_j\) to the norm. Consequently \(g_1\le(4/3)\sqrt3\), and its integral squared length is at most 5. For any lattice point in this ball, \(|x+4y-5t|\le\sqrt{210}<31\), so the congruence is an equality. Now \(|x-t|\le\sqrt{10}<4\) and \(x-t=-4(y-t)\) force \(x=y=t\). Primitivity forces the first row to be \(\pm u\). This specializes [the width-two gap argument](wall1_small_exact.md) without enumerating bases or residues.

For a necessary width of a particular procedure, the unresolved quantity is the probability under its **output law** of both missing capture and failing the terminal criterion. Even a proof that the projected plant vanishes with overwhelming probability is compatible with overwhelming success in the first row. The existential HKZ construction gives no runtime or success estimate for a width-limited tour.
