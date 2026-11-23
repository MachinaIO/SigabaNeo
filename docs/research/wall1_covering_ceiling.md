# Finite-subgroup covering at the long-winner radius

Neither the 0.1795 ceiling on draws 11–405 nor the 0.126 ceiling on draws 11–380 follows from the covering estimates below. The obstruction to the usual Gaussian proof is quantitative. On **every unresolved entry**, at **every Gaussian width**, dividing the Gaussian mass inside the height-one ball by the maximum mass per mark certifies a covered fraction smaller than **\(4.18\cdot10^{-28}\)**. On each of the 395 draws in the residual determinant corridor, an integer-vector count using only the dual floor and the ambient integer grid already admits a shell with normalized squared ball coefficients summing to more than \(10^{109}\). This second figure measures the loss in a relaxation. The actual finite-group variance still requires the marked dual spectrum.

## The cosets at one entry

Condition on the revealed prefix. Put \(n=506,\ d=505,\ q=3329,\ c=1.10,\ D=\det M=V_n g^n,\ r=cg\), with \(V_n\) the unit-ball volume. In the retained space \(E=F^\perp\) of the used coordinates, \(K=P_E\mathbb Z^N\), \(M=P_E L\), and \(qK\subseteq M\subseteq K\). The independent fresh column supplies one uniform \(U\in H=K/M\), with \(h=|H|=D/\det K\). In the appended space the points at signed height \(k\) have horizontal parts \(k\tilde U+M\), for any lift of \(U\). Every draw in question has the same retained and appended dimensions. The increasing dimension \(N=505+i-1\) at incoming draw \(i\) belongs to the raw prefix. [First-tour law](wall1_first_tour.md) · [Integral projection](wall1_integrality_bound.md) · [R88](wall1_long_winner_ceiling.md)

If \(r\ge q\) or \(\lambda_1(M)\le r\), the long-winner probability is zero. This covers all histories on draws 1–7. Otherwise put \(\rho_k=\sqrt{r^2-k^2}\). The exact event is
\[
 \bigcap_{1\le k\le\lfloor r\rfloor}
 \{\operatorname{dist}(k\tilde U,M)>\rho_k\}.
\]
The height-one void at \(\rho=\rho_1\) gives an upper bound. Distinct heights can cover the same mark. All conditioning here is before the append, including any gate decided by the prefix. The dual exit in Part 172 is a separate joint-event estimate. Parts 213–214 concern an additional randomized transition. Its endpoint law does not describe this draw. [Part 172](wall1_transference.md) · [Part 213](wall1_hecke_randomization.md) · [Part 214](wall1_hecke_gated_mixing.md) · [Parts 215](wall1_fresh_mark_extension.md) [and 216](wall1_small_g_frequency.md)

## Parseval on the marked subgroup

For a real test function \(f\) let \(G_f(u)=\sum_{m\in M} f(\tilde u+m)\). Use the Fourier convention \(e^{-2\pi i\langle w,x\rangle}\). Restriction of torus characters to \(H\) has kernel \(K^*\subseteq M^*\), and \(\widehat H=M^*/K^*\). For \(a\) in this quotient define
\[
 C_a(f)=\frac1h\sum_{y\in K} f(y)e^{-2\pi i\langle a,y\rangle}
       =\frac1D\sum_{w\in a+K^*}\widehat f(w).
\]
The first expression follows by partitioning \(K\) by marks. The second follows by Poisson summation on \(K\) for Schwartz functions. Orthogonality on the finite group gives
\[
 \mathbb E_H G_f=C_0(f),\qquad
 \mathbb E_H |G_f|^2=\sum_a |C_a(f)|^2,\qquad
 \operatorname{Var}_H G_f=\sum_{a\ne0}|C_a(f)|^2.
\]
For the ball, use the first expression directly. Equivalently multiply the terms of the dual sum by \(e^{-\pi t\|w\|^2}\) and take \(t\downarrow0\) **before squaring each class sum**. Gaussian convolution tends to the indicator at every sampled grid point and its tails permit summation on \(K\). No grid point lies on these ball boundaries since its squared norm is rational whereas \(r^2=c^2(253!D)^{1/253}/\pi\) is transcendental. Here \(D>0\) is algebraic. The unregularized ball transform need not be absolutely summable. At height one the exact mean is \(\#(K\cap B_\rho)/h\). R88 bounds it below by \(1.85\cdot10^{16}\).

For example, take \(M=\mathbb Z, K=\tfrac12\mathbb Z, \rho=1/5\). The two mark counts are 1 and 0, giving finite mean \(1/2\) and variance \(1/4\). Haar sampling of the full circle gives mean \(2/5\) and variance \(6/25\). Diagonalizing the ball transform frequency by frequency computes the latter experiment.

The normalized individual ball transform is
\[
 F_d(t)=\Gamma(1+d/2)(2/t)^{d/2}J_{d/2}(t),\qquad t=2\pi\rho\|w\|,\quad F_d(0)=1 .
\]
To certify a void probability at most \(p\) by Cauchy–Schwarz, the normalized **class** energy \(\sum_{a\ne0}|C_a|^2/|C_0|^2\) must be at most \(p/(1-p)\). The two thresholds are \(359/1641\) and \(63/437\), respectively. The same test applies to the sum over all positive heights. Its coefficient at \(a\) is \(\sum_k C_{k^{-1}a}(\mathbf1_{B_{\rho_k}})\), since each allowed \(k<q\) permutes the characters. This gives a finite, prefix-specific formulation of the outstanding estimate.

## What a smoothed Gaussian can certify

Write \(G_s=G_{f_s}\) for \(f_s(y)=e^{-\pi\|y\|^2/s^2}\). Let \(L_0=D^{1/d}\), \(s_b=\rho\sqrt{2\pi/d}\), and \(z=(s_b/L_0)^2\). On the full R88 range \(32.18553<g<q/c\),
\[
 s_b>3.9475,\qquad s_b/L_0<0.67011 .
\]
Indeed the logarithmic derivative of \(s_b/L_0\) with respect to \(g\), multiplied by \(g\), is \((n-c^2g^2)/(d(c^2g^2-1))<0\).

**Smoothing scale.** If \(\sum_{0\ne w\in M^*}e^{-\pi s^2\|w\|^2}\le\epsilon<1\), Poisson summation at zero and the primal origin give \(s\ge L_0/(1+\epsilon)^{1/d}\). Even at exact smoothing the height-one radius is less than \(0.672\) times the continuous Gaussian root-mean-square radius \(s\sqrt{d/(2\pi)}\). At error \(2^{-d}\), the dual-floor choice \(s=\sqrt d/R_0(i-1)\) gives \(\rho/(s\sqrt{d/(2\pi)})<0.125\) on all residual corridors. This is an upper bound on the ratio at this *chosen* width. For comparison, the determinant obstruction holds for every smoothing width. [Micciancio and Regev, Lemma 3.2](https://cims.nyu.edu/~regev/papers/average.pdf) · [Earlier Gaussian coverage test](wall1_dual_coverage.md)

**Finite marks and all widths.** A direct Gaussian coverage argument charges the numerator below to covered marks, each carrying at most \(G_s(0)\). This maximum is exact by Poisson positivity and \(0\in H\). Its certified fraction is
\[
 A_s=\frac{\sum_{y\in K\cap B_\rho}e^{-\pi\|y\|^2/s^2}}{hG_s(0)}
 \ \le\ \frac{\sum_{y\in K\cap B_\rho}e^{-\pi\|y\|^2/s^2}}
 {h\max(1,s^d/D)}.
\]
The right side attains its maximum at \(s=L_0\). Below that width the numerator increases. Above it, each summand divided by \(s^d\) decreases since \(2\pi\|y\|^2\le d s_b^2<dL_0^2\). At \(L_0\) replace the summands inside the ball by \(e^{\pi\rho^2(1/s_b^2-1/L_0^2)}f_{s_b}(y)\) and extend the sum to \(K\). Poisson summation gives
\[
 A_s\le e^{(d/2)(1-z+\log z)}\Theta_{K^*}(s_b^2)<4.18\cdot10^{-28},
 \qquad \Theta_J(v)=\sum_{w\in J}e^{-\pi v\|w\|^2}.
\]
Here \(K^*=E\cap\mathbb Z^N\) injects into \(d\) integer coordinates without increasing norms, so \(\Theta_{K^*}(v)\le(1+2e^{-\pi v}/(1-e^{-3\pi v}))^d\). This proof takes the finite sampling law exactly and gives the favorable denominator from the maximum over the actual marks. It bounds the certificate \(A_s\) from above. The true covered fraction can be much larger.

The complementary Gaussian-tail argument also fails at every smoothing width, even using the exact minimum over the finite marks. At a void the whole Gaussian mass lies outside the ball, giving the upper estimate
\[
 T_s=\frac{\sum_{y\in K\setminus B_\rho}f_s(y)}{h\min_{u\in H}G_s(u)}.
\]
The minimum is at most the mean. Thus \(T_s\) is at least one minus the fraction of Gaussian mass on \(K\) inside the ball. For \(s\ge L_0/2^{1/d}>s_b\), Poisson positivity on \(K\) bounds this inside fraction by \((\det K)s^{-d}\sum_{K\cap B_\rho} f_s\). Each term decreases with \(s\) on this interval after normalization by \(s^d\). At the left endpoint use \(f_s\le f_{L_0}\) and \(s^{-d}=2/D\). The tilted-grid estimate just proved bounds the inside fraction by \(8.36\cdot10^{-28}\). Consequently even the exact outside-mass estimate satisfies \(T_s>1-8.36\cdot10^{-28}\) throughout the smoothing range.

**Gaussian second moment at the ball scale.** Positivity makes the cross terms inside each Gaussian class nonnegative. Including the trivial class and using Poisson on \(M^*\),
\[
 1+\frac{\operatorname{Var}_H G_s}{(\mathbb E_H G_s)^2}
 \ \ge\ \frac{\Theta_{M^*}(2s^2)}{\Theta_{K^*}(s^2)^2}
 \ \ge\ \frac{D}{(\sqrt2s)^d\Theta_{K^*}(s^2)^2}.
\]
At \(s=s_b\) this ratio exceeds \(6.11\cdot10^{11}\) on every unresolved entry. This is a lower bound for the actual Gaussian second moment. Gaussian mass is positive even in a ball void, and a second-moment argument for the ball indicator needs its own coefficients.

## Loss from the ambient integer shell count

Consider the relaxation that retains \(qw\in\mathbb Z^N\) and \(\|w\|\ge R=R_0(i-1)\) when counting potential individual nontrivial dual frequencies. It drops the orthogonal-section, lattice membership and residue-code tests. The following *single finite shell* quantifies the loss before one even deals with aliases. These trial frequencies need not coexist in a separated dual lattice.

Put \(m=\lfloor qR/\sqrt d\rfloor\) and \(k=\lceil((qR)^2-dm^2)/(2m+1)\rceil\). In the first \(d\) coordinates of \(qw\) use absolute value \(m+1\) in the first \(k\) positions and \(m\) in the rest. Set the remaining coordinates to zero. Every sign choice has length \(v=\sqrt{dm^2+k(2m+1)}/q\ge R\) after rescaling. These are nonintegral frequencies, so the integer-annihilator test alone cannot discard them. There are \(2^b\) choices with \(b=d\) if \(m>0\) and \(b=k\) otherwise.

For \(0\le t<(d+2)/2\), \(F_d(t)\ge e^{-t^2/(d+2)}\). To see this, \(F''+(d+1)F'/t+F=0\), and \(u=-F'/F=t/(d+2)+O(t^3)\) near zero. At the trial upper barrier \(2t/(d+2)\), the Riccati derivative \(1-(d+1)u/t+u^2\) is strictly below the barrier slope in the given interval. Hence \(u\) stays below the barrier up to the first zero. Integration gives the positive stated bound, excluding such a zero.

Take the incoming corridor \(g_i^*\le g<\min(q/c,e^{u_i})\) from R88. It suffices for testing histories that can still reach a residual crossing. On all draws 11–405 the script gives \(b\ge469\), \(t=2\pi\rho v<157.28\), and
\[
       2^b F_d(t)^2\ge 2^b e^{-2t^2/(d+2)}>10^{109}.
\]
For the last inequality the script uses the paired sign count and radius at each draw. The table rounds corridor and frequency bounds outward. Its last column is a lower bound on the base-ten logarithm of the relaxed shell energy in units of squared ball volume.

| Incoming draw | Lower \(g_i^*\) | Upper \(g\) | Upper \(2\pi\rho v\) | Lower log energy |
|---:|---:|---:|---:|---:|
| 11 | 2843.3383 | 3026.3637 | 136.08 | 109.46 |
| 63 | 1269.2983 | 1481.1154 | 153.45 | 111.68 |
| 100 | 749.7558 | 865.3950 | 140.80 | 118.05 |
| 200 | 216.0313 | 243.0135 | 99.45 | 135.07 |
| 300 | 77.8230 | 85.7133 | 68.56 | 143.96 |
| 380 | 39.3014 | 42.6786 | 52.20 | 147.35 |
| 405 | 32.4276 | 35.0743 | 48.25 | 148.03 |

Thus the shell relaxation and the Gaussian maximum-mass certificate yield zero additional fully certified draws in either requested range (395 and 370 draws). Entries passing the period or horizontal test already have zero long-winner probability. The figures above do not identify a reachable history violating either ceiling. The unresolved quantity is the energy of the actual nontrivial character classes or, directly, the fraction of their marks missed at every height.

## Reproduction

The interval verifier is embedded to preserve the single-file scope. Run it from the repository root.

```sh
(cd docs/research/scripts && awk '/^```python$/{p=1;next} /^```$/{p=0} p' ../wall1_covering_ceiling.md | python -B -)
```

```python
from math import floor, ceil
from mpmath import iv

iv.dps = 65
I = iv.mpf
q, n, d = 3329, 506, 505
c, a = I(11)/10, I(d)/n
vol = [I(1), I(2)]
for j in range(2, 911):
    vol.append(2*iv.pi*vol[j-2]/j)
lv, Q = iv.ln(vol[n]), iv.ln(q)
gmin = I('32.18553')
sb = iv.sqrt((c*gmin)**2-1)*iv.sqrt(2*iv.pi/d)
L = iv.exp((lv+n*iv.ln(gmin))/d)
assert (c*gmin)**2 > n and sb > I('3.9475')
ratio = sb/L
assert ratio < I('.67011')
assert ratio*I(2)**(I(1)/d) < I('.672')
z = ratio**2
v = iv.pi*sb**2
theta = (1+2*iv.exp(-v)/(1-iv.exp(-3*v)))**d
assert iv.exp(I(d)/2*(1-z+iv.ln(z)))*theta < I('4.18e-28')
assert (1/(iv.sqrt(2)*ratio))**d/theta**2 > I('6.11e11')+1

logh = iv.ln(I('56.2142'))/2+lv/n
x = (400*Q-lv)/n
upper = {406: iv.ln(I('34.807'))}
for i in range(405, 0, -1):
    period = upper[i+1]+Q/n
    hermite = (upper[i+1]+logh/n)/a
    assert period < hermite or hermite < period
    upper[i] = min(period, hermite)
table = {
    11: ('2843.3383','3026.3637','136.08','109.46'),
    63: ('1269.2983','1481.1154','153.45','111.68'),
    100: ('749.7558','865.3950','140.80','118.05'),
    200: ('216.0313','243.0135','99.45','135.07'),
    300: ('77.8230','85.7133','68.56','143.96'),
    380: ('39.3014','42.6786','52.20','147.35'),
    405: ('32.4276','35.0743','48.25','148.03'),
}
count = 0
for i in range(1, 406):
    if i >= 11:
        count += 1
        N = d+i-1
        qR = iv.exp(((N-400)*Q-iv.ln(408000*vol[N]))/N)-iv.sqrt(N)/2
        base = qR/iv.sqrt(d)
        m = floor(float(base.mid))
        assert m <= base < m+1
        fraction = (qR**2-d*m*m)/(2*m+1)
        k = ceil(float(fraction.mid))
        assert k-1 < fraction <= k and 0 <= k <= d
        freq = iv.sqrt(I(d*m*m+k*(2*m+1)))/q
        assert freq >= qR/q and m+1 < q
        b = d if m else k
        top = iv.exp(upper[i])
        assert top < q/c or top > q/c
        top = min(top,q/c)
        assert gmin < iv.exp(x) < top
        rho = iv.sqrt((c*top)**2-1)
        t = 2*iv.pi*rho*freq
        energy = (b*iv.ln(2)-2*t*t/(d+2))/iv.ln(10)
        assert b >= 469 and t < I('157.28') < I(d+2)/2
        assert energy > 109
        assert rho*(qR/q)*iv.sqrt(2*iv.pi)/d < I('.125')
        if i in table:
            low, high, arg, log_energy = map(I, table[i])
            assert low < iv.exp(x) and top < high
            assert t < arg and energy > log_energy
    period, hermite = x-Q/n, a*x-logh/n
    assert period < hermite or hermite < period
    x = max(period, hermite)
assert count == 395 and 380-11+1 == 370
print('Verified Gaussian bounds, all 395 corridor shell estimates, and all table entries.')
```

## Audit

**Confirmed.** The embedded interval verifier passed all 395 draws and every displayed table entry. The estimates leave both proposed conditional ceilings open. No correction is required.

On a fixed prefix, two frequencies restrict to the same character precisely when their difference belongs to \(K^*\). Finite-group Parseval therefore squares the sum in each class of \(M^*/K^*\). At height \(k\), the ball count is evaluated at \(kU\), so its coefficient at \(a\) is \(C_{k^{-1}a}\). After the horizontal and period exclusions, the sum of the nonnegative height counts vanishes exactly when every height misses for that one mark.

The Gaussian upper bound is uniform in both width and prefix. The width majorant peaks at \(L_0\). As \(g\) increases, \(z<1\) decreases, so \(1-z+\log z\) decreases as well, while \(s_b\) increases and the theta bound decreases. An independent calculation at the lower endpoint \(g=32.18553\) gave a majorant of approximately \(4.169541277\times10^{-28}\). At every smoothing width the inside-mass fraction is bounded by twice the endpoint majorant. Taking the minimum mark mass in the tail denominator gives \(T_s>1-8.36\times10^{-28}\).

For the relaxed shell, the Riccati derivative at \(u=2t/(d+2)\) minus the barrier slope is \(4t^2/(d+2)^2-1<0\) throughout the tested range. Thus the positive ball-transform bound applies at the upper radius of each corridor and throughout its interior. Independently evaluating the paired sign count and radius gave the smallest base-ten log bound on draw 11, approximately \(109.46265097\), with 469 nonzero coordinates. This sum uses individual squared coefficients in units of squared ball volume. A variance estimate for an actual prefix still requires membership in its dual lattice and the sums within its character classes.
