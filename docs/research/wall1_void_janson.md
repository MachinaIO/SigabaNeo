# Short-vector witnesses in a terminal index window

Fix the positive GS lengths, put $R=g_0$, and use the upper triangular convention of [Part 72](wall1_mu_moments.md). Write $C_j=(U_{ij})_{i<j}$ for the independent columns of centered unit uniforms. For $J=\{w-h,\ldots,w-1\}\cap\{1,\dots,w-1\}$, the events for the unit coefficients $e_j$, $j\in J$, are independent up-sets. They give an explicit profile-dependent void exponent. Even allowing every signed second entry of magnitude one can capture very little of the mean. At width 406 there is a geometric example with $\log E>132$ where the **exact** void exponent for these one- and two-entry witnesses in the last 342 positions is below $0.000002$.

## Independent up-sets

Order the independent scalars $1/2-|U_{ij}|$ increasingly. Then $A_{e_j}$ is increasing and depends only on $C_j$. Its probability is the following cube-section volume, with integration in Lebesgue measure:

$$
p_j=\int_{[-1/2,1/2]^j}
 {\bf1}\!\left\{\sum_{i<j} g_i^2 u_i^2<R^2-g_j^2\right\}du.
$$

Thus the Janson mean is $m=\sum_J p_j$, the ordered off-diagonal dependency sum is exactly zero, and $\Pr(N=0)\le\prod_J(1-p_j)=e^{-F_J}$, where $F_J=-\sum_J\log(1-p_j)\ge m$. This includes $F_J=\infty$ if any $p_j=1$. Disjointness here is at the level of individual entries, even though the candidates all use the top physical coordinate. Riordan–Warnke permits general up-sets in a positively associated class closed under unions and intersections. It gives $e^{-m}$ here. Its hypotheses do not cover arbitrary dependent events. [Riordan and Warnke, Theorem 1](https://arxiv.org/abs/1203.1024)

## Adding a second signed coefficient

Include $x=e_j+s e_k$, $0\le k<j\in J$, $s=\pm1$, as well as the unit vectors. The following finite convolution computes both Janson parameters for arbitrary $g$. For a list $L=(x)$ or $L=(x,y)$, set $a_i=(v_i)_{v\in L}$. Form the probability measure $H_i$ by translating the convolution of the uniform segment measures on $[-a_l/2,a_l/2]$, $l>i$, by $a_i$ (zero segments are atoms). Push it forward by $z\mapsto(g_i^2 z_v^2)_{v\in L}$ and call the result $K_i$. Define

$$
Q(L)=(K_0*\cdots*K_{w-1})([0,R^2)^{|L|}).
$$

Indeed row $i$ equals $a_i+\sum_{l>i}U_{il}a_l$, and the squared contributions add across independent rows. Write $S_x=\{l>0:x_l\ne0\}$. The mean and unordered dependency sum for the column-intersection graph are exactly

$$
m=\sum_x Q((x)),\qquad D=\sum_{\{x,y\}:S_x\cap S_y\ne\varnothing}Q((x,y)).
$$

The second sum uses distinct candidates, with ordered convention $\Delta=2D$. Edge-free groups use disjoint independent columns. Mixed signs introduce cancellation, so the folded-coordinate up-set proof no longer applies. Suen's dependency-graph bound in Janson's form gives an exponent $\min\{m^2/(8D),m/2,m/(6\delta)\}$, where $\delta=\max_x\sum_{y\sim x}Q((y))$, omitting zero denominators for positive mean. Thus even exact evaluation of the pair integrals cannot rescue a tiny restricted mean. [Janson, *New versions of Suen’s correlation inequality*](https://doi.org/10.1002/(SICI)1098-2418(199810/12)13:3/4%3C467::AID-RSA15%3E3.0.CO;2-W)

More generally some terminal column carries at least $m/|J|$ of the marginal mass, by grouping by last index. Its group is a clique, so $\delta\ge m/|J|-1$. For $m\ge2|J|$ the third Suen term is at most $|J|/3$. Below that mean its second term is below $|J|$. This ceiling applies to the displayed Suen exponent with this graph even for larger supports. It does not bound the true log suppression.

## A finite-width separation from the full mean

Take $R=1, w=406, g_i=e^{-ai}$, and $J=\{64,\ldots,405\}$. Condition on all columns except the last nonzero column $C_j$ of a candidate. The first 64 unscaled row coordinates are independently uniform on translated unit intervals since $x_j=1$. Their joint density is bounded by one. Dropping the later rows gives $p_x\le B=V_{64}e^{2016a}$, the volume of the prefix ellipsoid. There are at most $406^2$ candidates since $\sum_{j=0}^{405}(1+2j)=406^2$. Consequently the exact restricted void exponent is at most $-\log(1-406^2 B)$ whenever $406^2B<1$, by the union bound. The unit-column product and every valid inequality for this restricted void obey the same ceiling.

At $a=0.0095$ this ceiling is below $2\cdot10^{-6}$, whereas the single $(j,m)=(405,1)$ term in the [exact full mean](wall1_window_asymptotics.md) exceeds $e^{132}$. At the milder slope $0.009$ the same ceiling is below $4\cdot10^{-7}$ and the term exceeds $e^{91}$. These are comparisons of witness families on specified profiles. No packing feasibility assertion is needed for either comparison. The following interval checks use the half-integer gamma formula.

~~~python
from math import factorial
from mpmath import iv as I
I.dps = 60
j = 405
V = I.pi**202 * 4**203 * factorial(203) / factorial(406)
for slope, lower, cap in [('0.0095', 132, '0.000002'),
                          ('0.009', 91, '0.0000004')]:
    a = I.mpf(slope)
    logterm = (I.ln(V) + a*j*(j-1)/2
               + I.mpf(j)/2 * I.ln(1-I.exp(-2*a*j)))
    mass = 406**2 * I.pi**32 / factorial(32) * I.exp(2016*a)
    assert logterm > lower and -I.ln(1-mass) < I.mpf(cap)
~~~

For a geometric profile of fixed width one may parameterize the achieved $F_J$ by the full mean using the exact mean formula (strictly increasing for positive slope). The example bounds its value at two such means. For unrestricted profiles the result is a function of the individual lengths. A growing uniform $f(E)$ on the surviving domain and a joint bound for overlapping windows remain open. The missing estimate concerns avoidance by many lifts sharing terminal columns. The small restricted void exponent gives no lower bound on the full void probability.
