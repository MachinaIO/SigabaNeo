# A positive-rank filtered first moment for the punctured embedding

At **dimension 699 and width 698** the expected number of bad admissible primitive lines is at most
$2^{-301}+2^{-7}+2^{-1774}<0.007813$. This includes fractional multiples and ties, for independent uniform plain designs and independent CBD(3) planting. At **dimension 647 and width 646**, the same first moment **exceeds $2^{163}$**. The latter obstruction already occurs for consistent, full-modular-rank off-line witnesses. A small failure probability for the empty prefix at dimension 647 does not control this moment.

Scanning every rank-one shape from $D=647$ through 800, the rounded certificate passes at precisely $D=699,\ldots,800$. Width 698 is the smallest positive-prefix width certified here. Global minimality is open. In particular these results do not lower Part 39's width 647. At higher prefix rank the bounds below are finite but much too large, including at both requested full shapes.

## Model and width certificate

Use $D=r+513$, $q=3329$, $u=(e,s,1)$, $R=\|u\|$, and $L=\{(x,y,t):x+Ay=t(e+As)\pmod q\}$. Puncturing deletes fixed sample coordinates. Counts are of subgroups primitive in $L$. At rank one the first Part 6 cumulative ceiling bounds the generator length; the argument also covers requiring a completion satisfying all block inequalities. At higher rank the numerical upper bounds use the latter, existential filter (also valid for a specified passing ordering). Logarithms in proofs are natural.

Write $c_h$ for Part 6's constants. Put $P_0=0$ and, for $j>0$, $h=\min(j+1,\beta)$,
$$
 P_j=(hc_h+\sum_{i=j-h+1}^{j-1}P_i)/(h-1).
$$
Then the log ratio to a spacing $j$ positions later is at most $P_j$, by induction with that block. At $\beta=D-1$ the first block and the ratio to the last spacing give $G^D=q^r\exp(\beta c_\beta+P_{D-1})$ as an upper bound on the $D$th power of the first spacing. This bounds even the envelope optimum because it uses only its defining inequalities.

The following entries are upper endpoints for lengths and for base-two logarithms of the three contributions. Each moment belongs to the interval from zero to two raised to the tabulated exponent. Full-rank bounds average over the plant. The divisible and deficient bounds hold for each plant separately.

| $D$ | $G$ upper | divisible | off-line rank 2 | off-line rank 1 |
|---:|---:|---:|---:|---:|
|647|48|−277|440|−1355|
|670|61|−288|241|−1557|
|698|80|−300|1|−1767|
|699|81|−301|−7|−1774|
|700|81|−301|−16|−1781|
|750|125|−325|−447|−2043|
|800|182|−348|−878|−2161|

For any fully BKZ-reduced basis in the width-698 experiment, containment in the first line gives the plant as its primitive generator (Part 30). Otherwise, outside the union of bad lines, terminal exact SVP returns the projected plant up to sign. To recover the ambient plant, minimize length over its lifts by nearest-integer rounding along the first basis row, then orient to positive height. Ambient uniqueness fails with probability below $2^{-383}$ by the separate single-vector bound below. Thus these operations recover the plant simultaneously for every such output with probability greater than 0.99218. This statement permits terminal SVP and lift processing. It does not assert that the reducer emits the ambient plant verbatim.

## Counting lines

Generate a line by $w$ with $\|w\|\le G$. For an off-line competitor choose its lift $z$ reduced along $w$ to parallel length at most $G/2$. The three integral vectors $u,w,z$ are rationally independent. For each tuple shear away height by subtracting $tu$. Its membership weight conditional on the plant is exactly $q^{-ra}$ if the secret-coordinate rank $a$ equals the joint horizontal rank modulo $q$, zero otherwise. This follows by solving independent linear systems in the rows of $A$. In the displayed rank-one experiments $G\sqrt{10}<q$. Rank zero for an admitted $w$ would force every integral discrepancy $w_i-w_Du_i$ to vanish, since its magnitude is at most $G\sqrt{10}$. This contradicts noncontainment.

*Divisibility.* If a prime $p$ divides the quotient class, then $u=pv+cw$ for $v\in L$ and $c\not\equiv0\pmod p$ by height one. Some nonzero minor of $(u,w)$ is divisible by $p$, so $p\le GR$. Thus $w$ is in one of fewer than $(GR+2)^2$ translated grids of spacing at least two, counting over all primes and residues. Charge each candidate at most $q^{-r}$. This covers all divisible lines without estimating the number of Part 41 pencils.

For any translated integer grid the number in a ball of squared radius $J$ is at most $B_D(J;t)=e^{tJ}\theta(t)^D$, $\theta(t)=\sum_{j\in\mathbb Z}e^{-tj^2}$. Indeed the Fourier coefficients of the periodized one-dimensional Gaussian are positive by the Gaussian Fourier transform, so translation can only reduce its maximum at zero. Scale the radius by $1/p$ for the grids above.

*Full modular rank.* Cover the possible lifts by at most $\lceil G\rceil+3$ balls centered a unit apart along the line, of squared radius $R^2+1$. Round the parallel coordinate and use orthogonality for the radius. Multiply the ball count for $w$ by this covering count and $q^{-2r}/4$. The four sign choices are distinct; if reduction gives a boundary tie both closed endpoints are allowed. The first ball uses fixed $G$. In the second, average $e^{t(R^2+1)}$ exactly as $e^{2t}(\mathbb E e^{t s_1^2})^{D-1}$. For ambient failure one ball about zero and one factor $q^{-r}$ suffice, omitting plant multiples, since $R\sqrt{10}<q$. The script conservatively retains the extra unit of squared radius there.

*Modular rank loss.* Put $S=\operatorname{span}_{\mathbb R}(u,w,z)\cap\mathbb Z^D$. A consistent rank-one sheared pair means the unsheared triple has rank two modulo $q$ (height of $u$ is one). Every order-three minor is divisible by $q$. Equivalently by Smith form the triple has index at least $q$ in $S$. This is the small-minor exclusion underlying Q2, used here also when nonzero multiples of $q$ are possible. By projecting $z$ off $w$, the volume of the triple is at most $R G R$. Project $S$ off its primitive vector $u$ to get a planar lattice of area at most $GR/q$. A Gauss-reduced planar basis has lengths $l_1\le l_2$ with $l_1l_2\le A_0=2GR/(q\sqrt3)$. Every nonzero projected integer vector has length at least $1/\sqrt{10}$, by applying an integral discrepancy $x_i-u_ix_D$ which does not vanish. Hence $l_1^2\le A_0$, $l_2^2\le10 A_0^2$.

Count the two integral lifts by the same tube covering, now along a segment of length $R$ on the plant line, adding one to each squared radius. They determine $S$ together with $u$. In each resulting three-space the integer points are unit-separated. Disjoint half-unit balls bound the possible ordered choices of $w,z$ by $(1+2G)^3(1+2(R+G/2))^3$. Multiply by the exact consistent rank-one weight $q^{-r}$. This pays the modular deficit while bounding its population separately. Treating all pairs as independent checks would miss this entire term.

## Lower bound at the one-step puncture

At $D=647$ a first spacing of 46 passes even the full inequality-completion test. Take the logs in arithmetic progression starting at $\log46$ with the mean fixed by $q^{134}$. The script checks every block length. Smaller first spacings down to the geometric mean follow by interpolation, and below the mean an increasing progression works.

Choose horizontal $w$ with first two secret coordinates $(1,0)$ and norm at most 46, and horizontal $z$ with pivots $(0,1)$ and norm at most 29. Each $w$ is primitive and positively oriented, and these choices specify distinct lines. For fixed $w$ the plant has $\|\pi_wu\|\ge29$ with probability at least $1/2$. Indeed $R^2$ has mean 970 and variance at most $5\cdot646$ (CBD(3) has fourth moment 6). Chebyshev at 880 and Markov for the squared component along the horizontal unit direction, of mean $1.5$, give an exceptional probability at most $3230/90^2+1.5/39<1/2$.

Conditional on membership of $w$, let $Z$ be the number of eligible $z$ in $L$. Its mean $v$ is the number of candidates divided by $q^{134}$. Two different secret rows for $z$ give three independent constraints together with $w$ by the pivot pattern and the coordinate bounds. Equal secret rows with different sample coordinates are incompatible. Thus $\Pr(Z>0\mid w\in L)\ge v-v^2/2$. This event uses only the horizontal design. Each such $z$ is off-line by the pivots and the plant height. The exact integer-ball counts in the script give $v<1$ and a lower bound of $2^{163}$ after paying both the plant event and the Bonferroni factor. The divisible and deficient strata have negligible upper bounds at this shape. The mean counts distinct lines even on the same failed input; it need not be a lower bound for the reducer's failure probability.

## Higher-rank bounds and the remaining counting problem

For remaining suffix length $n$, a valid individual ceiling is
$$
 g_i\le G_i=\exp\{(r\log q-\sum_{j=0}^{n-1}P_j)/n+P_{n-1}\}.
$$
Indeed use only the maximal available block at each index in the suffix. The log spacings $P_{n-1},\ldots,P_0$ attain equality at each such block. Subtract their mean and add the suffix log determinant per dimension. Part 6's leftmost-maximum argument for partial sums bounds the first spacing of every feasible suffix by this comparison profile's first spacing. The preceding integral covolume is at least one. More sharply, divide $G_i$ by the preceding covolume to the power $1/n$.

For the displayed HKZ pencil put $h=\|P_V b_k\|$ as in Part 42. Its admissible multiplicity is bounded above by $1+2G_k/h$ (one-based index), with $h\ge e^{-P_{k-1}}$ since the first horizontal HKZ vector has length at least one. For an existential ordering replace $G_k$ by $\max_iG_i$ by the first-exit argument. Keeping the actual $H=\det V$ improves the displayed bound by replacing $G_k$ with $G_k/H^{1/(\beta+1)}$. The audit's scale at width 406 cannot be transported unchanged across widths, preceding covolumes or orderings. A pencil count alone also omits other divisible subgroups.

The table gives upper endpoints. The deficient column bounds **each** deficient modular rank's expected off-line tuple count by two to the indicated power. The full-rank column does the same for rank $k+1$. The final column bounds the entire bad-prefix mean by dropping the competitor and summing over prefix ranks. These large upper bounds establish finiteness, not divergence or lower bounds.

| $D,\beta$ | max spacing | last spacing | displayed pencil count | deficient exponent | full-rank exponent | total exponent |
|---|---:|---:|---:|---:|---:|---:|
|647,512|92|67|9758|764413|768465|762825|
|700,646|110|93|2937|290614|295336|289976|
|800,646|350|326|61744|1101567|1105611|1098488|
|1024,512|25689|25689|73350957|7518012|impossible|7503357|
|1024,647|5341|5341|7146284|4576090|4577648|4565548|

For the uniform formula at any of the requested shapes, size-reduce the passing prefix basis (GS lengths unchanged) and reduce the competitor along it by nearest-plane rounding. All coordinates have magnitude at most $B=\lceil\sqrt{k+1}\max G_i+\sqrt{9D-8}\rceil$. Write $M=2B+1$, $f=\lceil M/q\rceil$. For $l=k$ or $k+1$ rows the consistent modular rank-$a$ contribution is bounded by
$$
 {l\choose a} M^{Da}\left(q^a M f^{D-1}\right)^{l-a} q^{-ra},\qquad 0\le a\le\min(l,512).
$$
Choose spanning rows, then their coordinates. Each remaining sheared residue is in their span. Choose the height and at most $f$ lifts per horizontal coordinate. Each admissible subgroup has a representative; counting all tuples overcounts. Rational joint rank for an off-line tuple is $l$, because shearing has kernel the plant line. Moreover every order-$l$ joint minor is divisible by $q^{l-a}$ by Smith form. If the product of the sheared row norms is smaller, that rank stratum is empty by Hadamard. The table does not assume this favorable test everywhere. At $D=1024$, width 512, every off-line tuple loses rank; at 647 the full-rank contribution is allowed. Sharper counts must retain the real GS geometry and the index of the saturation simultaneously. The box count gives no decision about which stratum dominates the true high-rank mean.

Sources: [Part 6](wall1_prefix.md), [Part 30](wall1_contained.md), [Part 39](wall1_projected_reference.md), [Part 41](wall1_sublattice_union.md), [Part 42 and audit](wall1_profile_union.md), [modular minor bounds](qary.md).

## Executable certificate

Python 3 with mpmath interval arithmetic. The Gaussian series tail uses a geometric upper bound from its first omitted term. All selections of Gaussian parameters give upper bounds individually. Integer endpoints deliberately round loosely.

```python
from mpmath import iv as I
from math import isqrt
I.dps=40
q=3329
log=I.ln
def hi(x): return int(I.mpf(x).b)+1
def lg(x): return log(x)/log(2)
def c(h):
 a=[0,0,I.mpf(4)/3,2,4,8,I.mpf(64)/3,64,256]
 return log(a[h])/(2*h) if h<9 else log(2/I.pi)/2+log(I.gamma(2+I.mpf(h)/2))/h
def theta(t):
 t=I.mpf(t)
 return 1+2*(sum(I.exp(-t*j*j) for j in range(1,101))+I.exp(-10201*t)/(1-I.exp(-203*t)))
def ball(D,r2):
 return min([t*r2+D*log(theta(t)) for t in map(I.mpf,['.01','.02','.04','.08','.15','.25','.4','.7','1','2','3','4','5','6','8'])],key=lambda x:x.b)
def one(D):
 r=D-513;b=D-1
 S=0
 for h in range(2,D):
  P=(h*c(h)+S)/(h-1); S+=P
 P=(b*c(b)+S)/(b-1)
 G=I.exp((r*log(q)+b*c(b)+P)/D)
 R=I.sqrt(9*D-8)
 A=2*G*R/(q*I.sqrt(3))
 assert (G*I.sqrt(10)).b<q and ((R+G/2)*I.sqrt(10)).b<q
 # grid centers at integers along the line segment, endpoints covered by rounding
 net=lambda l: hi(l)+3
 deficit=(2*log(net(R))+ball(D,A+1)+ball(D,10*A*A+1)
          +3*log(1+2*G)+3*log(1+2*(R+G/2))-r*log(q))
 F=log(net(G))-log(4)-2*r*log(q)
 from math import comb
 F+=min([t*2+(D-1)*log(sum(comb(6,3+j)*I.exp(t*j*j)/64 for j in range(-3,4)))+D*log(theta(t)) for t in map(I.mpf,['.12','.15','.18','.20','.22','.24','.26','.28','.30'])],key=lambda x:x.b)
 # tighter first-ball theta, tight continuous-scale choice
 t=D/(2*G*G)
 ambient=F-log(net(G))+log(4)+r*log(q)
 F+=t*G*G+D*log(theta(t))
 t=2*D/(G*G)
 div=2*log(G*R+2)+t*G*G/4+D*log(theta(t))-r*log(q)
 return hi(G),*[hi(lg(I.exp(i))) for i in (div,F,deficit,ambient)]
if __name__=='__main__':
 for D in [647,670,698,699,700,750,800]:print(D,one(D),flush=True)
def many(D,b):
 from math import comb
 k=D-b;r=D-513
 P=[I.mpf(0)]; S=[I.mpf(0)]
 for j in range(1,D):
  h=min(j+1,b)
  P.append((h*c(h)+sum(P[-(h-1):]))/(h-1))
  S.append(S[-1]+P[-1])
 gs=[I.exp((r*log(q)-S[n-1])/n+P[n-1]) for n in range(D,D-k,-1)]
 G=max(gs,key=lambda x:x.b)
 B=hi(I.sqrt(k+1)*G+I.sqrt(9*D-8))
 M=2*B+1;f=(M+q-1)//q
 def bound(l,a):
  return (log(comb(l,a))+a*D*log(M)+(l-a)*(a*log(q)+log(M)+(D-1)*log(f))-r*a*log(q))/log(2)
 vals=[hi(bound(k+1,a)) for a in range(min(k+1,512)+1)]
 return hi(G),hi(gs[-1]),hi(1+2*gs[-1]*I.exp(P[k-1])),max(vals[:k+1]),(vals[-1] if k+1<=512 else None),max(hi(bound(k,a)) for a in range(min(k,512)+1))+10
if __name__=='__main__':
 for D,b in [(647,512),(700,646),(800,646),(1024,512),(1024,647)]:print(D,b,many(D,b))
def lower():
 D=647;r=134
 a=(log(46)-r*log(q)/D)/(D-1)
 assert all((a*(h-1)).b<c(h).a for h in range(2,D))
 def N(j):
  v=[1]*(j+1)
  for _ in range(644):
   w=v.copy()
   for i in range(1,isqrt(j)+1):
    t=i*i
    for l in range(t,j+1): w[l]+=2*v[l-t]
   v=w
  return v[-1]
 w,z=[I.mpf(N(j))/q**r for j in [46**2-1,29**2-1]]
 assert z.b<1 and (w*z/4).a>2**163
if __name__=='__main__':
 from fractions import Fraction
 lower()
 passed=[]
 for D in range(647,801):
  _, div, full, deficient, _ = one(D)
  if sum(Fraction(2)**v for v in (div,full,deficient)) < Fraction(1,100):
   passed.append(D)
 assert passed==list(range(699,801))
```
