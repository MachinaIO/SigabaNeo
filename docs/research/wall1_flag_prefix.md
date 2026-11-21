# The first-pass determinant cap in the simultaneous flag test

At full width 506 the first-pass cap is automatic, but its normalized natural logarithm is **1207.5464**. The Haar flag first moment allows **547.8033** at the proposed ratio 0.954. On the finite graph ensemble the all-prefix claim at this cap actually fails for **every** matrix: there is always an eligible prefix with physical quotient minimum below $10^{-176}$. The construction below does not assert that the forward pass selects this prefix.

## Normalization and the Haar width curve

Let $N=m+n=1023$, $(m,n,q)=(511,512,3329)$, $u=q^{m/N}$, $G_j=V_j^{-1/j}$, and normalize physical lengths by division by $u$. For the full window $b$, set $d=b-1$, $k=N-d$, and $a=d/b$. Primitive completion at each freeze makes the lifted prefix primitive in the full input basis. With physical retained determinant $D$, its physical prefix determinant is $u^N/D$. Hence its **normalized** determinant is $P=u^d/D$. A larger prefix makes the quotient determinant smaller.

Write $J_b$ for a certified upper bound on $\sqrt{\gamma_b}$. Part 114 starts at $D_0=q^d$ and gives $D_t=D_{t-1}/s_t\ge D_{t-1}^a/J_b$ on the 512 graph appends. Thus
$$
Z=d a^{512}\log q-b(1-a^{512})\log J_b,\quad
D\ge e^Z,\quad T=u^d e^{-Z},\quad H=G_d e^{Z/d}.
$$
The automatic cap is $P\le T$. Over this range $H$ is the smallest physical own GH permitted by the cap. Equality in the bound need not occur on any history. The deterministic argument uses the specified $qI$-first order, exact forward SVPs and no lookahead. [Part 108](wall1_first_tour.md) · [Part 114 and its audit](wall1_idea_drift.md)

For determinant-one Haar input apply Part 115 to this numerical cutoff. With $A_{N,k}$ its unoriented primitive-prefix constant, the expected number of bad flags is $A_{N,k}T^N c^d/(2\zeta(d))$. Setting it equal to 0.005 gives
$$
c(T)=\left(\frac{0.01\zeta(d)}{A_{N,k}}\right)^{1/d}T^{-N/d},
\qquad g(T)=uG_d T^{-1/d}c(T)=Hc(T).
$$
Outside probability 0.005 these are simultaneous ratio and physical lower bounds for passing prefixes. The probability is per predetermined width. The automatic passing property belongs to the graph reducer. On a Haar parent the assertion quantifies over eligible prefixes, with no claim that an analogous pass produces one. [Part 115 and its audit](wall1_idea_variants.md) · [Kim's flag integrals](https://arxiv.org/abs/2005.10874)

All entries below are rounded **down**. The last two columns are base-ten logarithms, so each is directly usable as an exponent for a lower bound. The curve uses the audited squared Hermite caps 45.6963 and 56.2142 at 406 and 506, and Blichfeldt elsewhere. Local jumps reflect the choice of cap.

| Full width | Horizontal rank | Physical GH floor | $\log T$ | $\log_{10}c$ | $\log_{10}g$ |
|---:|---:|---:|---:|---:|---:|
|350|349|6.9733|1266.0932|−986.4356|−985.5921|
|400|399|11.3234|1280.3353|−845.8616|−844.8076|
|406|405|12.3365|1267.8581|−816.5495|−815.4584|
|450|449|17.7184|1265.8609|−718.7548|−717.5064|
|475|474|21.8568|1249.5157|−660.4897|−659.1501|
|500|499|26.7192|1227.8410|−605.7087|−604.2819|
|506|505|28.8095|1207.5463|−580.4419|−578.9824|
|511|510|29.1071|1216.7416|−582.6868|−581.2228|

At 506, $0.954H>27.4842$ would clear 27.4537. The simultaneous Haar calculation gives about $1.04\times10^{-579}$ physical. At 406 its physical bound is about $3.48\times10^{-816}$, against 24.5807. Reducing $\log T$ by one increases $\log g$ by $(N+1)/d$. Part 115's much larger physical certificate used a much smaller cutoff and left the chance of finding a passing prefix open.

## Exact finite graph flag mean and numerical certificates

Use the sign convention $x+Ay=0\pmod q$; negating uniform $A$ preserves its law. Sum over rational flags $U\subset W$ of ranks $k,r=k+1$. Choose a saturated integer basis $(S;F)$ of $W$, and integer columns $C$ giving a saturated basis $(S;F)C$ of $U$. Let $v_W,v_U$ be their Euclidean covolumes. Sum over maps $B$ with $\ker F\subseteq\ker B$ modulo $q$. For $M=S+B$ put
$$
e=v_W q^{\operatorname{rank}_q M},\quad
p=v_U q^{\operatorname{rank}_q(MC)},\qquad P_*=u^kT.
$$
The exact expected bad-flag count is
$$
\sum_{U\subset W}\sum_B q^{-m\operatorname{rank}_q F}
\mathbf1\{p\le P_*,\ e<cG_d u^{N/d}p^{1-1/d}\}.
$$
Indeed $AF=B$ has the displayed weight. Restricting that *same* map gives both indices. The primitive intersections with the graph lattice have physical determinants $p,e$. The primitive line in the quotient has length $e/p$, and each unoriented flag is counted once. The strict test bounds both integer plane heights, so only finitely many terms contribute. This is the zero-dual-tuple specialization of Part 101 with a nested plane mark. Substituting the Haar coefficient for this arithmetic sum would change the distribution. [Part 101 and its audit](wall1_qary_rogers.md)

There is a computable **zero** of the exact sum at 506. Saturation gives the stacked basis full column rank modulo $q$, and the graph code has dimension $n$, whence $e\ge q^{r-n}=q^7$ (also $v_W\ge1$ by integer minors). The right side of the strict flag test increases in $p$. At $c_0=q^7/(P_*H)$ it equals $q^7$ at the upper endpoint. Thus every summand vanishes, certifying ratio $10^{-1412.6216}$ and physical length $10^{-1411.1621}$ even for fixed $A$. This evaluates the raw pair mean at a certified threshold. Its optimal 0.005 threshold has not been numerically enumerated.

A stronger computable 0.005 certificate uses Part 101's overlap bound on the **same extensions**. Write $F_p(l,s)$ for its determinant-root bound with failure budget $p=0.005$ (formula in the code below). Use the dual annihilator of rank $l=N-r=504$ and unit $s=q/u$. Simultaneously $e/u^r\ge F_p(l,s)^l$, so the physical floor is $g=u F_p(l,s)^l/T$ and the ratio floor is $g/H$. The latter follows directly from $e/p^{1-1/d}$ decreasing with $p$ at fixed $e$; dividing a length floor by a lower GH bound alone would be invalid. The resulting bounds are **$10^{-497.1814}$ times own GH** and **$10^{-495.7219}$ physical**. This bounds the probability of any bad extension through a common ambient statistic. It does not evaluate a positive raw flag multiplicity. Even Part 108's reducer-specific pathwise lift bound $(\sqrt3/2)^{512}$ physical is stronger.

## A bad eligible prefix on every graph

The slack at 506 is large enough to prove a converse without averaging. Work in determinant-one units. Use an auxiliary size-reduced HKZ basis $v_1,\dots,v_N$ and denote the determinant of its first $i$ vectors by $p_i$. Hermite in the projected rank $h$ gives a head at most $J_h$ times its determinant root. Dividing by the head raises the log determinant root of the remaining quotient by at least $-\log J_h/(h-1)$. Starting at determinant one and taking complements yields
$$
\log p_i\le U_i=(N-i)\sum_{h=N-i+1}^N\frac{\log J_h}{h-1}.
$$
Blichfeldt gives $U_{518}<796$ and $U_{519}<797$. Fix the first $k-1$ basis vectors and replace $v_k$ by $v_k+t v_{k+1}$ for integer $t\ge0$. This is a primitive prefix inside the same primitive rank-519 extension. Its determinant starts below $T/2$ and tends to infinity. Between consecutive values its absolute change is at most $p_{k-1}\|\pi_{k-1}v_{k+1}\|$, with $\pi_{k-1}$ projection off the fixed vectors. Every HKZ head is at most $q/u$ since the projections of the scaled $q\mathbb Z^N$ axes span the remaining space. Size reduction therefore bounds this increment by $e^{U_{k-1}}\sqrt{5/4}\,q/u<T/2$. The first crossing of $T/2$ supplies a prefix in $[T/2,T]$. The line from the fixed extension has physical length at most $2u e^{U_{519}}/T<10^{-176}$. Its quotient has own GH at least $H$.

Consequently at the requested physical floor the finite bad-flag count is at least one on every design. No sharper evaluation of that count can establish the proposed all-prefix conclusion at the automatic cap. HKZ here constructs an existence witness and carries no claim about the oracle budget or the selected first-pass history.

## Implications for Wall 1

Parts 86–101 also protect adaptive choices by simultaneous extension tests. Their twin predicates give $\det E\le(e^\ell g)^r$ for physical head $g$, which takes an $r$-th root when inverted. Here $\det E\le P_*g$ involves only the first power of $g$. Giving up the twin predicates loses their strong coupling between a short head and a small extension. At final oracle rank 506 the comparable Part 101 row is **horizontal 505**, giving 8.08831183 physical under its tests. The 8.15876975 row is horizontal 506. Part 108 does not establish those tests. [Part 101](wall1_qary_rogers.md) · [Width and height conventions](wall1_width_scan.md)

The cap establishes the scale of the actual retained quotient. The probability that its selected minimum clears the height-zero necessary floor remains open. Clearing that floor alone would still leave the conditional plant probability, height-one Voronoi competition, higher heights, and the overall failure budget. Later tours reuse columns and can change earlier prefixes. The 512 fresh height-one appends describe the graph basis, whereas attack heights refer to the additional embedding coordinate. The graph has horizontal rank 1023 for every $A$, including rank-deficient matrices, and the final embedded call adds one dimension to the 505 retained horizontal ones. [Part 108](wall1_first_tour.md) · [Part 114](wall1_idea_drift.md) · [Wall 1](../PROOF_GAP.md)

## Interval reproduction

Run the following standalone Python block with mpmath. Internally V and J store logarithms. For small zeta arguments Euler's transformed alternating eta series has tail at most $2^{-96}$ because the alternating forward differences of $j^{-i}$ lie in $[0,1]$ by the Laplace integral. The remaining zeta tails use the integral test.

```python
from math import comb, floor
from mpmath import iv
iv.dps=50
I=iv.mpf
N,m,n,q=1023,511,512,3329
L=iv.ln
u=iv.exp(I(m)*L(q)/N)
def V(i): return i*L(iv.pi)/2-iv.loggamma(1+I(i)/2)
def J(i): return (L(2/iv.pi)+2*iv.loggamma(2+I(i)/2)/i)/2
def z(i):
    if i==1: return I(0)
    if i<9:
        terms=[I(j)**(-i) for j in range(1,99)]
        eta=I(0)
        for t in range(96):
            eta+=terms[0]/2**(t+1)
            terms=[x-y for x,y in zip(terms,terms[1:])]
        return L((eta+I([0,1])/2**96)/(1-I(2)**(1-i)))
    M=32
    v=sum(I(j)**(-i) for j in range(1,M+1))
    return L(v+I([0,1])*I(M)**(1-i)/(i-1))
A=[I(0)]
for i in range(1,N+1): A.append(A[-1]+V(i)-z(i))
for b in (350,400,406,450,475,500,506,511):
    d,k=b-1,N-b+1
    j={406:L(I('45.6963'))/2,506:L(I('56.2142'))/2}.get(b,J(b))
    a=I(d)/b
    y=a**512
    Z=d*y*L(q)-b*(1-y)*j
    H=iv.exp((Z-V(d))/d)
    T=d*L(u)-Z
    loga=L(I(comb(N,k))/N)+A[N]-A[k]-A[d]
    lc=(L(I('.01'))+z(d)-loga-N*T)/d
    cgoal=(L(I('.01'))+z(d)-loga-d*L(I('.954')))/N
    # decadic logs for small quantities
    row=[H,T,lc/L(10),(lc+L(H))/L(10)]
    scaled=[x*10000 for x in row]
    floors=[floor(float(x.mid)) for x in scaled]
    assert all(I(v)<=x<I(v+1) for v,x in zip(floors,scaled))
    print(b, floors)  # table entries in units of 0.0001
    assert all(x.delta < I('1e-8') for x in row)
    if b==506:
        Q=max(k+1-n,0)*L(q)-(T+k*L(u))
        # HKZ prefix determinant upper bounds, normalized
        def U(i): return (N-i)*sum(J(h)/(h-1) for h in range(N-i+1,N+1))
        ub=U(k+1)-T+L(2*u)
        print('extras',*[float(x.mid) for x in [cgoal,Q/L(10),(Q-L(H))/L(10),U(k),U(k+1),ub/L(10)]])
        assert U(k)<T-L(2) and ub < 0
        for l,s in [(k+1,u),(d-1,q/u)]:
            h=I(l)/(N-l)
            B=s*iv.exp((L(I('.005')*h/2)-V(N))/N)
            lm=(iv.loggamma(1+I(l)/2)+iv.loggamma(I(N+1)/2)
                -L(iv.pi)/2-iv.loggamma(1+I(N+l)/2))
            t=iv.sqrt(B**2-I(N)/4)*iv.exp(-lm/N)/2
            assert 2*t<q
            Umin=V(l)+l*L(t/s)-L(1+h)
            phys=L(u)+Umin-T
            print('overlap',l,float((phys/L(10)).mid),float(((phys-L(H))/L(10)).mid))
            if l==504:
                assert phys/L(10)>I('-495.7219')
                assert (phys-L(H))/L(10)>I('-497.1814')
        assert Q/L(10)>I('-1411.1621') and (Q-L(H))/L(10)>I('-1412.6216')
        assert ub/L(10)<-176 and U(k-1)+L(iv.sqrt(I(5)/4)*q/u)<T-L(2)
        assert I('547.8032')<cgoal<I('547.8033')
        assert H*I('.954')>I('27.4842')
```

## Audit note (Nov 2026)

Independent audit (Codex): CORRECT.

* **Automatic cap.** It holds. At 506, log T = 1207.54637200…; the table's 1207.5463 rounds down, so use the formula or an upward
  rounding when applying it.
* **Haar certificate.** It needs log T ≤ 547.80325 for 0.954·GH. At the automatic cap it gives 1.0415·10⁻⁵⁷⁹ (506) and
  3.4809·10⁻⁸¹⁶ (406). All eight rows were reproduced.
* **Counterexample.** Valid: a unimodular shear of v_518 by v_519 crosses into [T/2, T], and the projected v_519 has physical
  length below 10^{−176.58}.
* **q-ary overlap exponents.** Valid.

The prefix that the reducer actually selects remains open.
