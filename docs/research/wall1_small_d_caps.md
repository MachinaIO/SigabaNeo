# Small-dimensional packing caps in the rank-1023 chain


The strongest terminal lower bound obtained here is **0.15090300 at width 800**, or **0.03498391** times the Gaussian radius of the terminal quotient. Small-dimensional packing bounds improve all four chain certificates. They also expose a second relocation of the relaxed mass. The first boxes constructed with the new caps still have hard two-coset exclusions. Moving the boxes slightly into the feasible region removes every deep W2 exclusion and leaves at least **218002 nats** at the closest target.

## Block caps

Write $V_d=\pi^{d/2}/\Gamma(1+d/2)$. A unit-radius packing density bound $\Delta_d$ gives $P_d=d\log2+\log\Delta_d-\log V_d$ for periodic packings. The lattice cap $H_d$ bounds $\log(\lambda_1^d/\det L)$. The array `lattice[d]/10**9` in the certificate specifies every $H_d$ for $2\le d\le1023$ and `P[d]/10**9` specifies the corresponding periodic cap. These are minima of the certified inputs below, with outward rounding at the indicated scale. Optimality among all possible bounds is open.

* For lattice ranks 2 through 8 use $H_d=\tfrac12\log q_d$ with $q_d=4/3,2,4,8,64/3,64,256$, respectively, before rounding. Rank 24 gives $24\log2$. The exact bounds also apply to general packings at 2, 3, 8 and 24. At 4 through 7 the code uses the separately proven periodic bounds for W2. [Exact packing results and references](https://dspace.mit.edu/server/api/core/bitstreams/6eda1660-ef8c-4d00-80cf-50805b5b2324/content)
* The decimals in the script are the outward-rounded **volume-density upper bounds** of Cohn's May 10, 2025 Table 1. At 4–7 and 9–16 they come from the rigorous three-point bound. Cohn, de Laat and Salmon describe the interval linear solve and positive-definiteness checks in §6.3. For 17–23, 25–48, 56, 64 and 72 the archive supplies exact rational LP auxiliary-function coefficients in `rigorous.txt`. Here the published certified bounds are inputs. The script rechecks their conversion to log caps; it does not rerun those authors’ polynomial or SDP verifiers. These stronger data supersede the original degree-limited Cohn–Elkies Table 3, including its dimension-33 bound. [Table and certificate archive](https://dspace.mit.edu/entities/product/d8a88a76-3fa7-4b75-89ef-ea71a0e05b77) · [Three-point certificate](https://arxiv.org/pdf/2206.15373) · [Original Cohn–Elkies bounds](https://annals.math.princeton.edu/wp-content/uploads/annals-v157-n2-p09.pdf)
* In every rank take the minimum with Parts 65 and 77, including the LCZ witness evaluated again with rational Gegenbauer coefficients and interval logarithms. The original grid search selected the witnesses heuristically. Each witness passes its sign tests independently of that search. Finally propagate Mordell's inequality $H_d\le dH_{d-1}/(d-2)$ as a candidate upper bound on the optimal lattice log constant. Indeed, for unit determinant, a shortest primitive dual normal has length at most $\sqrt{\gamma_d}$. Its orthogonal lattice section has that length as determinant and minimum at least the ambient minimum. Taking suprema gives $\gamma_d\le\gamma_{d-1}\gamma_d^{1/(d-1)}$ and the stated recurrence for $(d/2)\log\gamma_d$. Only lattice rows receive this propagation. [Part 65](wall1_one_sided_terminal.md) · [Part 77 witnesses](wall1_lcz_all_widths.md)

## Primitive-chain certificate

Each row gives simultaneous lower bounds for every fully reduced basis, outside a Haar event of probability below 0.01 **per width**. Let $k=1023-\beta$ and $R_T=(\det T/V_\beta)^{1/\beta}$.

| $\beta$ | $g_k$ lower | $g_k/R_T$ lower | log failure upper |
|---:|---:|---:|---:|
|406|0.00654258|0.00384694|−4.60897|
|506|0.01696601|0.00916855|−4.61955|
|647|0.04255796|0.01517095|−4.61267|
|800|0.15090300|0.03498391|−4.61213|

For each admissible start the shortest head in the projected block gives $dS_{i+1}\le(d-1)S_i+S_{i+d}+H_d$, where $S_i$ is the prefix log determinant. The Part 77 backward recurrence constructs a supersolution with a minimizing outgoing width at each ordinary row. At a positive maximum of $S-U$ the minimizing row forces equality at its left neighbor; the endpoints have difference zero. At the exceptional row, violation of either radius gives the leftward comparison directly (with left coefficient $1$ or $1-1/\beta$). Thus either failure forces the same primitive chain below the same caps $U$ at the Part 65 cuts. Integrating its counting density there gives the displayed upper bounds by Markov. The dent search only selects a witness; the final interval inequality certifies it. [Chain integral and cuts](wall1_one_sided_terminal.md) · [Maximum principle](wall1_lcz_all_widths.md)

## Surviving mass and coverage

All log columns are in nats. The cut is $\rho=cG_\beta$ with the Part 71 GSA formula. $J$ is the oriented relaxed first moment. Its lower endpoint comes from one box and its upper endpoint from the full dominating orthant. The middle three columns enclose, throughout that box, the exact width-three log acceptance, the truncated V7 penalty for the Part 77 greedy shallow schedule, and the W2 finite penalty summed over fresh columns. The residual lower bound allows optimized disjoint truncated V7 schedules and the best deep W2 start at each column.

| $\beta$ | $c$ | $\log J$ | $\log W_3$ | V7 | W2 | residual lower |
|---:|---:|---:|---:|---:|---:|---:|
|406|.25|[802442,824629]|[−487,−414]|[6,7]|[167,169]|795649|
|406|.50|[817244,832074]|[−467,−399]|[5,6]|[156,158]|810482|
|406|.85|[819633,833098]|[−456,−391]|[4,5]|[156,158]|812882|
|506|.25|[565585,589112]|[−458,−388]|[6,7]|[120,121]|558869|
|506|.50|[582501,598412]|[−439,−373]|[5,6]|[117,119]|575806|
|506|.85|[586903,600368]|[−423,−361]|[4,5]|[116,118]|580225|
|647|.25|[367307,389685]|[−437,−371]|[7,8]|[72,74]|360659|
|647|.50|[382201,398487]|[−418,−356]|[5,6]|[70,71]|375575|
|647|.85|[387088,400793]|[−403,−344]|[4,5]|[68,70]|380478|
|800|.25|[224585,248264]|[−423,−358]|[7,8]|[22,24]|218002|
|800|.50|[241549,258762]|[−404,−343]|[5,6]|[21,23]|234985|
|800|.85|[247747,261847]|[−388,−332]|[4,5]|[20,22]|241200|

For a deep column at relative height $h<1/\sqrt2$ let $r=R\sqrt{1-h^2}$ with $R$ the head, and $B=P_j+\log\det D-j\log r$ for its prefix lattice $D$. Prefix survival plus one missed shift produces a two-coset packing, so $B<\log2$ excludes that profile. The ordinary inward recurrence with all the new lattice caps produces the same four hard exclusions on each of the twelve initial boxes. All end at column 1022 (zero-based), with prefix ranks 48, 56, 64 and 72 and respective starts 974, 966, 958 and 950. For the replacement centers impose the auxiliary inward caps $\min(H_j,P_j-\log2)$ at $7\le j<\beta$ with extra outward slack on the subtraction. This steers the box search only. The full-domain upper integral and all chain radii use the original certified caps. At $j\le6$ the adjacent slope bound prevents deep windows. The script checks every possible deep pair over each replacement box. All have $\lfloor e^B\rfloor\ge2$. A maximal separated set on the prefix torus covers it by radius-$r$ balls, so the conditional missed fraction is at most $1-1/\lfloor e^B\rfloor$. Maximizing the resulting penalty per endpoint handles overlapping windows by successive conditioning. [W2 packing and coverage proof](wall1_hole_filling2.md)

The integer-centered boxes perturb the first 1022 log lengths by at most $10^{-6}$ before centering. Their prefix-coordinate volume is $(2\cdot10^{-6})^{1022}/1023$. The directed checks certify the radius cut, every block facet, the eight-bin width-three integration and the greedy V7 schedule. To allow other disjoint shallow schedules, use $e_j\le V_j<6$ at each charged column. The pointwise minimum of separate conditional probability upper bounds dominates their product. Thus the log of the resulting **upper-bound integral** is at least the box log mass plus the lower log width-three factor minus $6n$ and the upper W2 penalty. For a fixed greedy schedule one may substitute its tabulated V7 upper endpoint for $6n$. The relaxed upper endpoint also bounds either weighted integral from above. A chain count below $-\log100$ would certify a target; even at width 800 and quarter GSA the optimized-schedule residual exceeds that threshold by 218006 nats. Whether the actual joint shortest-vector tests suppress the surviving mass sufficiently remains open. [Part 71 mass and width-three integral](wall1_surviving_mass.md) · [Truncated V7](wall1_void_combined.md)

## Certificate

Run the Python block from the repository root with NumPy and mpmath. To emit the full cap table in integer billionths of a nat, insert `for d in range(2,n+1): print(d,lattice[d],P[d])` immediately after `lattice = C.copy()`.

```python
from pathlib import Path
from fractions import Fraction as Q
from math import comb
root = Path("docs/research")
def read(name):
    return (root / ("wall1_" + name + ".md")).read_text()
def src(name):
    return read(name).split("\n```python\n", 1)[1].split("\n```", 1)[0].split("\n ```", 1)[0]
base = src("surviving_mass")
exec(base.split("for b,rounded")[0])
p77 = src("lcz_all_widths")
exec(p77[p77.index("def cert"):p77.index("for d in range(2,n+1):")])
tab = read("lcz_all_widths").split("d k numerator LCZ Part65\n")[1].split("```")[0]
P = C.copy()
for line in tab.strip().splitlines():
    d,k,a,lc,old = map(int,line.split())
    assert old == C[d] and cert(d,d,a,k)[0] == lc
    C[d] = min(old,lc)
    P[d] = lc if 4 <= d <= 7 else C[d]
density = """
.6361073321551329 .5126451306253027 .4103032818801865 .3211471056675559 -
.1911204152968963 .1434100871082547 .1067252934567631 .0797117710668987
.0601644380983860 .0450612211935181 .0337564432797899 .0249944093845237
.0184640903350649 .0134853404450862 .0098179551395438 .0071270536033763
.0051596603948176 .0037259419689206 .0026842798864291 -
.0013841907222857 .0009910238892216 .0007082297958617 .0005052542161057
.0003598581852089 .0002559028743732 .0001817083813917 .0001288432887595
.0000912356039023 .0000645221967438 .0000455743843107 .0000321530553313
.0000226586900106 .0000159506499105 .0000112168687009 .0000078801051697
.0000055306464395 .0000038780970907 .0000027169074727 .0000019017703144
.0000013300905665 .0000009295151556 .0000006490757338 .0000004529067791
""".split()
dens = dict(enumerate(density,4))
dens.update({56:".0000000248393710",64:".0000000013129981",72:".0000000000673580"})
for d,s in dens.items():
    if s=="-": continue
    u = I.mpf(d)/2
    H = d*I.ln(2)+I.ln(I.mpf(s))+I.loggamma(1+u)-u*I.ln(I.pi)
    bound = int((M*H).b)+1
    assert bound-2 < M*H < bound
    C[d],P[d] = min(C[d],bound),min(P[d],bound)
C[24] = P[24] = int((24*M*I.ln(2)).b)+1
# Mordell's inequality for lattice minima only.
for d in range(3,n+1):
    C[d] = min(C[d], (d*C[d-1]+d-3)//(d-2))
lattice = C.copy()
exec(p77[p77.index("p65=src"):p77.index("combined=src")])
w2 = src("hole_filling2")
exec(w2[w2.index("def ends(x)"):w2.index("for b in (406")])
def coverage(v,b):
    v=np.array(v,dtype=np.int64)
    T=np.r_[0,v.cumsum()]
    low=np.zeros(n,dtype=np.int64)
    high=low.copy()
    locations=[]
    hits=0
    possible_hits=0
    for j in range(1,b):
        drop=v[:-j]-v[j:]
        slack=P[j]-j*v[:-j]+T[j:-1]-T[:-j-1]
        kl=(drop-2000)//10**6
        ku=(drop+2000+10**6-1)//10**6
        possible=drop+2000>=deep[0]
        certain=drop-2000>deep[1]
        hi=slack+2000*(j-1)+j*grid[np.clip(kl,345,20000)-345,1]
        lo=slack-2000*(j-1)+j*np.where(ku>20000,0,grid[np.clip(ku,345,20000)-345,0])
        assert not np.any(kl>20000)
        kmin=np.searchsorted(logs[:,1],lo,side="right")
        kmax=np.searchsorted(logs[:,0],hi,side="right")
        locations.extend((int(i),j) for i in np.flatnonzero(certain & (kmax<2)))
        hits+=int(np.sum(certain & (kmax<2)))
        possible_hits+=int(np.sum(possible & (kmin<2)))
        low[j:]=np.maximum(low[j:],np.where(certain & (kmax<1001),weights[np.clip(kmax,2,1001)-2,0],0))
        high[j:]=np.maximum(high[j:],np.where(possible,weights[np.clip(kmin,2,1001)-2,1],0))
    return hits,possible_hits,int(low.sum()//M),int(-(-high.sum()//M)),locations

combined=src("void_combined")
boxes=combined[combined.index("for b in (406,506,647,800):"):combined.index("        q,r=divmod")]
boxes=boxes.replace("v=solve(b,R,False)", """C=lattice
        first=solve(b,R,False)
        initial=coverage(first,b)
        C=lattice.copy()
        if initial[1]:
            for j in range(7,b):
                C[j]=min(C[j],P[j]-693147182)
        v=solve(b,R,False) if initial[1] else first
        C=lattice""")
width3=base[base.index("        m=I.exp"):base.index("        print(b,frac")]
exec(boxes+width3+"""
        hits,possible,p0,p1,_=coverage(v,b)
        assert min(y-x for x,y in zip(v,v[1:]))>=-55000000
        assert possible==0
        print('box',b,frac,initial[4],flooriv(L),ceiliv(H),flooriv(wl),ceiliv(wh),
              shallow(v,b),(p0,p1),flooriv(L+wl-6*n-p1),flush=True)
""")
```

## Audit note (independent audit, Nov 2026)

Every cap entering the general-packing (W2) penalties is a general-packing bound; lattice-only values (exact Hermite
constants, Mordell) enter only the lattice caps used for projected windows. The 16-digit three-point values for d = 4–7, 9–16
could not be traced to a retrievable source; rerunning with the paper's (arXiv 2206.15373) rounded-up values leaves all box
residuals unchanged and moves the chain only in the last digits. Conservative headline values (paper inputs):
g_{1023−β} ≥ 0.00654258 / 0.01696600 / 0.04255794 / 0.15090292 and g/R_T ≥ 0.00384694 / 0.00916855 / 0.01517094 / 0.03498389.
The MIT archive item has since been updated (Nov 18, 2026); the Cohn–Elkies decimals used here were checked against its
rigorous.txt full-text copy.
