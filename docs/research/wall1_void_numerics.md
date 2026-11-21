# Single-window void probabilities at fixed geometric profile

Normalize the radius to one and take GS lengths $g_j=r^j$, $0<r<1$. The tests below concern a single start and count all strict short pairs modulo sign, including nonprimitive pairs. Write $P_w=\Pr(N=0)$. The exact integral on shallow slopes gives $P_w\le e^{-E}$. Sequential importance sampling on steeper slopes gives a fitted exponent close to one at widths 20, 24 and 30. The estimates depend on the width and slope. They give no uniform exponent at the application widths.

## Exact integration on the disjoint-ball range

Write $D_j=\prod_{i<j}g_i$, $V_j=\pi^{j/2}/\Gamma(1+j/2)$, and let $L_j$ denote the prefix lattice of rank $j$. The mean from [Part 70](wall1_window_asymptotics.md) is $E=\sum_{j=1}^{w-1}e_j$, where
$$
e_j=\frac{V_j}{D_j}\sum_{m\ge1,\,mg_j<1}(1-m^2g_j^2)^{j/2}.
$$

**Theorem.** If $g_{w-1}\ge\sqrt{3}/2$, then $P_w=\prod_{j=1}^{w-1}(1-e_j)$. More generally the formula is exact up to the last prefix satisfying this condition, giving an upper bound on full-window survival.

**Proof.** Condition on a surviving prefix. A fresh horizontal shift is uniform on the torus modulo $L_j$, since the centered GS rectangle is a fundamental domain by backward reduction. Only height one can fail. Its forbidden set is the projected open ball of radius $s_j=\sqrt{1-g_j^2}\le1/2$. Translates have disjoint interiors because the prefix minimum is one. The conditional forbidden fraction is therefore exactly its Euclidean volume divided by $D_j$, independently of the surviving prefix shape. Multiplication gives the claim. In particular $f(E)=E$ works on this range by $1-x\le e^{-x}$. More precisely $0\le-\log P_w-E\le\sum_j e_j^2/[2(1-\max e_j)]$ if the maximum is below one, by the logarithm series. This argument uses the fresh-column torus of [Part 68](wall1_covering_fraction.md); independence of individual vector tests is unnecessary.

Exact integral values, rounded. Each cell gives $(E,P_w)$.

| Width | $r=.995$ | $r=.98$ | $r=.97$ |
|---:|---:|---:|---:|
|2|(.199750,.80025016)|(.397995,.60200503)|(.486210,.51379017)|
|3|(.262425,.75009403)|(.646860,.45218709)|(.857718,.32291274)|
|4|(.284111,.73382816)|(.818519,.37456490)|(1.171016,.22174490)|
|5|(.291968,.72806229)|(.942589,.32809270)|(1.448079,.16030763)|

## Which coefficients survive?

At width two the complete answer is $P_2=(1-2\sqrt{1-r^2})_+$. Indeed a surviving first shear must satisfy $x=|\mu_{10}|\ge t=\sqrt{1-r^2}$, and whenever this has positive measure the higher multiples are too tall. The near-diagonal cube with all shear magnitudes below $t$ therefore contains no survivors in any width. In the disjoint-ball range even conditioning on *full* survival leaves $x$ exactly uniform on $[t,1/2]$, since every continuation has the same survival probability from every passing prefix.

At width three there is a sharper description near extinction. For $t<x<1/2$, reflect the planar prefix so its generators are $u=(1,0),v=(x,r)$. Its squared covering radius is
$$
C^2(x,r)=1/4+[(r^2+x^2-x)/(2r)]^2.
$$
Indeed the triangle $0,u,v$ and its reflected translate tile the plane. It is acute since $0<x<1/2$ and $r^2+x^2>x$. Its circumcenter is $(1/2,(r^2+x^2-x)/(2r))$. The circumdisk is empty of other lattice points: on rows of heights 0 and $r$ the listed vertices are nearest to the center, and rows at heights at most $-r$ or at least $2r$ are farther (here $r\ge\sqrt3/2$, center height at most $r/2$, and $C<r$). The triangle is covered by disks of radius $C$ at its vertices, as seen by subdividing at its circumcenter and side midpoints. Thus the covering radius is attained. Continuity handles the endpoints.

Only last coefficient one matters for $r\ge\sqrt3/2$. A fresh shift survives with positive probability precisely when $C^2(x,r)>1-r^4$; equality leaves finitely many torus points. The maximum over passing shears occurs at $x=t$, where $C^2=1/[2(1+t)]$. Consequently the width-three cutoff $r_*$ is the unique root in $(\sqrt3/2,1)$ of
$$
2(1+\sqrt{1-r_*^2})(1-r_*^4)=1
$$
(about .89873347). The left side is strictly decreasing and crosses one. $P_3>0$ exactly for $r>r_*$. Close to the cutoff survivors require a first shear close to $t$ and a final shift close to a circumcenter modulo the prefix lattice.

There is also an exact two-variable integral for the entire intermediate range $r_*<r<(\sqrt3/2)^{1/2}$. Set $y=|\mu_{21}|$, $s^2=1-r^4$, $a=\min(1/2,\sqrt{(s^2-r^2y^2)_+})$ and $b=\min(1/2,\sqrt{(s^2-r^2(1-y)^2)_+})$. After integrating the first coordinate of the final column exactly,
$$
P_3=4\int_t^{1/2}\int_0^{1/2}
\min\{1-2a,1-2b,(x-a-b)_++(1-x-a-b)_+\}\,dy\,dx .
$$
Indeed only the two nearest vertical rows can reach the disk since $s<r$. On the unit horizontal circle they cut arcs of radii $a,b$ at center separation $x$. On each of the two paths between the centers the residual gap is its positive length after subtracting the two radii, except when one arc contains the other. The minimum with the two single-arc complements accounts for containment. An empty arc may be represented by a point without changing length. Reflection symmetry in the two independent shear signs supplies the factor four.

In fact $P_3=\Theta((r-r_*)^3)$ from above. To see this, put $h=C^2(x,r)-(1-r^4)$. The derivative in $r$ of $h(t(r),r)$ is strictly positive, while the partial derivative in $x$ at the maximizing endpoint is strictly negative $(0<t(r_*)<1/2)$. Thus the admissible shear interval has length comparable to $r-r_*$, and $h$ decreases across it with slope bounded away from zero and infinity in magnitude. In a neighborhood of either deep hole the loss of squared nearest-site distance under displacement $d$ is comparable to $|d|$: the three incident vertex directions positively span the plane because the triangle is strictly acute. Expanding the three squared distances gives the corresponding linear bounds with an $O(|d|^2)$ remainder. The constants are uniform near the critical shape; all other sites have a strict gap, and the compact complement of the hole neighborhoods has a strict deficit. The surviving torus area is therefore comparable to $h^2$. Integrating this over the shear interval proves the cubic law. Here the mean tends to a finite limit, so a single Poisson curve cannot describe the approach to the packing boundary.

## A bound extending past disjointness

If $g_{w-1}>1/\sqrt2$, then
$$
-\log P_w\ \ge\ \sum_{j=1}^{w-1}(2g_j^2-1)e_j\ \ge\ (2g_{w-1}^2-1)E.
$$
Given a surviving prefix, let $K$ be the number of lifts of the fresh shift in the radius-$s_j$ ball. These lifts are pairwise separated by at least one. For $K>0$, their squared pair distances sum to $K\sum_i\|v_i\|^2-\|\sum_i v_i\|^2\le K^2s_j^2$, and are at least $K(K-1)/2$ in total. Hence $K\le1/(2g_j^2-1)$. Unfolding gives conditional mean $e_j$ because only height one contributes. Therefore the conditional probability of failure is at least $(2g_j^2-1)e_j$. Multiply the conditional bounds. This gives a linear exponent uniformly on every subrange $g_{w-1}\ge c>1/\sqrt2$. At the large-width balanced slope the terminal length tends to zero, so this list-size argument stops before the layers supplying most of the mean.

## Sequential importance sampling

At each endpoint extend every surviving prefix by an independent uniform column. Enumerate positive last coefficients and recursively enumerate all earlier integer lifts within the remaining squared norm budget. Keep the passing particles and resample uniformly with replacement to the original population size. The product of the passing fractions is an unbiased normalizing-constant estimate in exact arithmetic. Indeed, multiplying the resampled empirical average of any terminal test function by the passing fraction gives, conditionally in expectation over resampling, its original empirical sum over passing extensions divided by population size. Iterating this identity proves unbiasedness, with extinct populations assigned zero weight. Enumeration used binary64 and strict inequalities. Equality for a random fresh shift has probability zero in the continuous model. The reported standard errors describe sampling, not rounding.

Each row uses 64 independent replicate populations of 512 particles. SE is the sample standard deviation across replicate products divided by eight. Each parameter run restarts the same pseudorandom seed, so different rows need not be independent. A sampler check at width five and ratio .97 with 24 populations of 192 gave $.16381\pm.00304$ against the exact .16031.

| Width | Ratio | Exact mean (rounded) | Estimated void probability | SE | $-\log \widehat P/E$ |
|---:|---:|---:|---:|---:|---:|
|20|.98|1.3485|0.2161|0.0016|1.136|
|20|.975|2.3216|0.071578|0.0006|1.136|
|20|.97|4.6272|0.0053515|7.5e-05|1.130|
|20|.968|6.3849|0.00072696|1.2e-05|1.132|
|20|.965|10.807|3.9188e-06|1.1e-07|1.152|
|24|.98|1.3588|0.21345|0.0017|1.137|
|24|.975|2.4529|0.062515|0.00059|1.130|
|24|.97|5.7775|0.0016216|2.1e-05|1.112|
|24|.968|8.9303|5.0892e-05|8.6e-07|1.107|
|24|.965|18.694|8.7705e-10|3.7e-11|1.116|
|30|.98|1.3659|0.21036|0.0015|1.141|
|30|.975|2.6369|0.05186|0.00056|1.122|
|30|.97|8.9461|6.8442e-05|1.1e-06|1.072|
|30|.968|18.1|4.7887e-09|1.7e-10|1.058|
|30|.965|61.24|all 64 extinct|unresolved|—|

Unweighted least squares on $\log(-\log\widehat P)=\log A+c\log E$ gives $(A,c)=(1.131,1.004)$ at width 20, $(1.137,.991)$ at width 24 and $(1.153,.969)$ at width 30. The last fit uses four resolved rows. Over the measured range the exponent per unit mean is roughly constant. For example, at width 24, increasing the mean from 2.45 to 18.69 raises the exponent from 2.77 to 20.85. This favors approximately linear growth over logarithmic growth there. Even a ten percent discrepancy in the exponent matters for the probability itself. Extinction at $E=61.24$ records a failure of sampling resolution.

At $(w,r)=(20,.968)$ the survival-weighted mean of the absolute first shear is $.37639\pm.00186$. The mean absolute entry over the other 189 shears is $.26469\pm.00015$, against the unconditioned .25 for both statistics. We weighted terminal survivor averages by the replicate product and divided by the sum of products. The errors use the replicate residuals for this ratio. Thus survival strongly biases the first shear; the bulk mean shows a smaller shift. The bulk mean alone cannot locate a unique dominant region in 190 dimensions. The proved mechanism is successive torus avoidance, with concentration around deep holes at the width-three boundary. The missing estimate for larger windows is control of forbidden-set overlap along the *surviving* prefix law when the last GS lengths are small. The simulations give neither a certificate at $\log E\gtrsim130$ nor a joint law for overlapping starts.

## Reproduction

Save the following as w1void.cpp and compile with g++ -O3 -std=c++17 w1void.cpp -o w1void. Arguments are width (2 to 30), ratio, population size and number of replicates. Output columns are the replicate product and its products with the two terminal shear statistics (use width at least three for both diagnostics).

```cpp
#include <array>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>
using namespace std;
constexpr int D=30;
using Basis=array<array<double,D>,D>; // column first
mt19937_64 rng(541897);
double g[D];
bool hit(const Basis &b,int i,int j,array<int,D>&x,double left){
    if(i<0) return true;
    double s=0;
    for(int k=i+1;k<=j;k++) s+=b[k][i]*x[k];
    double d=sqrt(left)/g[i];
    for(int n=ceil(-s-d);n<=floor(-s+d);n++){
        x[i]=n;
        double t=g[i]*(s+n), rest=left-t*t;
        if(rest>0 && hit(b,i-1,j,x,rest)) return true;
    }
    return false;
}
bool passes(const Basis &b,int j){
    array<int,D> x{};
    for(int m=1;m*g[j]<1;m++){
        x[j]=m;
        if(hit(b,j-1,j,x,1-pow(m*g[j],2))) return false;
    }
    return true;
}
int main(int argc,char**argv){
    int w=atoi(argv[1]), B=atoi(argv[3]), reps=atoi(argv[4]);
    double r=atof(argv[2]);
    for(int j=0;j<w;j++) g[j]=pow(r,j);
    for(int h=0;h<reps;h++){
        vector<Basis> p(B);
        double z=1, head=0, bulk=0;
        for(int j=1;j<w;j++){
            vector<int> ok;
            for(int i=0;i<B;i++){
                for(int k=0;k<j;k++) p[i][j][k]=generate_canonical<double,53>(rng)-.5;
                if(passes(p[i],j)) ok.push_back(i);
            }
            z*=double(ok.size())/B;
            if(ok.empty()) break;
            if(j==w-1){
                for(int id:ok){
                    head+=abs(p[id][1][0])/ok.size();
                    for(int a=2;a<w;a++) for(int k=0;k<a;k++)
                        bulk+=abs(p[id][a][k])/(ok.size()*(w*(w-1)/2.-1));
                }
                break;
            }
            vector<Basis> next;
            next.reserve(B);
            uniform_int_distribution<int> draw(0,int(ok.size())-1);
            for(int i=0;i<B;i++) next.push_back(p[ok[draw(rng)]]);
            p.swap(next);
        }
        cout.precision(16);
        cout<<z<<" "<<z*head<<" "<<z*bulk<<"\n";
    }
}
```

The following Python 3.10+ driver reproduces the tables, fits and shear diagnostics.

```python
import math,statistics as st
def layers(w,r):
    return [math.pi**(j/2)/math.gamma(1+j/2)/r**(j*(j-1)/2)*sum(max(0,1-(m*r**j)**2)**(j/2) for m in range(1,int(r**-j)+1)) for j in range(1,w)]

from subprocess import check_output
for w in (2,3,4,5):
    for r in (.995,.98,.97):
        e=layers(w,r)
        print(w,r,sum(e),math.prod(1-v for v in e))
for w in (20,24,30):
    X,Y=[],[]
    for r in (.98,.975,.97,.968,.965):
        args=["./w1void",str(w),str(r),"512","64"]
        rows=[list(map(float,line.split())) for line in
              check_output(args,text=True).splitlines()]
        weights=[v[0] for v in rows]
        p=st.mean(weights)
        e=sum(layers(w,r))
        if p==0:
            print(w,r,e,"extinct")
            continue
        f=-math.log(p)
        print(w,r,e,p,st.stdev(weights)/8,f/e)
        if (w,r)==(20,.968):
            for i in (1,2):
                m=sum(v[i] for v in rows)/sum(weights)
                se=st.stdev(v[i]-m*v[0] for v in rows)/(8*p)
                print("conditional shear",m,se)
        X.append(math.log(e))
        Y.append(math.log(f))
    c,logA=st.linear_regression(X,Y)
    print("fit",math.exp(logA),c)
```
