# Joint coverage on the relocated boxes

Normalize the window head to one. Conditional on a surviving prefix, its lattice $D$ has minimum one, determinant $d$, and the fresh shift $x$ is Haar on $T=\mathbb R^j/D$. Put $h=g_j/g_0$ and $r_m=(1-m^2h^2)_+^{1/2}$. The strict forbidden event is the union of the inverse images of the projected open balls under multiplication by $m$. In particular $1/2\le h<1/\sqrt2$ is already deep but admits only height one (a zero-radius section is empty).

## A conditional joint bound

Keep the first $k$ heights with $mh\le\sqrt3/2$, and use balls of radius $1/2$ inside their sections. Each core has probability $p=V_j2^{-j}/d$ by injectivity on the open ball and Haar invariance. For $m<n$ condition on $nx=y$. The image $mx$ is uniform on a translate of $T[q]$, with $q=n/\gcd(m,n)\ge2$, by counting fibers. Lifts meeting the core, scaled by $q$, are 1-separated points of a ball of radius $q/2$. Thus for the core events $A_m$,
$$
 P(A_m\cap A_n)\le p C_j,\qquad
 C_j=\min\{1,6\pi j(1/(.9\sqrt2))^j\}.
$$
Indeed lift those points to the upper hemisphere of radius $q/2$ in dimension $j+1$ by appending a coordinate. Distances can only increase. In a cap of angular radius $\alpha$ with $\sin\alpha=.9\sqrt2/q$, points lie in a Euclidean ball of radius $.9/\sqrt2$ centered on the cap axis at radius $(q/2)\cos\alpha$. The sum of squared pair distances gives $N(N-1)/2\le N^2(.9)^2/2$, so at most six points lie there. A random cap covers each point with probability at least $\sin^j\alpha/(\pi j)$ by integrating $\sin^{j-1}t$ and using $\cos t\le1$. Divide the resulting list bound by $q^j$. This uses the survival condition on the actual prefix, including after earlier tests.

Counting the core hits and applying Cauchy–Schwarz gives the following per-column guaranteed failure fraction:
$$
 L_j=\frac{k p}{1+(k-1)C_j}\le P(F\mid D)
 \le \min\{1,d^{-1} V_j\sum_{m h<1,\ m\ge1} r_m^j\}.
$$
The right side unfolds *all* lifts, so a strict bound below one rules out complete coverage for every such prefix. Heights with smaller positive sections can only increase the left-hand coverage. The script uses $k$ rounded down to a power of two. This loses at most a factor two in the fraction and keeps evaluation inexpensive.

For exact inclusion–exclusion take $a_m$ to be the indicator of the projected ball on $T$ and $q'=m/\gcd(m,n)$. Then the pair term is
$\sum_{u\in D^*}\widehat a_m(q u)\overline{\widehat a_n(q'u)}$, by orthogonality and Parseval. Subtraction of these terms from the sum of the marginals gives the second Bonferroni lower bound. Convolving each torus indicator with the wrapped Gaussian of width $s$ multiplies the summand by $\exp[-\pi s^2(q^2+q'^2)\|u\|^2]$. The sum converges to the sharp pair measure as $s\downarrow0$ by Cauchy–Schwarz and dominated convergence. A finite-width convolution leaks beyond the forbidden event. Counting torus indicators here also avoids mistaking intersections of events for products of lift counts. [V5](wall1_void_fourier.md)

## Results on the twelve boxes

The entries below enclose the deep-chain penalty in nats. Parentheses give the number of start–endpoint pairs for which the all-height volume upper bound proves positive uncovered measure, divided by the number classified as possibly deep. The upper endpoint of every individual **lower certificate** is below 0.117162. This bounds the strength of the certificate, not the true forbidden fraction.

| Width | .25 GSA | .5 GSA | .85 GSA |
|---:|---:|---:|---:|
|406|6.032–6.034 (219442/295571)|3.918–3.920 (222804/297361)|3.313–3.315 (223051/297601)|
|506|6.334–6.335 (268856/345436)|4.321–4.322 (272918/347988)|3.313–3.315 (273454/348576)|
|647|6.495–6.496 (325520/400151)|4.680–4.682 (330309/403353)|3.314–3.315 (331381/404379)|
|800|6.544420–6.544591 (377375/437602)|4.975–4.977 (381542/441621)|3.546–3.548 (382663/443115)|

For example, at width 800 and cut .25, start 186 and endpoint 985 (zero-based), 256 heights give failure probability at least $\exp(-308.324308)$ throughout the box, versus $\exp(-313.869485)$ from one half-radius core. The factor of approximately 256 at this column has negligible effect on the log survival budget.

At the closest target even granting the whole new penalty in addition to the Part 77 allowance leaves more than **219215.455 nats** in the log of the upper-bound integral. Taking the best of multiple conditional estimates at one endpoint costs at most their summed log penalties. The sum is used here only to upper-bound the achievable improvement. It would be invalid to multiply separate survival bounds at the same endpoint as if the tests were independent. Even granting the separate Part 78 ceiling of 2356 more nats leaves over 216859.455. [Part 77](wall1_lcz_all_widths.md) · [Part 78](wall1_dual_coverage.md)

No column reaches hard exclusion by the joint lower test. For the 60227 remaining pairs at the closest target the two bounds leave actual complete coverage undecided. The pair estimate resolves dilution among different torsion grids, but restricting to injective cores loses volume exponentially in rank. The Fourier formula for full sections would require conditional control of their overlaps and single-section coverage on surviving prefixes. No power of the full short-vector mean or heuristic independence assumption is used.

## Interval certificate

Run at the repository root. For each endpoint choose the strongest certified deep start. Earlier survival of the simultaneous window tests implies survival of each candidate prefix. The tower property therefore adds one log penalty per endpoint. This schedule allows overlapping windows and never charges two starts at the same endpoint. The two ends of the computed interval bracket the size of this particular certificate across the entire box. The hard-hole count uses the coarser upper bound $V_j/(hd)$ and counts start–endpoint pairs, not distinct fresh columns.

```python
from pathlib import Path
from mpmath import iv as I
import numpy as np
I.dps=40
root=Path("docs/research")
def read(name):
    return (root/("wall1_"+name+".md")).read_text()
s=read("surviving_mass")
n=1023
M=10**9
rows=read("lcz_all_widths").split("d k numerator LCZ Part65\n")[1].split("```")[0]
C=[0,0]+[min(map(int,l.split()[-2:])) for l in rows.strip().splitlines()]
exec(s[s.index("def profile"):s.index("def ceiliv")])
def bounds(x):
    return int((M*x).a)-1,int((M*x).b)+1
# k=2^a is available when log(1/h) exceeds the corresponding threshold.
threshold=np.array([bounds(I.ln(2**(a+1)/I.sqrt(3))) for a in range(20)])
deep=bounds(I.ln(2)/2)
constants={}
for j in range(1,800):
    half=I.mpf(j)/2
    logV=half*I.ln(I.pi)-I.loggamma(1+half)
    corr=min(I.mpf(1),6*I.pi*j*(1/(I.mpf(".9")*I.sqrt(2)))**j)
    terms=[logV-j*I.ln(2)+a*I.ln(2)-I.ln(1+(2**a-1)*corr)
           for a in range(20)]
    constants[j]=np.array([bounds(x) for x in terms]),bounds(logV)[1]
emit_pairs=False  # Set True to print each definitely deep (start, endpoint, lower log fraction).
for b in (406,506,647,800):
    slope=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    for frac in (".25",".5",".85"):
        v=np.array(solve(b,I.mpf(frac)*I.exp((2*b-n-1)*slope),False))
        T=np.r_[0,np.cumsum(v)]
        best=np.full((2,n),-10**16,dtype=np.int64)
        pairs=holes=0
        for j in range(1,b):
            terms,lv=constants[j]
            drop=v[:-j]-v[j:]
            H=j*v[:-j]-(T[j:n]-T[:n-j])
            err=2000*(j-1)
            possible=drop+2000>=deep[0]
            pairs+=int(possible.sum())
            holes+=int((possible & (lv+H+err+drop+2000<0)).sum())
            for e in (0,1):
                sign=2*e-1
                x=drop+sign*2000
                mask=x>=deep[1-e]
                a=np.searchsorted(threshold[:,1-e],x)-1
                assert a.max()<19 and (a[mask]>=0).all()
                z=H+sign*err+terms[a,e]
                if b==800 and frac==".25" and j==799 and e==0:
                    i=int(np.argmax(x))
                    print("example",i,i+j,2**int(a[i]),int(z[i]),
                          int(H[i]-err+terms[0,0]))
                if emit_pairs and e==0:
                    for i in np.flatnonzero(mask):
                        print(b,frac,i,i+j,int(z[i]),"/ 1e9 log fraction")
                np.maximum(best[e,j:],np.where(mask,z,-10**16),out=best[e,j:])
        def total(arr):
            val=I.mpf(0)
            for z,count in zip(*np.unique(arr,return_counts=True)):
                if z != -10**16:
                    p=I.exp(I.mpf(int(z))/M)
                    assert p<1
                    val-=int(count)*I.log1p(-p)
            return val
        print(b,frac,pairs,holes,bounds(I.exp(I.mpf(int(best[1].max()))/M))[1], int((10**6*total(best[0])).a),
              int((10**6*total(best[1])).b)+1,flush=True)
```
