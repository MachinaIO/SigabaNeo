# Terminal minima on rank-1023 Haar lattices

For each fixed width the probability is at least 0.99 that every basis passing its indicated predicate has terminal quotient minimum at least the tabulated radius. The maximum certified fraction of the comparison target is 0.45320138 (rounded down) for two-block generalized slide at width 511, and 0.45438568 for the terminal variant at width 512. The latter fraction falls to 0.29838066 at 800 and rises to 0.33830562 at 900. These are maxima of the two specified certificate scans. A simultaneous 559-width probability or optimal output quantile would require a separate argument.

## Predicates and first moments

Write $b=\beta$, $k=1023-b$, $r=k+1$, $W=L_k$, $P=L_r$, $D=\det P$, and $q=D/\det W$. Both algorithms make the named terminal head a shortest vector of the projected quotient. For $K_r=\exp(A_n-A_r-A_{b-1})/(2n)$ the primitive incidence intensity at $P$ is $nK_rD^{n-1}dD$ times Haar probability on its normalized shape. Count each extension once regardless of how many flags certify it. The $(A_j)$ and the audited upper bounds $H_j=C[j]/10^9$ for $\log(\gamma_j^{j/2})$ use the normalizations in [Part 86](wall1_dual_pinning.md).

* **Two blocks, 342–511.** Take the unchanged-tour twin factor $a=(1+10^{-6})\exp((k-1)H_b/[b(b-1)])$. For the first length $x$, the twin bounds give $x\le a(D/q)^{1/k}$ and $D/x\le(aq)^k$. Elimination gives $D\le e^U q^r$ with $U=rk\log(a)/(k-1)$. Integrating the radial density bounds the mean count of bad extensions by $K_r e^{nU}\rho^{nr}$ at radius $\rho$. Here $F=1$ below. Positive tour slack and the capped DBKZ subroutine are essential to the algorithmic interpretation. [Part 88](wall1_li_walter.md) · [Part 90](wall1_selfdual_sharpen.md)
* **Terminal variant, 512–900.** Put $c=1.0001$, $U=H_r+r\log c$. The test $1/q\le c\lambda_1(P^*)$ implies the same scalar determinant inequality by Hermite. More precisely, for unit dual shape $H=D^{1/r}P^*$ put $J=\lambda_1(H)e^{-H_r/r}\le1$. A bad extension satisfies $D< e^U\rho^r J^r$. Thus the radial integral gains a factor $\mathbb E J^{nr}\le\mathbb E J^{r(b-1)}$. We retain the Part 87 exponent and split grid to reproduce its certificate. For $p=r(b-1)$, each split $0<f<1$ gives $\mathbb E J^p\le f^p+\Pr(J\ge f)$. A primitive-pair count in a ball of radius $f e^{H_r/r}$ has mean $\mu=V_r(f e^{H_r/r})^r/(2\zeta(r))$ and variance $\mu$. Cauchy–Schwarz bounds its void probability by $1/(1+\mu)$. The sphere boundary is Haar-null. Replacing $2\zeta(r)$ by 4 gives the factor $F$ computed below after minimization with 1. [Part 87](wall1_selfdual_extend.md) · [Haar minimum law](wall1_haar_prefix_law.md)

In either case Markov gives the radius $\rho=\exp(([-\log 100-\log K_r-\log F]/n-U)/r)$. The table's gap is $0.85G_b-\rho$ in ambient length units. GSA enters only in the denominator and gap. Values round down independently.

| Width | Radius | Fraction of $0.85G_b$ | Gap |
|---:|---:|---:|---:|
| 342 | 0.05239528 | 0.27743375 | 0.13646164 |
| 350 | 0.05920614 | 0.28562828 | 0.14807774 |
| 360 | 0.06861038 | 0.29584806 | 0.16330049 |
| 370 | 0.07906974 | 0.30605490 | 0.17928176 |
| 380 | 0.09065411 | 0.31625418 | 0.19599542 |
| 390 | 0.10343611 | 0.32645560 | 0.21340976 |
| 400 | 0.11749235 | 0.33667485 | 0.23148636 |
| 406 | 0.12656786 | 0.34281389 | 0.24263498 |
| 410 | 0.13289600 | 0.34691120 | 0.25018762 |
| 420 | 0.14972721 | 0.35717917 | 0.26946635 |
| 430 | 0.16806442 | 0.36748326 | 0.28927456 |
| 440 | 0.18798957 | 0.37783204 | 0.30955841 |
| 450 | 0.20958673 | 0.38823410 | 0.33025954 |
| 460 | 0.23293942 | 0.39869314 | 0.35131798 |
| 470 | 0.25813771 | 0.40922098 | 0.37266501 |
| 480 | 0.28526834 | 0.41981999 | 0.39423322 |
| 490 | 0.31442239 | 0.43049664 | 0.41594891 |
| 500 | 0.34569456 | 0.44125919 | 0.43773287 |
| 506 | 0.36551260 | 0.44775852 | 0.45080374 |
| 510 | 0.37917692 | 0.45210959 | 0.45950673 |
| 511 | 0.38265187 | 0.45320138 | 0.46167889 |
| 512 | 0.38622783 | 0.45438568 | 0.46377216 |
| 520 | 0.39567471 | 0.44152634 | 0.50047727 |
| 530 | 0.40786648 | 0.42670874 | 0.54797631 |
| 540 | 0.42050162 | 0.41316181 | 0.59726335 |
| 550 | 0.43359961 | 0.40076647 | 0.64832624 |
| 560 | 0.44718481 | 0.38942135 | 0.70114668 |
| 570 | 0.46127791 | 0.37903287 | 0.75570863 |
| 580 | 0.47590452 | 0.36952136 | 0.81198993 |
| 590 | 0.49108790 | 0.36081348 | 0.86996961 |
| 600 | 0.50686672 | 0.35285408 | 0.92961012 |
| 610 | 0.52326130 | 0.34558030 | 0.99089128 |
| 620 | 0.54030681 | 0.33894504 | 1.05377700 |
| 630 | 0.55803721 | 0.33290438 | 1.11823152 |
| 640 | 0.57649404 | 0.32742234 | 1.18421059 |
| 647 | 0.58986376 | 0.32389679 | 1.23128348 |
| 650 | 0.59571365 | 0.32246266 | 1.25167433 |
| 660 | 0.61574217 | 0.31799699 | 1.32057230 |
| 670 | 0.63662819 | 0.31399988 | 1.39085088 |
| 680 | 0.65841982 | 0.31044710 | 1.46245621 |
| 690 | 0.68117914 | 0.30732210 | 1.53531985 |
| 700 | 0.70496360 | 0.30460662 | 1.60937738 |
| 710 | 0.72983984 | 0.30228691 | 1.68455460 |
| 720 | 0.75588887 | 0.30035502 | 1.76076246 |
| 730 | 0.78317837 | 0.29879724 | 1.83792471 |
| 740 | 0.81182124 | 0.29761672 | 1.91591942 |
| 750 | 0.84190137 | 0.29680421 | 1.99465328 |
| 760 | 0.87352881 | 0.29635907 | 2.07400637 |
| 770 | 0.90684221 | 0.29628859 | 2.15382983 |
| 780 | 0.94197157 | 0.29659477 | 2.23398313 |
| 790 | 0.97907446 | 0.29728630 | 2.31429781 |
| 800 | 1.01834742 | 0.29838066 | 2.39456618 |
| 810 | 1.05997638 | 0.29988858 | 2.47459088 |
| 820 | 1.10421069 | 0.30183533 | 2.55411087 |
| 830 | 1.15132748 | 0.30424878 | 2.63283713 |
| 840 | 1.20162443 | 0.30715709 | 2.71045986 |
| 850 | 1.25551240 | 0.31061137 | 2.78655591 |
| 860 | 1.31340942 | 0.31465659 | 2.86069478 |
| 870 | 1.37583233 | 0.31935354 | 2.93234702 |
| 880 | 1.44348934 | 0.32479704 | 3.00079163 |
| 890 | 1.51709593 | 0.33107044 | 3.06530026 |
| 900 | 1.59765240 | 0.33830562 | 3.12485962 |

## Compatibility of the tests

There is a useful implication at $r\le b$. Apply the terminal variant, then choose a shortest first vector inside $W$ and complete it inside $W$. This additional call has rank $k<b$ and preserves $W,P,q$ and both terminal tests. The first vector satisfies primal HSVP with factor $e^{H_k/k}$. If $v$ is that first vector, the dual of the projected shifted block $P/\mathbb Zv$ is $P^*\cap v^\perp$. Its named terminal normal still has length $1/q$, so it is within $c$ of the minimum of this sublattice as well. Hermite in rank $k$ gives shifted dual HSVP with factor $ce^{H_k/k}$. This proves both twin inequalities with a common factor $ce^{H_k/k}$, in the block layout $[1,k],[2,k+1]$. Definition 1 of generalized slide itself presumes $n\ge2b$. These are its two local tests with the stated factors.

Part 87's potential argument applies verbatim before that final call. After LLL initialization the covolume of any primitive rank-$k$ sublattice is at least $2^{-k(n-k)/2}$ times the starting prefix covolume by the pivot-minor bound. Each kernel replacement divides that covolume by more than $c$, and the terminal SVP step preserves it. Hence the number of calls, including the final primal call, is at most $2(1+\lceil k(n-k)\log 2/(2\log c)\rceil)+1$. This concerns exact arithmetic and oracle calls. The wide rows consequently hold for this common output predicate as well. The extra primal test used here has no separate shape probability factor: every $W$ admits that choice of first vector, and every such choice satisfies the shifted test by the dual intersection argument. For the predicate that includes the full terminal test, the set of eligible extensions is therefore exactly the original set.

At 406 and 506 the direct test on $P^*$ requires ranks 618 and 518. Part 88 tests a shifted block via capped DBKZ and gives a Hermite inequality there. A lower bound on the minimum of a sublattice does not give that lower bound on its superlattice $P^*$. Further, choosing an internally reduced basis of $W$ does not enforce Part 84's windows crossing its boundary. Thus neither implication supplies the missing width-budgeted narrow reducer. No narrow combined moment or improvement over the individual certificates is established here. The reported gaps describe the certificates, not an obstruction to larger minima on Haar inputs.

## Reproduction

Run this block from the repository root with Python and mpmath. It prints all 559 widths. The last assertions compare interval endpoints before display rounding.

```python
from pathlib import Path
def code(name):
    return Path('docs/research/wall1_'+name+'.md').read_text().split('\n```python\n',1)[1].split('\n```',1)[0]
exec(code('dual_pinning').split('def ceildiv')[0])
def floor8(x):
    t=int((10**8*x).a)
    return f'{t//10**8}.{t%10**8:08d}'
def row(b):
    k=n-b
    r=k+1
    K=A[n]-A[r]-A[b-1]-I.ln(2*n)
    if b<=511:
        a=(k-1)*I.mpf(C[b])/(M*b*(b-1))+I.ln(1+I.mpf('0.000001'))
        U=a*r*k/(k-1)
        F=I.mpf(1)
    else:
        H=I.mpf(C[r])/M
        U=H+r*I.ln(I.mpf(10001)/10000)
        h=I.exp(I.loggamma(1+I.mpf(r)/2)/r)/I.sqrt(I.pi)
        t=I.exp(H/r)/h
        F=I.mpf(1)
        for j in (500,900,950,975,990,995,998,999):
            f=I.mpf(j)/1000
            F=imin(F,f**(r*(b-1))+1/(1+(f*t)**r/4))
    R=I.exp(((-I.ln(100)-K-I.ln(F))/n-U)/r)
    S=(I.ln(b/(2*I.pi*I.exp(1)))+I.ln(I.pi*b)/b)/(2*(b-1))
    target=I.mpf('.85')*I.exp((2*b-n-1)*S)
    return R,R/target,target-R
rows={b:row(b) for b in range(342,901)}
for b,(radius,fraction,gap) in rows.items():
    print(b,*map(floor8,(radius,fraction,gap)))
for lo,hi,peak in ((342,511,511),(512,900,512)):
    assert all(rows[b][1]<rows[peak][1] for b in range(lo,hi+1) if b!=peak)
assert rows[511][1]<rows[512][1]<1
```

## Audit note (Nov 2026)

Independent audit: CORRECT WITH MINOR ISSUES. All 559 widths and all 62 table rows reproduce, and the peaks are confirmed. The
minimum on 512–900 is 0.29627102 at width 767, so 800 (0.29838066) is already on the rising branch. The factor c·e^{H_k/k} is
not Definition 1's twin factor; Definition 1 does not apply for n < 2b. The β = 512 maximum is for the terminal-variant scan only:
Part 87's MW certificate at 512 is slightly higher (0.38626645 vs 0.38622783). The no-gain conclusion at 647/800 is sound.
