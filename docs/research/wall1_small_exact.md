# Exact width-two reduction on a planted three-dimensional lattice

For one sample, one secret coordinate and fixed error and secret both equal to 1, the Part 8 terminal success probability is at most $11/q$ for **every selection of a fully exact BKZ-2 reduced basis** and every prime $q\ge5$. For the specified reducer at five enumerated primes it is exactly $5/q$. Every ambient-unique instance in these runs has its plant in the first row, so its projection vanishes.

## Proof

Write the scalar matrix as $a$, the plant as $p=(1,1,1)$, and the membership congruence as $x-t+a(y-t)\equiv0\pmod q$. Let $g_i$ denote the three successive Gram–Schmidt lengths, indexed from zero. In each projected adjacent pair, subtract the nearest integer multiple of the first vector from the second. The result has squared norm at most $g_{i+1}^2+g_i^2/4$, and exact block reducedness bounds it below by $g_i^2$. Hence $g_i\le(2/\sqrt3)g_{i+1}$. The last nonzero basis coefficient of any nonzero lattice vector gives a Gram–Schmidt component of length at least the corresponding $g_i$. Applying this to $p$ gives $g_0\le(4/3)\sqrt3<\sqrt6$.

When the first row differs from $\pm p$, it is primitive and has norm-square at most 5. For each such candidate $z$, membership either fixes one residue $a$, or is impossible: if $y=t$ modulo $q$, membership also forces $x=t$ modulo $q$, which in this ball implies $z\in\mathbb Z p$. In fact the exceptional matrices belong to an explicit set of at most eleven residues. Enumerate the integer triples in the ball of squared radius 5 and take the distinct rational values of $(t-x)/(y-t)$ for $y\ne t$. They are
$$
-3,-2,-3/2,-1,-2/3,-1/2,-1/3,0,1/2,1,2 .
$$
The enumeration can be checked by taking the signed coordinate permutations of $(1,0,0),(1,1,0),(1,1,1),(2,0,0),(2,1,0)$. All denominators are invertible for the stated primes. Outside their reductions modulo $q$, the first row must be the plant up to sign. Thus the strict terminal success probability is at most $\min(1,11/q)$.

## Exhaustive results

The columns count uniform residues, with denominator $q$. Ambient uniqueness is tested independently by enumerating the 27 points of the cube with coordinates in {−1,0,1}, which contains the closed ball of squared radius 3. Terminal success requires exactly the two shortest vectors $\pm\pi p$.

| q | Ambient unique and projection zero | Ambient nonunique and terminal success | All other outcomes |
|---:|---:|---:|---:|
| 5 | 0 | 5 | 0 |
| 11 | 6 | 5 | 0 |
| 31 | 26 | 5 | 0 |
| 101 | 96 | 5 | 0 |
| 1009 | 1004 | 5 | 0 |

A reproducible implementation (Python standard library) follows. It works on integer rows and rational orthogonal projections. Size reduction preserves prefix volumes. Each strict adjacent swap decreases the product of the two squared proper prefix volumes, a positive integer, so the loop terminates. At termination each projected pair is Gauss reduced: its first vector $x$ is no longer than its size-reduced partner $y$. Vectors with second coefficient of magnitude at least two have perpendicular height at least $\sqrt3\|x\|$, while for second coefficient one the centered representative is shortest. Thus the pair minimum equals $\|x\|$ and has one line precisely when $\|y\|>\|x\|$. This also proves the terminal classifier.

```python
from fractions import Fraction as F
from collections import Counter
from itertools import product

def dot(x,y): return sum(a*b for a,b in zip(x,y))
def sub(x,c,y): return tuple(a-c*b for a,b in zip(x,y))
def proj(x,y): return sub(x,F(dot(x,y),dot(y,y)),y)

def reduce2(B):
    while True:
        S=[]
        for i in range(3):
            for j in reversed(range(i)):
                mu=F(dot(B[i],S[j]),dot(S[j],S[j]))
                B[i]=sub(B[i],(mu+F(1,2))//1,B[j])
            v=B[i]
            for w in S: v=proj(v,w)
            S.append(v)
        for i in range(2):
            w=B[i+1] if i==0 else proj(B[2],S[0])
            if dot(w,w)<dot(S[i],S[i]):
                B[i:i+2]=B[i:i+2][::-1]
                break
        else: return B

def outcome(q,a):
    p=(1,1,1)
    b=(a+1)%q
    h,j,k=reduce2([(q,0,0),((-a)%q,1,0),(b,0,1)])
    v,x,y=[proj(z,h) for z in (p,j,k)]
    w=dot(v,v)
    if not w: return 'zero'
    if w!=dot(x,x): return 'long'
    return 'unique' if dot(y,y)>w else 'tie'

for q in (5,11,31,101,1009):
    C=Counter()
    for a in range(q):
        unique=not any(x*x+y*y+t*t<=3 and (x,y,t) not in [(0,0,0),(1,1,1),(-1,-1,-1)] and
                       (x+a*y-t*(a+1))%q==0 for x,y,t in product(range(-1,2),repeat=3))
        C[unique,outcome(q,a)]+=1
    print(q,sorted(C.items()))
```

## GSA comparison and scope

In dimension three a geometric progression of Gram–Schmidt lengths with product $q$ has middle length $q^{1/3}$, independently of its slope. The isotropic projected-plant estimate at width two is $\sqrt{2/3}\|p\|=\sqrt2$. The heuristic comparison therefore favors the plant for all five primes. It compares lengths before accounting for capture. Under the strict terminal event a zero projection fails the same-line leaf and satisfies the off-line leaf vacuously. At $q=1009$ this occurs on 1004 of 1009 matrices even though the algorithm has recovered the plant on all of them.

This is an obstruction to interpreting a terminal-only probability as overall recovery after convergence. The computation uses exact BKZ-2, dimension three and fixed planting. The registered leaves use the verified slide loop, divisible block shape and their own parameter hypotheses. Neither the table nor the bound refutes those leaves. The law before the first capture, and the probability for the registered slide output, remain open here.


## Independent audit (Nov 2026)

Verdict: **correct**. The eleven residues and the exact values 5/q (also at q = 7, 13) reproduce. Independent check over ALL
fully BKZ-2 reduced bases (not only the specified reducer): terminal success is possible exactly at 5 residues {0, 1, −1, −2, 1/2}
for q ∈ {5, 7, 11, 13, 17, 31, 101, 1009}, so the true maximum is 5/q and the proved 11/q bound is valid but not sharp; every
ambient-unique instance has b_0 = ±p (1004/1009 at q = 1009). Wording: the first row is always primitive (not only when ≠ ±p).
