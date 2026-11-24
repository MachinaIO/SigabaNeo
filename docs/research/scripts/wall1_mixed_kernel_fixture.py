"""Exact fixed-chart mixed Gaussian certificates; toy q=5 only."""
from fractions import Fraction as F
from itertools import product, permutations


def main():
    q=5;n=2;m=1;R2=4;anchor=(0,1,2)
    center=lambda x:(x+2)%5-2
    codes={tuple(ts):[tuple(center(a+t*b) for t in ts)
                     for a,b in product(range(q),repeat=2)]
           for ts in [anchor,anchor+(3,),anchor+(4,),anchor+(3,4),anchor+(4,3)]}
    grid=[F(1,2),F(2,3),F(3,4),F(4,5),F(9,10),F(1)]
    scalar_anchor=lambda ta:sum(ta**sum(x*x for x in row) for row in codes[anchor])
    anchor_caps={ta:ta**(-len(anchor)*R2)*scalar_anchor(ta)**(n+m)/q**(2*m)
                 for ta in grid}
    # Full-rank input anchors have (y0,y1) distinct. Each fixed affine
    # restriction to that line has exactly q^(-2m) probability.
    actual={1:F(0),2:F(0)}
    for params in product(range(q),repeat=6):
        a=params[:3];b=params[3:]
        if b[0]==0 and b[1]==0:continue
        rows=[tuple(center(a[j]+t*b[j]) for j in range(3)) for t in range(q)]
        if not all(sum(x*x for x in rows[t])<=R2 for t in anchor):continue
        for k in (1,2):
            actual[k]+=F(sum(all(sum(x*x for x in rows[t][:n])<=R2 for t in ts)
                             for ts in permutations((3,4),k)),q**(2*m))
    for k in (1,2):
        charts=list(permutations((3,4),k))
        bound0=len(charts)*min(anchor_caps.values())
        candidates=[]
        for ta in grid:
            sa=scalar_anchor(ta)
            energy=sum(sum(ta**sum(x*x for x in row[:3])*sum(x*x for x in row[3:])
                           for row in codes[anchor+ts]) for ts in charts)/(len(charts)*sa)
            derivative=k*R2-n*energy
            if ta==F(3,4):assert derivative>0
            if ta==F(9,10):assert derivative<0
            print("boundary derivative",k,ta,float(derivative))

        for ta,tb in product(grid,grid+[F(19,20),F(49,50),F(99,100),F(999,1000)]):
            sa=scalar_anchor(ta)
            si=[]
            for ts in charts:
                si.append(sum(ta**sum(x*x for x in row[:3])*tb**sum(x*x for x in row[3:])
                              for row in codes[anchor+ts]))
            cap=ta**(-3*R2)*tb**(-k*R2)*sa**m*sum(x**n for x in si)/q**(2*m)
            assert cap>=actual[k]
            candidates.append((cap,ta,tb))
            if tb==1:
                assert cap==len(charts)*anchor_caps[ta]
        best,ta,tb=min(candidates)
        assert best<=bound0
        print('k',k,'exact mixed count',actual[k], 'best Gaussian upper',best,
              'anchor-only upper',bound0,'weights',ta,tb,
              'ratio',float(best/bound0))
    print('120 exact mixed-kernel upper bounds checked; boundary derivatives diagnostic only.')

if __name__=='__main__':main()
