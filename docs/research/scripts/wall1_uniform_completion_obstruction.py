"""Barrier for improving only the uniform affine-slice cap; not a failure bound."""
from math import isqrt
from mpmath import iv


def main():
    iv.dps=80
    I=iv.mpf
    q=3329
    volume=[I(1),I(2)]
    for d in range(2,507):
        volume.append(2*iv.pi*volume[d-2]/d)
    R2=I('1.21')*iv.exp(2*(386*iv.log(q)-iv.log(volume[506]))/506)-2
    # Rounded downward snapshots of dominant TWO_TERM log bounds, not
    # lower bounds on actual incidence probabilities.
    cases=[(18,9,'10.832',7),(19,11,'39.947',6),(24,12,'212.809',10)]
    for h,r,logterm,k in cases:
        d=r-1
        b=min((q-1)//2,isqrt(int(R2.a)//d))
        assert I(d*b*b)<=R2.a
        assert b==(q-1)//2 or I(d*(b+1)**2)>R2.b
        cube=(2*b+1)**d
        M=min((I(q**d),volume[d]*(iv.sqrt(R2)+iv.sqrt(I(d))/2)**d),key=lambda v:v.b)
        # Any uniform replacement cap C is >= cube, hence this particular
        # existing numerical term A*M^k cannot fall below A*cube^k.
        floor=I(logterm)+k*iv.log10(I(cube)/M)
        required=iv.log10(M)+(-12-I(logterm))/k
        assert floor.a>-12
        print('size',h,'rank',r,'cube side',2*b+1,
              'log10 uniform cap lower',iv.log10(I(cube)),
              'log10 cap needed for this term <1e-12',required,
              'log10 term floor under uniform-only replacement',floor,flush=True)
    print('All three uniform-cap-only term obstructions certified; no actual probability lower bound.')

if __name__=='__main__':main()
