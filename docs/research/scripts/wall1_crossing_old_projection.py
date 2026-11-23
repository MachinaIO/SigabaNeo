"""A crossing supported on an anchor basis cannot lose its whole old part."""
from itertools import product


def finite_checks():
    planes = [
        ((1,1,-1,-1,0,0), (0,0,1,1,-1,-1), (0,1,2,4)),
        ((1,1,-1,-1,0,0), (1,-1,0,0,1,-1), (0,1,3,5)),
        ((1,1,1,1,0,0,0), (1,0,0,0,1,1,1), (0,2,3,5,6)),
    ]
    checked = 0
    for q in (3,5):
        for a,b,basis in planes:
            complement = [i for i in range(len(a)) if i not in basis]
            i,j = complement
            assert (a[i]*b[j]-a[j]*b[i]) % q != 0
            for values in product(range(q), repeat=len(basis)):
                if not any(values):
                    continue
                old = [0]*len(a)
                for k,v in zip(basis,values):
                    old[k] = v
                for u,w in product(range(q), repeat=2):
                    assert any((v+u*x+w*y) % q for v,x,y in zip(old,a,b))
                    checked += 1
    print(f'Passed {checked} exact nonvanishing old-part checks.')


if __name__ == '__main__':
    finite_checks()
