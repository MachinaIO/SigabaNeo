"""Draw-14 proper-subset envelope diagnostic; not a failure-probability bound."""
import contextlib, io, runpy, sys
from math import comb
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
with contextlib.redirect_stdout(io.StringIO()):
    s=runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
I,mu,q,eps,rho=[s[k] for k in ('I','mu','q','epsilon','rho_max')]
proper={}
for h in range(9,25):
    value=I(0)
    for r in range(3,h-1):
        for j in range(3,h):
            for t in range(2,min(j-1,r)+1):
                w=h-j-r+t
                if w<1 or r-t>h-j: continue
                for c in range(3,t+2):
                    count=comb(h,j)*comb(j,c)*comb(j-c,t-c+1)*comb(h-j,r-t)
                    value+=count*q**((t-1)*(j-t-1)+(r-1)*w)*mu**(r-c+1)*eps[c]*rho**w
    proper[h]=value
    print(h, s['iv'].log10(s['transfer']({h:value})), flush=True)
small = s['transfer']({h: value for h, value in proper.items() if h <= 21})
assert small < I('1.548e-31')
assert s['transfer']({22: proper[22]}) > I('360')
assert s['transfer']({24: proper[24]}) > I('1e74')
print('Combined proper-only envelope log10:', s['iv'].log10(s['transfer'](proper)))
print('Proper-only components through 21: < 1.548e-31.')
print('Not a bound for mixed terms containing full-incidence activities.')
