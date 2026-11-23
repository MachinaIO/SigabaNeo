"""Interval bound for nullity-one corrections only; not the full draw-13 bound."""
from math import comb
from pathlib import Path
import runpy

s = runpy.run_path(str(Path(__file__).with_name('wall1_affine_void_moments.py')))
I, iv = s['I'], s['iv']
q, m, n, draw, k = 3329, 400, 506, 13, 12
N, inputs = 504+draw, 104+draw
R = iv.sqrt(I('1.21')*iv.exp(2*(I(400-draw)*iv.ln(q)-iv.ln(s['volume'][n]))/n)-2)
mu = s['candidate_lower'](N, R)/q**m
S = [[0]*(k+1) for _ in range(k+1)]
A = [[0]*(k+1) for _ in range(k+1)]
S[0][0] = A[0][0] = 1
for i in range(1, k+1):
    for j in range(1, i+1):
        S[i][j] = j*S[i-1][j]+S[i-1][j-1]
        A[i][j] = sum(comb(i-1,h-1)*A[i-h][j-1] for h in range(2,i+1))
independent = sum(A[k][b]*mu**(b-k) for b in range(1,k//2+1))/I('.280')
correction = I(0)
epsilon = {}
for j in range(3, k+1):
    beta = I((j-1)*N)/(2*j*R**2)
    Qj = (s['affine_triple_count_upper'](beta,R,N) if j == 3 else
          q**(j-2)*iv.exp(j*beta*R**2)*s['relation_theta_upper'](j,beta)**N)
    beta0 = I(N)/(2*R**2)
    T = iv.sqrt(iv.pi/beta0)
    Bj = ((q**(j-1)-1)//(q-1)*iv.exp(j*beta0*R**2)
          *(1+T)**(j*m+(j-2)*inputs)*s['relation_theta_upper'](2,beta0)**inputs)
    epsilon[j] = Qj/q**(m*(j-1))+Bj/q**(m*j)
    for b in range((k-j)//2+1):
        H = sum(comb(k,ell)*S[k-ell][j]*A[ell][b] for ell in range(k+1))
        correction += H*mu**(b-k)*(Qj/q**(m*(j-1))+Bj/q**(m*j))/I('.280')
assert independent < I('2.845e-13')
print('Draw 13, order 12: independent contribution / rho < 2.845e-13')
assert correction < I('2.468e-54')
print('Draw 13, order 12: nullity-one correction / rho < 2.468e-54')
print('UNBOUNDED HERE: supports of nullity at least two and later selected histories.')
