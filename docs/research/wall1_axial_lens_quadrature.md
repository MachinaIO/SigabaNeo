# Arithmetic axial spacing for the collision lens

This bounds one part of a lens-count approximation on actual projected integer
lattices. It does not bound the actual lens count: transverse affine-lattice
slice errors remain unbounded.

Let K=P_E Z^N, qK subset M subset K, with q prime. Assume lambda1(M)>r,
rho²=r²-2, and v in M satisfies r<||v||<=2rho. Write t=||v||.
Because t<2lambda1(M), v is primitive in M. Rationality of E lets us write
v=(a/b)u, where u is a primitive integer vector in E, a,b are positive
coprime integers. Both u and v belong to K, so Bezout gives u/b in K.
The lattice M contains a*u/b and q*u/b, hence gcd(a,q)*u/b. Primitivity of
v in M forces a=gcd(a,q), so a is either 1 or q.

The axial projection of K onto the unit direction u/||u|| is precisely the
grid of spacing Delta=1/||u||: <u,P_E z>=<u,z> ranges over all integers.
If a=1, t=||u||/b gives Delta<=1/t. If a=q, u is in K* and u/b is in K,
so ||u||²/b is a positive integer. Thus Delta<=t/q. In either case,

    Delta <= max(1/t,t/q).

## Axial sum with continuum transverse sections

Put d=505 and

    f(s)=V_(d-1)*(rho²-(t/2+s)²)_+^((d-1)/2), s>=0,
    ell(t)=2 integral_0^infinity f(s) ds.

The transverse section of the lens at centered axial position s has volume
f(|s|). Since t>rho, f is decreasing and convex: differentiating twice
reduces convexity on its support to (d-2)(t/2+s)²>=rho², which holds here.
It vanishes with zero derivative at the end of its support.

A decreasing convex f of this kind is a positive mixture of (L-s)_+.
The even triangular functions (L-|s|)_+ have nonnegative Fourier transforms.
Their periodized sums are maximal at shift zero, and the same holds for f.
The composite trapezoid remainder on the half-line is at most
Delta²*(-f'(0))/8: the local remainder is one half the integral of f''
times s(Delta-s), bounded by Delta²/8 times the integral of f''.
Doubling both halves therefore gives, at every axial shift theta,

    Delta sum_k f(|k*Delta+theta|)
      <=ell(t)+Delta²*(-f'(0))/4.

Let c=-f'(0)/f(0)=504t/[2(rho²-t²/4)]. Convexity gives the tangent
triangle lower bound ell(t)>=f(0)/c. Consequently the relative excess of
this axial continuum-section quadrature is at most (Delta*c)²/4.

On the central interval x=t²/(4rho²) in [2/5,3/5], the two arithmetic cases
above give

    (Delta*c)²/4 <= max((630/rho²)²/4,(1512/3329)²/4) < .064,

using the incoming-draw corridor g>32.18553, r=1.1g. Thus the axial sum of
continuum slice volumes is at most 1.064 times the exact lens volume there.
The bound is uniform in axial shift. It is not asserted for the entire
radial integral, nor for scalar floors outside this stated corridor.

## What is still missing

An actual axial slice contains a translated lattice of rank 504. Replacing
its point count by its volume divided by its covolume is an additional
approximation, not a consequence of the axial estimate. In particular the
result does NOT prove w(v)<=1.064*ell(t)/det(K), bound the discrete lens
error E, or control the selected distribution of radial differences in M.
Taking a supremum of shifted transverse Gaussian counts is also not free:
projecting K* perpendicular to u can introduce short dual vectors even
though K* lies in the ambient integer lattice.

Run `python3 docs/research/scripts/wall1_axial_lens_quadrature.py` for exact
rational verification of the two numerical constants. The arithmetic-grid
and quadrature deductions are paper arguments, independently checked by the
parent after the research agent's derivation. No production collision bound
or Lean formalization is claimed.
