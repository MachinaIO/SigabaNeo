# Screening a height-one covariance proof of the history drift

This investigates the missing selected-direction input in
[the projected void recursion](wall1_drift_recursion.md). The sector reduction
below is valid, but even its ideal covariance case cannot certify capture of
the critical shell using that recursion. It does not bound production drift.

Fix a complete incoming history. For every fresh uniform mark u choose a
nearest old representative y(u), with a fixed tie rule. Let E be the event
that the actual selected line is spanned by (y(u),1). This definition retains
ties explicitly: a height-one winner using a different nearest representative
need not belong to E. Write the actual winner as (a(u),k(u)), with length s(u),
and define positive semidefinite matrices

    A = E_u[a(u)a(u)^T/s(u)^2],
    B = E_u[y(u)y(u)^T/(1+||y(u)||^2)],
    B_bad = E_u[1_(E complement) y(u)y(u)^T/(1+||y(u)||^2)].

On E the integrands defining A and B agree. The remaining contribution to A
is positive semidefinite, so

    A >= B-B_bad >= B-epsilon I,  epsilon=Pr(E complement).

The second inequality follows pointwise from
yy^T/(1+||y||^2) <= I. Consequently

    lambda_min(A) >= max(0,lambda_min(B)-epsilon).

For any fixed positive semidefinite representative covariance C, a sharper
trace version is

    tr(C A) >= tr(C B)-lambda_max(C)*epsilon.

Indeed tr(C B_bad)<=lambda_max(C) tr(B_bad)<=lambda_max(C)epsilon.
The zero representative and either sign of the selected line cause no issue.
These are conditional identities/inequalities on the full history; replacing
epsilon or B by unconditioned input quantities would need a separate proof.

## Why this does not repair the existing radial kernel

Every actual A satisfies tr(A)<=1, independently of how well the height-one
sector is controlled. In retained dimension505 this forces
lambda_min(A)<=1/505. The already certified draw129 endpoint shell tests
require squared removed fractions greater than .02554 and .02606,
respectively. Each exceeds1/505 by more than a factor12. Thus obtaining
the most favorable possible minimum eigenvalue still leaves the critical
reference shell outside the capture range of the mean-projector recursion.
This is a limitation of that certificate, not an assertion about actual
BKZ capture or the other witness heights.

There is also a direct geometric reason why isotropic covariance alone
cannot supply the missing angular tail. In dimension d, let e be uniformly
distributed among sign vectors (sigma_1,...,sigma_d)/sqrt(d), and let the
test representatives be y_i=R times the i-th coordinate vector. Then

    E[e e^T]=I/d,
    ||projection_(e perpendicular) y_i||^2=R^2*(1-1/d)

for every direction outcome and every i. If the required removed fraction
theta=1-B_radius^2/R^2 exceeds1/d, none of these representatives is captured,
despite perfectly isotropic covariance. This example specifies vectors and
directions only; it is not a realizable selected q-ary lattice construction.
It shows why an angular-tail or joint multiple-height estimate is needed
in addition to a covariance estimate. It does not refute the production
transport inequality.

No new finite lattice experiment or production probability claim follows
from this screen. The next useful input must control joint capture under
the actual selection law, rather than only improve lambda_min(A).
