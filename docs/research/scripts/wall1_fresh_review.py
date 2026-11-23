"""Outward interval checks for wall1_fresh_review.md. Run with python -B."""

from fractions import Fraction
from math import comb

from mpmath import iv

from wall1_hermite_budget import log_floors, log_theta

iv.dps = 60
I = iv.mpf
log, exp, sqrt = iv.ln, iv.exp, iv.sqrt


def report(label, value, lower, upper):
    assert I(lower) < value < I(upper), (label, value)
    print(label, value)


def crossing_tests():
    fraction = I(100) / 405
    p = I('.12')
    divergence = fraction * log(fraction/p) + (1-fraction)*log((1-fraction)/(1-p))
    entropy_bound = exp(-405*divergence)
    report("compensator crossing bound", entropy_bound, '1.9641e-11', '1.9642e-11')
    assert entropy_bound + I('7.6e-12') < I('2.72513e-11')
    p = I('.06')
    # If the total is at least 100, one of the three classes has at least 34.
    tail = 3*sum(comb(135, j)*p**j*(1-p)**(135-j) for j in range(34, 136))
    report("three-class crossing bound", tail, '1.9639e-12', '1.9640e-12')
    assert I('.3914')**3 < p
    volume_log = 253*log(iv.pi)-iv.loggamma(254)
    h = sqrt(I('56.2142'))*exp(volume_log/506)
    x = log(35)
    for _ in range(2):
        x = (505*x-log(h))/506
    b = sqrt(I('1.21')*exp(2*x)-2)
    report("two intermediate projections, inner radius", b, '37.89000', '37.89002')
    ratio = (b/sqrt((I('1.1')*35)**2-1))**505
    report("inner / reference ball volume", ratio, '.00037266', '.00037268')


def withheld_columns():
    n = 505
    log_det = log_floors()[405]
    report("incoming draw-406 log10 determinant floor", log_det/log(10),
           '388.94147', '388.94149')
    anchor = 3*(iv.pi/4 + 502*log_theta(I(1)) - log_det)/log(10)
    report("three prescribed anchors, log10", anchor, '-1111.59', '-1111.57')

    area = I(1352)/sqrt(3)
    winner = sqrt(sqrt(2)*area)
    line = I(52)/sqrt(3)
    min_s, min_t, min_u = area/line, area/winner, sqrt(3)*area/(2*winner)
    assert min_u > 20 and min_t > 20 and min_s > 20
    lift_x = sqrt(line**2 + winner**2/4)
    shift_x = winner/200
    shift_y = (winner+lift_x)/200
    step = I(1)/8
    assert winner + step < 36 and line + shift_x + step < 36
    assert winner + shift_y + step < 36
    radius_product = (winner*area*(1+step/min_s)*(1+(step+shift_x)/min_t)
                      *(1+(step+shift_y)/min_u))
    z_unit = sqrt(2*iv.pi/n)
    log_gaussians = (3*(I(n)/2+n*log(z_unit)+n*log_theta(20*z_unit)-log_det)
                     + n*log(radius_product))
    choices = 252*comb(510, 3)*289**3*101**2*151
    report("all free-coordinate triples and draws, log10",
           (log_gaussians + log(choices))/log(10), '-19.97', '-19.95')
    assert exp(log_gaussians)*choices < I('1.13e-20')

    final_floor = log_floors()[406]

    def log_ball(d, r, floor):
        z = r*sqrt(2*iv.pi/d)
        return I(d)/2 + d*(log(z)+log_theta(z))-floor

    short_line = 511*exp(log_ball(505, I(24), final_floor))
    min_u_plane = 12*sqrt(3)
    plane_product = area*(1+step/24)*(1+(step+line/200)/min_u_plane)
    log_pair = (2*(I(n)/2+n*log(z_unit)+n*log_theta(20*z_unit)-final_floor)
                + n*log(plane_product) + log(comb(511, 2)*289**2*101))
    assert area/24 + line/200 + step < 36
    plane_bound = short_line+exp(log_pair)
    report("terminal plane, log10", log(plane_bound)/log(10), '-40.63', '-40.62')
    assert plane_bound < I('2.39e-41')
    short_win = 407*512*exp(log_ball(506, I(13), final_floor))
    report("first use by small winner, log10", log(short_win)/log(10), '-190.06', '-190.05')
    t = I(505)/1921
    high_score = 512*I('5.26586e-8')*sum(exp(-t*j*j) for j in range(6, 31))
    report("visible score, heights 6 through 30", high_score, '2.1624e-9', '2.1625e-9')


if __name__ == '__main__':
    assert (I('5.283493e-8')+I('6.998082e-8')+I('5.2408e-7')
            < I('.005')*I('.00012938'))
    charges = ['.005', '.003546229', '.000623', '.000607731', '.00022304']
    assert sum(map(Fraction, charges)) == Fraction('.01')
    crossing_tests()
    withheld_columns()
