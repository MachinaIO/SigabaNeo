"""Two-relation full-incidence envelopes at draw 14; no complete exit certificate."""
import contextlib
from itertools import combinations, product
from fractions import Fraction as F
from math import comb
from pathlib import Path
import io
import runpy
from wall1_centered_affine_cancellation import rank
from wall1_full_incidence_reduction import density_errors
from wall1_short_relation_shapes import (
    equal_pair_sum_ball_bound, equal_pair_sum_alias_bound,
    pair_sum_ball_bound, orthogonal_pair_ball_bound, orthogonal_pair_alias_bound,
    shared_four_gaussian_bound, shared_four_ball_bound)


def witness_checks():
    tested = 0
    for points in (list(product(range(3), repeat=2)), list(product(range(2), repeat=3))):
        q = 3
        ranks = {mask: rank([(1, *p) for i, p in enumerate(points) if mask >> i & 1], q)
                 for mask in range(1 << len(points))}
        circuits = [mask for mask, r in ranks.items() if mask.bit_count() == r+1
                    and all(ranks[mask ^ (1 << i)] == r
                            for i in range(len(points)) if mask >> i & 1)]
        for support, r in ranks.items():
            h = support.bit_count()
            if r < 2 or h < r+2:
                continue
            sub = (support-1) & support
            while sub:
                if ranks[sub]+ranks[support ^ sub] == r:
                    break
                sub = (sub-1) & support
            if sub:
                continue
            contained = [c for c in circuits if c & support == c]
            girth = min(c.bit_count() for c in contained)
            for first in contained:
                if first.bit_count() != girth:
                    continue
                found = False
                for second in contained:
                    outside = second & ~first
                    overlap = second & first
                    t, a = outside.bit_count(), overlap.bit_count()
                    if ((1 if r == girth-1 else 2) <= t <= r-girth+2
                            and 1 <= a <= girth-1
                            and t+a >= girth and ranks[first | second] == girth+t-2
                            and (r == girth-1 or all(
                                ranks[first | (1 << i)] == girth
                                for i in range(len(points)) if outside >> i & 1))):
                        found = True
                        break
                assert found
                tested += 1
    print(f'Passed {tested} shortest-circuit two-relation witness checks.')


def fixed_position_checks():
    checked = 0
    q = 7
    for degree in (1, 2, 3):
        points = [(1, *(pow(t, j, q) for j in range(1, degree+1))) for t in range(q)]
        r = degree+1
        for size in range(r+2, q+1):
            for support in combinations(points, size):
                assert all(rank(list(basis), q) == r for basis in combinations(support, r))
                first = support[:r+1]
                second = support[:r]+(support[r+1],)
                assert rank(list(first), q) == rank(list(second), q) == r
                assert rank(list(support[:r+2]), q) == r
                checked += 1
    assert checked == 101
    print(f'Passed {checked} fixed-position witnesses on uniform moment-curve supports.')


def weighted_holder_checks():
    q = 5
    directions = [(1, a) for a in range(q)]+[(0, 1)]
    f = [F(1, 1+min(u, q-u)) for u in range(q)]
    checked = 0
    for size, heavy, light in ((7, 3, 1), (8, 3, 2), (9, 4, 1)):
        bound = sum((f[u]**heavy*f[v]**heavy*f[(u+v) % q]**light
                     for u, v in product(range(q), repeat=2)), F(0))/q**2
        for counts in product(range(heavy+1), repeat=len(directions)):
            if sum(counts) != size:
                continue
            columns = [d for d, count in zip(directions, counts) for _ in range(count)]
            actual = F(0)
            for u, v in product(range(q), repeat=2):
                value = F(1)
                for i, (a, b) in enumerate(columns):
                    value *= f[((i % 4)+1)*(a*u+b*v) % q]
                actual += value/q**2
            assert actual <= bound
            checked += 1
    print(f'Passed {checked} exact weighted three-direction Holder bounds.')


def group_holder_checks():
    q = 5
    f = [F(1, 1+min(u, q-u)) for u in range(q)]
    checked = 0
    for c in range(3, 8):
        for t in range(1, 7):
            for overlap in range(1, c):
                if t+overlap < c:
                    continue
                sizes = (c-overlap, t, overlap)
                bound = sum((f[u]**sizes[0]*f[v]**sizes[1]*f[(u+v) % q]**sizes[2]
                             for u, v in product(range(q), repeat=2)), F(0))/q**2
                for mode in range(3):
                    columns = ([(1, 0)]*sizes[0]+[(0, 1)]*sizes[1]
                               +[(1, 1+(mode*i) % 4) for i in range(overlap)])
                    for scaled in (False, True):
                        actual = F(0)
                        for u, v in product(range(q), repeat=2):
                            weight = F(1)
                            for i, (a, b) in enumerate(columns):
                                scale = 1+i % 4 if scaled else 1
                                weight *= f[scale*(a*u+b*v) % q]
                            actual += weight/q**2
                        assert actual <= bound
                        checked += 1
    print(f'Passed {checked} exact three-group Holder bounds.')


def draw14_bounds(*, exclude_triangular_anchors=False, exclude_double_short_anchors=False,
                  exclude_four_six_twenty=False, exclude_four_six_twenty_three=False,
                  exclude_three_circuit_twenty=False, exclude_four_six_twenty_four=False,
                  exclude_seven_four_six=False, exclude_five_twenty=False,
                  exclude_nine_twenty_seven=False, exclude_ten_twenty_eight=False,
                  exclude_five_fifteen=False, exclude_six_twenty_three=False,
                  exclude_eleven_thirty_one=False, exclude_six_ten_thirty_two=False,
                  exclude_six_d24=False):
    """With exclusion, bound only supports having no eligible triangular anchor.

    An eligible anchor has six positions, augmented rank four, and one of the
    five triangular balanced-sign codes in the c=4,t=2,a=2 classification.
    The default retains these anchors and bounds the full classes.
    The second exclusion restricts girth-four supports to those without an
    eligible two-circuit anchor having two independent balanced norm-four rows.
    The third exclusion restricts girth-four supports to those without an
    eight-position norm-four/norm-six anchor of Gram determinant twenty.
    Removed families must be covered separately before using a full bound.
    The fourth exclusion removes eligible nine-position determinant-23 anchors.
    The last exclusion removes six-position determinant-20 anchors from girth-three supports.
    exclude_four_six_twenty_four removes eight-position orthogonal norm-four/six anchors.
    exclude_seven_four_six removes seven-position norm-four/six determinant23 anchors.
    exclude_five_twenty removes five-position girth-three determinant20 anchors.
    exclude_nine_twenty_seven removes nine-position girth-six determinant27 anchors.
    exclude_ten_twenty_eight removes ten-position girth-four determinant28 anchors.
    exclude_six_ten_thirty_two removes ten-position girth-six determinant32 anchors.
    exclude_eleven_thirty_one removes eleven-position norm-four/eight determinant31 anchors.
    exclude_five_fifteen removes five-position girth-three two-four anchors.
    exclude_six_twenty_three removes six-position girth-three determinant23 anchors.
    exclude_six_d24 removes six-position girth-four determinant24 anchors.
    """
    with contextlib.redirect_stdout(io.StringIO()):
        s = runpy.run_path(str(Path(__file__).with_name('wall1_draw14_frontier.py')))
    I, iv, q, m, n, mu, radius = [s[k] for k in ('I', 'iv', 'q', 'm', 'N', 'mu', 'radius')]
    from wall1_triangular_third_relation import new_group_bound
    four_ball = (equal_pair_sum_ball_bound(radius**2, n, 2)
                 +equal_pair_sum_alias_bound(radius**2, n, 2, q))
    new_groups = {t: new_group_bound(radius**2, n, t, q) for t in range(4, 21)}
    s['first_ball_ratios'] = {}
    s['four_circuit_anchor_parts'] = {}
    s['five_circuit_anchor_parts'] = {}
    s['six_circuit_split_parts'] = {}
    s['three_circuit_anchor_parts'] = {}
    s['three_circuit_no_four_parts'] = {}
    s['six_circuit_anchor_parts'] = {}
    s['ten_position_rare_parts'] = {}
    s['nine_position_rare_parts'] = {}
    s['eleven_position_parts'] = {}
    s['twelve_six_parts'] = {}
    def theta(x):
        geometric = s['geometry']['theta_upper']
        return geometric(x) if x > iv.pi else iv.sqrt(iv.pi/x)*geometric(iv.pi**2/x)
    def moment(power, beta):
        scale = iv.sqrt(iv.pi/beta)
        a = iv.pi**2/beta
        delta = 2*iv.exp(-a/4)/(1-iv.exp(-2*a))
        return scale**power/q*(theta(a*power/q**2)**(1/power)
                              +I(q)**(1/power)*delta)**power
    anchors = {}
    for c in range(3, 24):
        for t in range(1, 25-c):
            union = c+t
            beta = I((union-2)*n)/(2*union*radius**2)
            power = min(I(union)/2, I(c))
            gaussian = theta(beta)**(union-2*power)*moment(power, beta)**2
            if union < 2*c:
                # Weighted three-direction Holder cover, followed by the
                # unequal-function Pollard rearrangement from Part 261.
                a = iv.pi**2/beta
                alpha = a/q**2
                delta = 2*iv.exp(-a/4)/(1-iv.exp(-2*a))
                heavy = max(I(union-c), I(union)/3)
                light = union-2*heavy
                pure = (theta((heavy+light)*alpha)
                        *theta(heavy*(heavy+2*light)/(heavy+light)*alpha)/q**2
                        +iv.exp(-heavy*a/8))
                eh = heavy*delta*(1+delta)**heavy
                el = light*delta*(1+delta)**light
                error = 2*eh+el+eh**2+2*eh*el+eh**2*el
                sharp = (iv.pi/beta)**(I(union)/2)*(pure+error)
                if sharp.b < gaussian.b:
                    gaussian = sharp
            for overlap in range(1, c):
                if t+overlap < c:
                    continue
                # Pick one column from each of the two exclusive groups and
                # the overlap. Holder retains their three different sizes.
                big, middle, small = sorted((c-overlap, t, overlap), reverse=True)
                a = iv.pi**2/beta
                alpha = a/q**2
                delta = 2*iv.exp(-a/4)/(1-iv.exp(-2*a))
                determinant = big*middle+big*small+middle*small
                pure = (theta((big+small)*alpha)
                        *theta(I(determinant)/(big+small)*alpha)/q**2
                        +iv.exp(-middle*a/8))
                e1, e2, e3 = [I(p)*delta*(1+delta)**p for p in (big, middle, small)]
                error = e1+e2+e3+e1*e2+e1*e3+e2*e3+e1*e2*e3
                grouped = (iv.pi/beta)**(I(union)/2)*(pure+error)
                chosen_gaussian = grouped if grouped.b < gaussian.b else gaussian
                # All short code words lie in a real plane. Full coordinate
                # support restricts pairs of norm-four generators.
                cutoff = 14
                assert cutoff**3 < q and union*cutoff**2 < q**2
                if c >= 5:
                    minimum_sq = 2*((c+1)//2)
                    lengths = (I(minimum_sq), I(3)*minimum_sq/4)
                else:
                    second_height = {4: I(5), 5: I(15)/4, 6: I(3),
                                     7: I(15)/4, 8: I(4)}.get(union, I(5))
                    lengths = (I(4), second_height)
                short_plane = theta(lengths[0]*alpha)*theta(lengths[1]*alpha)
                tail_plane = iv.exp(-alpha*cutoff**2/2)*theta(power*alpha/2)**2
                periodic_plane = sum((comb(union, j)*delta**j for j in range(1, union+1)), I(0))
                plane = (iv.pi/beta)**(I(union)/2)*((short_plane+tail_plane)/q**2
                                                 +periodic_plane)
                if plane.b < chosen_gaussian.b:
                    chosen_gaussian = plane
                power_bound = chosen_gaussian**n
                if c <= 4:
                    # Split codes by the number of independent norm-four words.
                    coefficient_count = q**(c+t+overlap-4)
                    short_lines = 3*comb(union, 4)
                    # A direction independent of the first circuit is nonzero
                    # on all t new positions and at least one old position.
                    # Thus it cannot be a norm-four direction when t >= 4.
                    one_count = short_lines*q**(c-2) if t <= 3 else 0
                    if c == 4:
                        one_count += 3*q**(t+overlap-2)
                    one_count = min(coefficient_count, one_count)
                    bad_count = short_lines**2
                    if c == 3 and (union != 5 or overlap == 1):
                        bad_count = 0
                    elif c == 3:
                        # Exact full-support five-point codes with prescribed
                        # first three-support and second four-support circuits.
                        bad_count = 6
                    if c==3 and union==5 and exclude_five_fifteen:
                        bad_count=0
                    if c == 4:
                        if union == 6:
                            bad_count = 9
                        if union == 5:
                            bad_count = 0
                        if union == 6 and overlap == 3:
                            bad_count = 0
                        if union == 7:
                            # Exactly two weight-four directions; the second
                            # shares one coordinate with the first. For either
                            # prescribed four- or six-circuit, its support fixes
                            # this shared coordinate. Three balanced sign rows
                            # on each four-support give 3*3 codes.
                            bad_count = 0 if overlap == 2 else 9
                        if union >= 8:
                            bad_count = 0
                    large_cutoff = 40
                    if c == 4 and exclude_double_short_anchors:
                        bad_count = 0
                    assert 2*large_cutoff**2 < q and union*large_cutoff**2 < q**2
                    half_sum = theta(power*alpha/2)**2
                    # Every direction outside the first circuit has support
                    # at least t+1. Short affine integer rows have even norm
                    # squared, so the second minimum is at least external_sq.
                    external_sq = 2*((t+2)//2)
                    one_height = max(5, external_sq-1) if t >= 4 else 5
                    if c == 4 and t >= 4:
                        # Old projection is nonzero, hence at least 3/4.
                        one_height = max(I(one_height), I(t)+I(3)/4)
                        # For even t, height < t+2 forces all new entries to
                        # be +/-1. Old parity excludes singleton 0/1 patterns;
                        # a 2+2 pattern cannot give a three-position overlap.
                        if t % 2 == 0 and overlap == 3:
                            one_height = max(one_height, I(t+2))
                    one_short = theta(4*alpha)*theta(one_height*alpha)
                    one_tail = iv.exp(-alpha*large_cutoff**2/2)*half_sum
                    one_bound = (iv.pi/beta)**(I(union)/2)*(
                        (one_short+one_tail)/q**2+periodic_plane)
                    # A Gauss-reduced second height is >= 3/4 of its norm
                    # squared. Two independent rows cannot both lie on C.
                    no_height = I(3)*max(6, external_sq)/4
                    no_short = theta(6*alpha)*theta(no_height*alpha)
                    no_tail = iv.exp(-alpha*cutoff**2/2)*half_sum
                    none_bound = (iv.pi/beta)**(I(union)/2)*(
                        (no_short+no_tail)/q**2+periodic_plane)
                    none_power = none_bound**n
                    if c in (3, 4):
                        # Girth three also permits the (2,-1,-1) shape.
                        # Retain short first-three-circuit rows explicitly.
                        six_lines = 10*comb(union, 6)
                        if c == 3:
                            six_lines += 3*comb(union,3)
                        six_count = six_lines*q**(c-2) if t <= 5 else 0
                        if c == 3:
                            six_count += 3*q**(t+overlap-2)
                        six_count = min(coefficient_count,six_count)
                        allowed_pair = union <= 8 if c == 3 else union == 7
                        six_pair_count = min(coefficient_count, six_lines**2) if allowed_pair else 0
                        assert 6*36**4 < q**2
                        def no_four_plane(first, second, tail):
                            return (iv.pi/beta)**(I(union)/2)*(
                                (theta(I(first)*alpha)*theta(I(second)*alpha)+tail)/q**2
                                +periodic_plane)
                        six_tail = iv.exp(-648*alpha)*half_sum
                        only_six_height=I(13)/2
                        if c==3 and t>=6:
                            # The norm-six line is on C, of shape(2,-1,-1).
                            # Its projected integer minimum is1/3; every
                            # independent row is nonzero on all t new positions.
                            only_six_height=I(max(39,6*t+2))/6
                        only_six = no_four_plane(6, only_six_height, six_tail)
                        two_six_height=I(35)/6 if c==4 and union==7 else I(9)/2
                        two_six = no_four_plane(6, two_six_height, six_tail)
                        no_six = no_four_plane(8, 6, no_tail)
                        no_six_power = no_six**n
                        if c==3 and union==7:
                            # Proportional new parts and full old difference:
                            # no(8,8); Gram(8,10)>=76; Gram(10,10)>=91.
                            refined_seven=(no_four_plane(8,I(19)/2,no_tail)**n
                                +no_four_plane(10,I(91)/10,no_tail)**n
                                +no_four_plane(12,9,no_tail)**n)
                            no_six_power=min((no_six_power,refined_seven),key=lambda v:v.b)
                        if c==3 and t>=8:
                            # A norm-eight row neither fits the three-circuit
                            # nor covers t new positions plus a proper old part.
                            no_eight=no_four_plane(10,I(15)/2,no_tail)
                            no_six_power=min((no_six_power,no_eight**n),key=lambda v:v.b)
                        if c==4 and union==10:
                            # Norm-eight rows are unit on six new and two old
                            # positions. Proportional new parts and a full C
                            # difference force disjoint old supports: dot=6,
                            # contradicting Gauss reduction. Thus no(8,8) pair.
                            refined_ten_four=(no_four_plane(8,8,no_tail)**n
                                +no_four_plane(10,I(15)/2,no_tail)**n)
                            no_six_power=min((no_six_power,refined_ten_four),key=lambda v:v.b)
                        if c==3 and union==10:
                            # New parts are proportional on seven coordinates;
                            # reduced (8,8),(8,10),(10,10) pairs are impossible.
                            refined_ten=(no_four_plane(8,10,no_tail)**n
                                +no_four_plane(10,I(19)/2,no_tail)**n
                                +no_four_plane(12,9,no_tail)**n)
                            no_six_power=min((no_six_power,refined_ten),key=lambda v:v.b)
                        if union == 11:
                            # Two norm-eight rows covering eleven positions
                            # have |dot|<=3 when Gauss reduced, including the
                            # support-five shape with a coefficient +/-2.
                            # At c=4 the seven new entries are proportional.
                            # Reduced(8,8) is impossible; a norm-ten partner must
                            # lie on C, where its dot product has absolute value<=2.
                            eight_height=I(19)/2 if c==4 else I(55)/8
                            ten_power=no_four_plane(10,I(15)/2,no_tail)**n
                            if c==4:
                                ten_pairs={1:(),2:((75,70),(84,140),(91,140),(100,140)),
                                    3:((75,210),(84,420),(91,420),(96,1344),(99,1344),(100,420))}
                                # Every reduced(10,10) plane contains a norm-ten
                                # row on C, even when the initial pair is outside C.
                                ten_split=(sum((I(count)/coefficient_count
                                    *no_four_plane(10,I(det)/10,no_tail)**n
                                    for det,count in ten_pairs[overlap]),I(0))
                                    +no_four_plane(10,I(19)/2,no_tail)**n
                                    +no_four_plane(12,9,no_tail)**n)
                                ten_power=min((ten_power,ten_split),key=lambda v:v.b)
                            refined_no_six = (
                                no_four_plane(8,eight_height,no_tail)**n
                                +ten_power)
                            no_six_power=min((no_six_power,refined_no_six),key=lambda v:v.b)
                        if c==4 and union==13:
                            # No norm-eight row fits C or covers nine new positions.
                            # Two norm-ten rows outside C cannot have full C
                            # difference. If one lies on C, |dot|<=2.
                            refined_thirteen=(no_four_plane(10,I(19)/2,no_tail)**n
                                +no_four_plane(12,9,no_tail)**n)
                            no_six_power=min((no_six_power,refined_thirteen),key=lambda v:v.b)
                        if c==4 and union==12:
                            # Proper crossing excludes reduced (8,8)/(8,10)
                            # pairs; eligible (10,10) pairs have Gram >=84.
                            refined_twelve = (
                                no_four_plane(8,10,no_tail)**n
                                +no_four_plane(10,I(42)/5,no_tail)**n
                                +no_four_plane(12,9,no_tail)**n)
                            no_six_power=min((no_six_power,refined_twelve),key=lambda v:v.b)
                        two_six_term=I(six_pair_count)/coefficient_count*two_six**n
                        if c==3 and union==5 and overlap==2:
                            # Prescribed C=012, S=0134: eight saturated planes.
                            # See wall1_three_five_six_pairs.py and its counting proof.
                            exact_two_six=sum((I(4)/coefficient_count
                                *no_four_plane(6,I(det)/6,six_tail)**n
                                for det in (32,35)),I(0))
                            two_six_term=min((two_six_term,exact_two_six),key=lambda v:v.b)
                        if c==3 and union==6:
                            # Saturated support-three/unit-six pairs; the
                            # determinant20 planes have a norm-four vector.
                            # See wall1_three_six_six_pairs.py.
                            six_pairs={1:((36,1),),2:((32,18),(36,1))}
                            exact_two_six=sum((I(count)/coefficient_count
                                *no_four_plane(6,I(det)/6,six_tail)**n
                                for det,count in six_pairs[overlap]),I(0))
                            two_six_term=min((two_six_term,exact_two_six),key=lambda v:v.b)
                        if c==3 and union==7:
                            six_pairs={1:((32,4),),2:((27,18),(32,4),(35,24),(36,18))}
                            # Weight1/8 on the coefficient-two old entry,
                            # 23/16 on the other old entries, and1 on new ones.
                            scaled_alpha=alpha*I(16)/23
                            scaled_a=a*I(16)/23
                            wdelta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                            wperiodic=sum((comb(union,j)*wdelta**j
                                           for j in range(1,union+1)),I(0))
                            wprefactor=1/iv.sqrt(I(1)/8*(I(23)/16)**2)
                            weighted_d27=wprefactor*(iv.pi/beta)**(I(union)/2)*(
                                (theta(I(768)/23*alpha)*theta(I(100)/23*alpha)
                                 +iv.exp(-648*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                                +wperiodic)
                            def seven_six_kernel(det):
                                old=no_four_plane(6,I(det)/6,six_tail)
                                return min((old,weighted_d27),key=lambda v:v.b) if det==27 else old
                            exact_two_six=sum((I(count)/coefficient_count
                                *seven_six_kernel(det)**n
                                for det,count in six_pairs[overlap]),I(0))
                            two_six_term=min((two_six_term,exact_two_six),key=lambda v:v.b)
                        if c==3 and union==8:
                            from wall1_three_six_pair_codes import COUNTS as THREE_COUNTS
                            exact_two_six=sum((I(count)/coefficient_count
                                *no_four_plane(6,I(det)/6,six_tail)**n
                                for det,count in THREE_COUNTS[overlap]),I(0))
                            two_six_term=min((two_six_term,exact_two_six),key=lambda v:v.b)
                        one_six_term=I(six_count)/coefficient_count*only_six**n
                        if c==3 and union==10:
                            # Only C can carry norm six. Norm-eight independent
                            # rows are unit on seven new and one old positions.
                            exact_eight=(sum((I(count)/coefficient_count
                                *no_four_plane(6,I(det)/6,six_tail)**n
                                for det,count in ((44,35),(47,70))),I(0))
                                +I(six_count)/coefficient_count
                                    *no_four_plane(6,I(17)/2,six_tail)**n)
                            one_six_term=min((one_six_term,exact_eight),key=lambda v:v.b)
                        refined_none = (one_six_term
                                        +two_six_term
                                        +no_six_power)
                        if refined_none.b < none_power.b:
                            none_power = refined_none
                        if c==3:
                            s['three_circuit_no_four_parts'][t,overlap]={
                                'one-six':one_six_term,'two-six':two_six_term,
                                'no-six':no_six_power,'selected':none_power}
                    bad_bound = (iv.pi/beta)**(I(union)/2)*(
                        (short_plane+one_tail)/q**2+periodic_plane)
                    if chosen_gaussian.b < bad_bound.b:
                        bad_bound = chosen_gaussian
                    one_power = I(one_count)/coefficient_count*one_bound**n
                    def fixed_four_plane(height):
                        return (iv.pi/beta)**(I(union)/2)*(
                            (theta(4*alpha)*theta(max(one_height, I(height))*alpha)
                             +one_tail)/q**2+periodic_plane)
                    # Without locating the unique norm-four line on C, count
                    # all pairs of independent short integer lines. Each pair
                    # fixes the code and its two prescribed proper supports.
                    all_six = 10*comb(union,6)+(3*comb(union,3) if c == 3 else 0)
                    all_eight = 35*comb(union,8)+20*comb(union,5)
                    rare_six_count = short_lines*all_six
                    rare_six_height = I(5)
                    if c == 4 and union == 7:
                        # Unique weight-four direction is C; a balanced six-row
                        # overlaps it in three positions. Excluding a second
                        # norm-four row forces dot product +/-1.
                        rare_six_count = {1:0,2:14,3:42}[overlap]
                        if exclude_seven_four_six:
                            rare_six_count=0
                        rare_six_height = I(23)/4
                    general_rare = (
                        I(min(one_count,rare_six_count))/coefficient_count
                        *fixed_four_plane(rare_six_height)**n
                        +I(min(one_count,short_lines*all_eight))/coefficient_count
                        *fixed_four_plane(7)**n
                        +I(one_count)/coefficient_count*fixed_four_plane(9)**n)
                    if general_rare.b < one_power.b:
                        one_power = general_rare
                    if c==4 and union==7:
                        # A norm-four/eight pair covering seven positions has
                        # a unique four-support direction, necessarily C.
                        seven_counts={1:(),2:((28,18),(31,10),(32,18)),
                                      3:((31,30),(32,54))}[overlap]
                        scaled_alpha=alpha*I(5)/7
                        scaled_a=a*I(5)/7
                        wdelta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                        wperiodic=sum((comb(union,j)*wdelta**j
                                       for j in range(1,union+1)),I(0))
                        weighted_d28=iv.sqrt(I(125)/49)*(iv.pi/beta)**(I(union)/2)*(
                            (theta(4*alpha)*theta(I(157)/7*alpha)
                             +iv.exp(-800*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                            +wperiodic)
                        def seven_eight_kernel(det):
                            old=fixed_four_plane(I(det)/4)
                            return min((old,weighted_d28),key=lambda v:v.b) if det==28 else old
                        seven_split=(I(rare_six_count)/coefficient_count
                            *fixed_four_plane(I(23)/4)**n
                            +sum((I(count)/coefficient_count*seven_eight_kernel(det)**n
                                  for det,count in seven_counts),I(0))
                            +I(one_count)/coefficient_count*fixed_four_plane(9)**n)
                        one_power=min((one_power,seven_split),key=lambda v:v.b)
                    if c==4 and union==12:
                        # An independent row has all eight new entries nonzero.
                        # Norm ten forces a unit row on these and two old entries.
                        twelve_counts={1:(),2:((36,196),(40,182)),3:((40,546),)}
                        ten_split=(sum((I(count)/coefficient_count
                            *fixed_four_plane(I(det)/4)**n
                            for det,count in twelve_counts[overlap]),I(0))
                            +I(one_count)/coefficient_count*fixed_four_plane(11)**n)
                        one_power=min((one_power,ten_split),key=lambda v:v.b)
                    if c==3 and union==6:
                        # Exact prescribed three-support and crossing support:
                        # all eligible norm-eight planes already occur at six.
                        count20=0 if exclude_three_circuit_twenty else 3
                        count23=0 if exclude_six_twenty_three else 6
                        six_position_split=(I(count20)/coefficient_count*fixed_four_plane(5)**n
                            +I(count23)/coefficient_count*fixed_four_plane(I(23)/4)**n
                            +I(one_count)/coefficient_count*fixed_four_plane(9)**n)
                        if six_position_split.b<one_power.b:
                            one_power=six_position_split
                    if c==3 and union==5:
                        counts={1:((20,1),),2:((20,1),(23,6),(24,6),(31,12))}[overlap]
                        if exclude_five_twenty:
                            counts=tuple((det,count) for det,count in counts if det!=20)
                        # D23 norm-four/six pairs: weights3/20 on the two
                        # shared positions,47/30 on the three exclusive ones.
                        # Total weight5 preserves the ball Markov factor.
                        scaled_alpha=alpha*I(30)/47
                        scaled_a=a*I(30)/47
                        wdelta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                        wperiodic=sum((comb(union,j)*wdelta**j
                                       for j in range(1,union+1)),I(0))
                        wprefactor=iv.sqrt(I(1200000)/103823)
                        weighted_d23=wprefactor*(iv.pi/beta)**(I(union)/2)*(
                            (theta(I(2060)/141*alpha)*theta(I(149730)/4841*alpha)
                             +iv.exp(-800*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                            +wperiodic)
                        def five_position_kernel(det):
                            old=fixed_four_plane(I(det)/4)
                            return min((old,weighted_d23),key=lambda v:v.b) if det==23 else old
                        five_position_split=(sum((I(count)/coefficient_count
                            *five_position_kernel(det)**n for det,count in counts),I(0))
                            +I(one_count)/coefficient_count*fixed_four_plane(9)**n)
                        if five_position_split.b<one_power.b:
                            one_power=five_position_split
                    if c==4 and union==6:
                        # One norm-four line, exact prescribed supports, and
                        # no relation on <=3 positions. Unit minors certify D/4.
                        counts={2:((24,12),(31,24),(32,8)),
                                3:((28,36),(31,72),(32,24))}[overlap]
                        if exclude_six_d24:
                            counts=tuple((det,count) for det,count in counts if det!=24)
                        # D24 has four old unit entries and two new unit entries
                        # in the second row, orthogonal to the norm-four row.
                        # Weights5/6(old),4/3(new) preserve the total weight6.
                        scaled_alpha=alpha*I(3)/4
                        scaled_a=a*I(3)/4
                        weighted_delta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                        weighted_periodic=sum((comb(union,j)*weighted_delta**j
                            for j in range(1,union+1)),I(0))
                        weighted_d24=I(27)/25*(iv.pi/beta)**(I(union)/2)*(
                            (theta(I(24)/5*alpha)*theta(I(63)/10*alpha)
                             +iv.exp(-800*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                            +weighted_periodic)
                        def six_position_kernel(det):
                            old=fixed_four_plane(I(det)/4)
                            return min((old,weighted_d24),key=lambda v:v.b) if det==24 else old
                        four_six_split=(sum((I(count)/coefficient_count
                            *six_position_kernel(det)**n for det,count in counts),I(0))
                            +I(one_count)/coefficient_count*fixed_four_plane(9)**n)
                        if four_six_split.b<one_power.b:
                            one_power=four_six_split
                    if c == 4 and t >= 4:
                        # The first circuit is the unique norm-four line.
                        # Enumerate rare independent norm-six/eight witnesses;
                        # all other codes have second squared minimum >=10.
                        six_witnesses = 10*comb(union, 6) if t <= 5 else 0
                        eight_witnesses = (35*comb(union, 8)+20*comb(union, 5)) if t <= 7 else 0
                        six_pair_count = 3*six_witnesses
                        eight_pair_count = 3*eight_witnesses
                        if union == 8:
                            six_pair_count = {1:0,2:30,3:42}[overlap]
                            eight_pair_count = {1:60,2:13,3:60}[overlap]
                        rare_split = (
                            I(min(one_count, six_pair_count))/coefficient_count
                            *fixed_four_plane(5)**n
                            +I(min(one_count, eight_pair_count))/coefficient_count
                            *fixed_four_plane(7)**n
                            +I(one_count)/coefficient_count*fixed_four_plane(9)**n)
                        if union in (8,9,10,11):
                            # A unit old/new minor makes each short pair a
                            # primitive plane basis. Its second height is D/4.
                            eight_counts = {
                                1: ((28,12),(31,48)),
                                2: ((20,16),(24,14),(32,13)),
                                3: ((24,42),(28,12),(31,48)),
                            }
                            nine_counts = {
                                1: ((23,30),),
                                2: ((31,50),),
                                3: ((23,30),(31,150)),
                            }
                            ten_counts={1:(),2:((28,55),(32,50)),3:((32,150),)}
                            eleven_counts={1:((31,105),),2:(),3:((31,105),)}
                            determinant_counts={8:eight_counts,9:nine_counts,10:ten_counts,
                                                11:eleven_counts}[union][overlap]
                            if exclude_four_six_twenty:
                                determinant_counts = tuple((det,count) for det,count in determinant_counts if det!=20)
                            if exclude_four_six_twenty_three:
                                determinant_counts = tuple((det,count) for det,count in determinant_counts if det!=23)
                            if exclude_four_six_twenty_four:
                                determinant_counts = tuple((det,count) for det,count in determinant_counts if det!=24)
                            if union==10 and exclude_ten_twenty_eight:
                                determinant_counts=tuple((det,count) for det,count in determinant_counts if det!=28)
                            if union==11 and exclude_eleven_thirty_one:
                                determinant_counts=tuple((det,count) for det,count in determinant_counts if det!=31)
                            if union==8:
                                scaled_alpha=alpha*I(16)/21
                                scaled_a=a*I(16)/21
                                wdelta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                                wperiodic=sum((comb(union,j)*wdelta**j
                                               for j in range(1,union+1)),I(0))
                                wprefactor=1/iv.sqrt(I(1)/8*(I(7)/8)**3*(I(21)/16)**4)
                                weighted_d28=wprefactor*(iv.pi/beta)**(I(union)/2)*(
                                    (theta(I(80)/7*alpha)*theta(I(1328)/105*alpha)
                                     +iv.exp(-800*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                                    +wperiodic)
                            if union==10:
                                # D32: orthogonal unit rows on 4 and 8 positions,
                                # sharing two. Weights5/8(shared),1(old-only),9/8(new).
                                scaled_alpha=alpha*I(8)/9
                                scaled_a=a*I(8)/9
                                wdelta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                                wperiodic=sum((comb(union,j)*wdelta**j
                                               for j in range(1,union+1)),I(0))
                                wprefactor=1/iv.sqrt((I(5)/8)**2*(I(9)/8)**6)
                                weighted_d32=wprefactor*(iv.pi/beta)**(I(union)/2)*(
                                    (theta(I(26)/5*alpha)*theta(I(128)/15*alpha)
                                     +iv.exp(-800*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                                    +wperiodic)
                            if union==9:
                                # Shared signs: two agree, one disagrees. These
                                # weights make the two short rows orthogonal.
                                scaled_alpha=alpha*I(6)/7
                                scaled_a=a*I(6)/7
                                wdelta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                                wperiodic=sum((comb(union,j)*wdelta**j
                                               for j in range(1,union+1)),I(0))
                                wprefactor=1/iv.sqrt((I(5)/6)**2*(I(5)/12)*(I(13)/12)*(I(7)/6)**5)
                                weighted_nine_d31=wprefactor*(iv.pi/beta)**(I(union)/2)*(
                                    (theta(I(372)/65*alpha)*theta(I(318)/35*alpha)
                                     +iv.exp(-800*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                                    +wperiodic)
                            def short_pair_kernel(det):
                                old=fixed_four_plane(I(det)/4)
                                if union==9 and det==31:
                                    return min((old,weighted_nine_d31),key=lambda v:v.b)
                                if union==8 and det==28:
                                    return min((old,weighted_d28),key=lambda v:v.b)
                                if union==10 and det==32:
                                    return min((old,weighted_d32),key=lambda v:v.b)
                                return old
                            refined_pair_split = (
                                sum((I(count)/coefficient_count*short_pair_kernel(det)**n
                                     for det,count in determinant_counts),I(0))
                                +I(one_count)/coefficient_count*fixed_four_plane(9)**n)
                            if union==9:
                                s['nine_position_rare_parts'][overlap]={
                                    'short':sum((I(count)/coefficient_count*short_pair_kernel(det)**n
                                                 for det,count in determinant_counts),I(0)),
                                    'remaining':I(one_count)/coefficient_count*fixed_four_plane(9)**n}
                            if refined_pair_split.b < rare_split.b:
                                rare_split = refined_pair_split
                            if union==9:
                                # Three norm-four lines on C; every balanced
                                # norm-ten line has support7 or4 at this union.
                                ten_witnesses=3*(105*comb(union,7)+12*comb(union,4))
                                short_part=sum((I(count)/coefficient_count*short_pair_kernel(det)**n
                                                for det,count in determinant_counts),I(0))
                                ten_part=I(min(one_count,ten_witnesses))/coefficient_count*fixed_four_plane(9)**n
                                remainder=I(one_count)/coefficient_count*fixed_four_plane(11)**n
                                ten_split=short_part+ten_part+remainder
                                rare_split=min((rare_split,ten_split),key=lambda v:v.b)
                                s['nine_position_rare_parts'][overlap].update({
                                    'norm-ten':ten_part,'higher':remainder,'new-split':ten_split})
                            if union==10:
                                ten_counts={1:((36,45),(39,270)),2:((40,46),),
                                            3:((36,45),(39,270))}
                                ten_split=(sum((I(count)/coefficient_count
                                    *short_pair_kernel(det)**n
                                    for det,count in determinant_counts+ten_counts[overlap]),I(0))
                                    +I(one_count)/coefficient_count*fixed_four_plane(11)**n)
                                rare_split=min((rare_split,ten_split),key=lambda v:v.b)
                                s['ten_position_rare_parts'][overlap]={
                                    'norm-eight':sum((I(count)/coefficient_count*short_pair_kernel(det)**n
                                                     for det,count in determinant_counts),I(0)),
                                    'norm-ten':sum((I(count)/coefficient_count*short_pair_kernel(det)**n
                                                   for det,count in ten_counts[overlap]),I(0)),
                                    'remaining':I(one_count)/coefficient_count*fixed_four_plane(11)**n,
                                    'sum':ten_split}
                            if union==11:
                                # A norm-ten row covering seven new coordinates
                                # and meeting C is unit on ten positions. Dot +/-3
                                # gives a norm-eight row already covered above.
                                # Remaining norm-ten pairs have determinant39.
                                # 3 first lines * 4 old triples * 126 balanced lines.
                                scaled_alpha=alpha*I(72)/77
                                scaled_a=a*I(72)/77
                                wdelta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                                wperiodic=sum((comb(union,j)*wdelta**j
                                               for j in range(1,union+1)),I(0))
                                wprefactor=1/iv.sqrt(I(55)/72*(I(11)/12)**3*(I(77)/72)**7)
                                weighted_d31=wprefactor*(iv.pi/beta)**(I(union)/2)*(
                                    (theta(I(252)/55*alpha)*theta(I(576)/77*alpha)
                                     +iv.exp(-800*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                                    +wperiodic)
                                d31_kernel=min((fixed_four_plane(I(31)/4),weighted_d31),key=lambda v:v.b)
                                assert all(det==31 for det,_ in determinant_counts)
                                ten_split=(
                                    sum((I(count)/coefficient_count*d31_kernel**n
                                         for det,count in determinant_counts),I(0))
                                    +I(1512)/coefficient_count*fixed_four_plane(I(39)/4)**n
                                    +I(one_count)/coefficient_count*fixed_four_plane(11)**n)
                                if ten_split.b<rare_split.b:
                                    rare_split=ten_split
                        if union==13:
                            # Every norm-ten extension is unit on nine new and
                            # one old position: 3*4*126 witnesses, Gram39.
                            thirteen_split=(I(min(one_count,1512))/coefficient_count
                                *fixed_four_plane(I(39)/4)**n
                                +I(one_count)/coefficient_count*fixed_four_plane(11)**n)
                            rare_split=min((rare_split,thirteen_split),key=lambda v:v.b)
                        if rare_split.b < one_power.b:
                            one_power = rare_split
                        # Only the first circuit can carry a norm-four word.
                        # Preserve its exact pair energy while Fourier/Holder
                        # bounds only the new positions of the second circuit.
                        direct_one = (I(3)/q**2*four_ball*new_groups[t]
                                      /iv.exp(union*beta*radius**2))
                        s['first_ball_ratios'][t, overlap] = direct_one/one_power
                        if direct_one.b < one_power.b:
                            one_power = direct_one
                    split = (I(bad_count)/coefficient_count*bad_bound**n
                             +one_power+none_power)
                    if c==4 and union==11:
                        s['eleven_position_parts'][overlap]={'one-four':one_power,
                            'no-four':none_power,'split':split}
                    if c == 3 and union == 5 and overlap == 2:
                        from wall1_five_point_weighted import ball_bound as five_ball_bound
                        weighted = five_ball_bound(radius**2,n,q)/iv.exp(union*beta*radius**2)
                        if weighted.b < (bad_bound**n).b:
                            split = I(bad_count)/coefficient_count*weighted+one_power+none_power
                    if c == 4 and union == 7 and overlap in (1, 3):
                        shared_power = shared_four_gaussian_bound(radius**2, n, q)
                        direct_shared = (shared_four_ball_bound(radius**2, n)
                                         +shared_four_gaussian_bound(radius**2, n, q, aliases_only=True))
                        if direct_shared.b < shared_power.b:
                            shared_power = direct_shared
                        shared_power /= iv.exp(union*beta*radius**2)
                        if shared_power.b < (bad_bound**n).b:
                            split = (I(bad_count)/coefficient_count*shared_power
                                     +one_power+none_power)
                    if c == 4 and t == 2 and overlap == 2:
                        # Five triangular and four orthogonal balanced-sign codes.
                        # Real equal-pair-sum count, plus nonzero modular layers.
                        assert n % 2 == 0
                        lens = pair_sum_ball_bound(radius**2, n)
                        kernel = theta(2*beta)**3*theta(I(3)*beta/2)
                        layers = theta(beta*q**2/6)**(2*n)-1
                        aliases = iv.exp(6*beta*radius**2)*kernel**n*layers
                        square_short = theta(4*alpha)**2
                        square_tail = iv.exp(-alpha*q**2/32)*half_sum
                        square_bound = (iv.pi/beta)**3*(
                            (square_short+square_tail)/q**2+periodic_plane)
                        square_power = square_bound**n
                        direct_square = (orthogonal_pair_ball_bound(radius**2, n)
                                         +orthogonal_pair_alias_bound(radius**2, n, q))
                        direct_square /= iv.exp(6*beta*radius**2)
                        if direct_square.b < square_power.b:
                            square_power = direct_square
                        triangular_count = 0 if (exclude_triangular_anchors or exclude_double_short_anchors) else 5
                        orthogonal_count = 0 if exclude_double_short_anchors else 4
                        bad_power = (triangular_count*(lens+aliases)/iv.exp(6*beta*radius**2)
                                     +orthogonal_count*square_power)
                        split = (bad_power/coefficient_count
                                 +one_power+none_power)
                    if split.b < power_bound.b:
                        power_bound = split
                    if c==4 and t in (4,5,6,7,9):
                        s['four_circuit_anchor_parts'][t,overlap]={
                            'one-four':one_power,'no-four':none_power,
                            'split':split,'selected':power_bound}
                    if c==3 and t in (2,3,5):
                        s['three_circuit_anchor_parts'][t,overlap]={
                            'one-four':one_power,'no-four':none_power,
                            'split':split,'selected':power_bound}
                if c in (5, 6):
                    # At girth five or six, norm-six rows are balanced on
                    # six positions. Only a first six-circuit can be one.
                    coefficient_count = q**(c+t+overlap-4)
                    six_lines = 10*comb(union, 6)
                    one_count = six_lines*q**(c-2) if t <= 5 else 0
                    if c == 6:
                        one_count += 10*q**(t+overlap-2)
                    one_count = min(coefficient_count, one_count)
                    # Full-support pairs force H=8 at girth five. At girth
                    # six, H<=7 is excluded and H=12 is disjoint, incompatible
                    # with the prescribed proper nonempty circuit overlap.
                    allowed_two = union == 8 if c == 5 else 8 <= union <= 11
                    two_count = min(coefficient_count, six_lines**2) if allowed_two else 0
                    assert 6*36**4 < q**2
                    half_sum = theta(power*alpha/2)**2
                    long_tail = iv.exp(-648*alpha)*half_sum
                    def six_plane(first, second, tail):
                        return (iv.pi/beta)**(I(union)/2)*(
                            (theta(I(first)*alpha)*theta(I(second)*alpha)+tail)/q**2
                            +periodic_plane)
                    one = six_plane(6, I(13)/2, long_tail)
                    two_height = I(9)/2
                    if c == 6:
                        two_height = {8: I(6), 10: I(16)/3, 11: I(35)/6}.get(union, two_height)
                    two = six_plane(6, two_height, long_tail)
                    none = six_plane(8, 6, iv.exp(-98*alpha)*half_sum)
                    none_term=none**n
                    if (c==6 and union<=11) or (c==5 and union==11):
                        # Girth six excludes support-five norm-eight rows.
                        # Unit pairs on H<=9 contradict girth; H=10 gives
                        # |dot|<=2; H=11 gives |dot|<=3 after Gauss reduction.
                        eight_height=(I(8) if union<=9 else I(15)/2 if union==10 else I(55)/8)
                        if c==6 and union==11:
                            # The prescribed six-support needs five zero columns.
                            # Two unit-eight rows have exclusive groups3,3;
                            # five zeros force shared signs to agree and |dot|=5.
                            # Their difference has norm six, excluded here.
                            eight_height=I(8)
                        tail8=iv.exp(-98*alpha)*half_sum
                        refined_none=(six_plane(8,eight_height,tail8)**n
                                      +six_plane(10,I(15)/2,tail8)**n)
                        none_term=min((none_term,refined_none),key=lambda v:v.b)
                    if c==6 and union==12:
                        tail8=iv.exp(-98*alpha)*half_sum
                        refined_twelve=(six_plane(8,10,tail8)**n
                            +six_plane(10,I(42)/5,tail8)**n
                            +six_plane(12,9,tail8)**n)
                        none_term=min((none_term,refined_twelve),key=lambda v:v.b)
                    if c==5 and union==10:
                        # Every two-norm-eight plane is generated modulo q by
                        # an unordered pair of balanced short lines. Count all
                        # such witnesses, retaining the old complete kernel.
                        eight_lines=35*comb(union,8)+20*comb(union,5)
                        pair_count=min(coefficient_count,comb(eight_lines,2))
                        refined_eight=(I(pair_count)/coefficient_count*none**n
                            +six_plane(8,8,iv.exp(-98*alpha)*half_sum)**n
                            +six_plane(10,I(15)/2,iv.exp(-98*alpha)*half_sum)**n)
                        none_term=min((none_term,refined_eight),key=lambda v:v.b)
                    if c==5 and union==11:
                        # Every eligible independent norm-eight pair has one
                        # support-five row (20 lines) and one unit row using
                        # all six new and two old coordinates (350 lines).
                        # Keep the complete cutoff-14 tails in every class.
                        from wall1_five_eleven_eight_pairs import PAIR_BOUND
                        tail8=iv.exp(-98*alpha)*half_sum
                        refined_eleven=(I(min(coefficient_count,PAIR_BOUND))/coefficient_count
                            *six_plane(8,I(55)/8,tail8)**n
                            +six_plane(8,8,tail8)**n
                            +six_plane(10,I(15)/2,tail8)**n)
                        none_term=min((none_term,refined_eleven),key=lambda v:v.b)
                    if c==5 and union==12:
                        # Eligible (8,8)/(8,10) pairs have Gram >=60/64;
                        # no reduced (10,10) pair has prescribed girth five.
                        tail8=iv.exp(-98*alpha)*half_sum
                        refined_twelve=(six_plane(8,I(15)/2,tail8)**n
                            +six_plane(10,I(19)/2,tail8)**n
                            +six_plane(12,9,tail8)**n)
                        none_term=min((none_term,refined_twelve),key=lambda v:v.b)
                    two_term=I(two_count)/coefficient_count*two**n
                    if c==5 and union==8:
                        from wall1_five_six_pair_codes import COUNTS as FIVE_COUNTS
                        exact_two=(I(FIVE_COUNTS[overlap])/coefficient_count
                                   *six_plane(6,I(16)/3,long_tail)**n)
                        two_term=min((two_term,exact_two),key=lambda v:v.b)
                    if c==6 and union==9:
                        from wall1_six_six_nine_codes import COUNTS
                        exact_two=sum((I(count)/coefficient_count
                            *six_plane(6,I(det)/6,long_tail)**n
                            for det,count in COUNTS[overlap]
                            if not (exclude_nine_twenty_seven and det==27)),I(0))
                        two_term=min((two_term,exact_two),key=lambda v:v.b)
                    if c==6 and union in (10,11):
                        from wall1_six_six_large_codes import COUNTS as LARGE_COUNTS
                        if union==10:
                            scaled_alpha=alpha*I(48)/49
                            scaled_a=a*I(48)/49
                            wdelta=2*iv.exp(-scaled_a/4)/(1-iv.exp(-2*scaled_a))
                            wperiodic=sum((comb(union,j)*wdelta**j
                                           for j in range(1,union+1)),I(0))
                            wprefactor=1/iv.sqrt((I(11)/12)**2*(I(49)/48)**8)
                            weighted_d32=wprefactor*(iv.pi/beta)**(I(union)/2)*(
                                (theta(I(3288)/539*alpha)*theta(I(35712)/6713*alpha)
                                 +iv.exp(-648*scaled_alpha)*theta(power*scaled_alpha/2)**2)/q**2
                                +wperiodic)
                        def large_six_kernel(det):
                            old=six_plane(6,I(det)/6,long_tail)
                            return min((old,weighted_d32),key=lambda v:v.b) if union==10 and det==32 else old
                        exact_two=sum((I(count)/coefficient_count
                            *large_six_kernel(det)**n
                            for det,count in LARGE_COUNTS[union][overlap]
                            if not (exclude_six_ten_thirty_two and union==10 and det==32)),I(0))
                        two_term=min((two_term,exact_two),key=lambda v:v.b)
                    one_term=I(one_count)/coefficient_count*one**n
                    if c==6 and union==10:
                        # Count all norm-six/eight witnesses; excluding two-six
                        # rows leaves second norm>=8, then>=10 beyond this cover.
                        witnesses=(10*comb(union,6))*(35*comb(union,8))
                        rare_eight=(I(min(one_count,witnesses))/coefficient_count*one**n
                            +I(one_count)/coefficient_count*six_plane(6,I(17)/2,long_tail)**n)
                        one_term=min((one_term,rare_eight),key=lambda v:v.b)
                    if c==6 and union==12:
                        eight_counts={1:(),2:((44,180),(48,170)),3:(),
                                      4:((44,180),),5:((48,850),)}
                        exact_eight=(sum((I(count)/coefficient_count
                            *six_plane(6,I(det)/6,long_tail)**n
                            for det,count in eight_counts[overlap]),I(0))
                            +I(one_count)/coefficient_count*six_plane(6,I(17)/2,long_tail)**n)
                        one_term=min((one_term,exact_eight),key=lambda v:v.b)
                    if c==6 and union==11:
                        from wall1_six_six_large_codes import EIGHT_COUNTS
                        eight_split=(sum((I(count)/coefficient_count
                            *six_plane(6,I(det)/6,long_tail)**n
                            for det,count in EIGHT_COUNTS[overlap]),I(0))
                            +I(one_count)/coefficient_count*six_plane(6,I(17)/2,long_tail)**n)
                        one_term=min((one_term,eight_split),key=lambda v:v.b)
                    split = (one_term
                             +two_term+none_term)
                    if c==6 and union==12:
                        s['twelve_six_parts'][overlap]={'one-six':one_term,
                            'two-six':two_term,'no-six':none_term,'split':split}
                    if c==6 and union==9:
                        s['six_circuit_anchor_parts'][overlap]={
                            'one-six':one_term,
                            'two-six':two_term,'no-six':none_term,'split':split}
                    if split.b < power_bound.b:
                        power_bound = split
                    if c==6:
                        s['six_circuit_split_parts'][t,overlap]={
                            'one-six':one_term,'two-six':two_term,
                            'no-six':none_term,'split':split,'selected':power_bound}
                    if c==5:
                        s['five_circuit_anchor_parts'][t,overlap]={
                            'one-six':one_term,'two-six':two_term,
                            'no-six':none_term,'split':split,'selected':power_bound}
                if (c==8 and union<=11) or (c==7 and union<=12):
                    # If both reduced minima are eight, girth eight excludes
                    # inner products +/-3,+/-5 on their five shared positions.
                    # Otherwise one minimum is >=10. Keep both complete cases.
                    def eight_plane(first,second):
                        return (iv.pi/beta)**(I(union)/2)*(
                            (theta(I(first)*alpha)*theta(I(second)*alpha)+tail_plane)/q**2
                            +periodic_plane)
                    # At girth seven, two unit norm-eight rows on H positions
                    # have shared sign groups (16-H +/- dot)/2, each <=H-7.
                    # H<=9 is impossible; H=10 forces dot=0; H=11 gives |dot|<=3.
                    # H=12: every projective group of two unit-eight rows has
                    # size<=4, so their plane has no seven-support circuit.
                    # If the second minimum is >=10, its height is >=8.
                    height=(I(63)/8 if c==8 and union==11 else
                            I(55)/8 if c==7 and union==11 else I(8))
                    short_eight=eight_plane(8,height)
                    no_eight=eight_plane(10,I(15)/2)
                    improved=short_eight**n+no_eight**n
                    if c==7 and union==11:
                        coefficient_count=q**(c+t+overlap-4)
                        eight_lines=35*comb(union,8)
                        pair_count=min(coefficient_count,comb(eight_lines,2))
                        # Two short unit rows determine their coefficient plane.
                        # Beyond this exception, second squared norm>=10 gives
                        # squared GS height>=8 when the first squared norm is8.
                        rare_eight=(I(pair_count)/coefficient_count*short_eight**n
                            +eight_plane(8,8)**n+no_eight**n)
                        improved=min((improved,rare_eight),key=lambda v:v.b)
                    if c==8:
                        # Unit norm-eight/ten pairs share >=7 coordinates;
                        # ten/ten pairs share >=9. Cancellation contradicts
                        # girth eight on H<=11. All other norm-ten shapes
                        # have support <=7 and are already excluded.
                        first_eight= eight_plane(8,I(63)/8 if union==11 else I(10))
                        first_ten=eight_plane(10,I(19)/2)
                        first_twelve=eight_plane(12,I(9))
                        improved=min((improved,first_eight**n+first_ten**n+first_twelve**n),
                                     key=lambda v:v.b)
                    if improved.b<power_bound.b:
                        power_bound=improved
                if c==8 and union==12:
                    # Count the exceptional(8,8) planes. All short rows are
                    # unit: girth eight excludes coefficient-two shapes.
                    coefficient_count=q**(c+t+overlap-4)
                    eight_lines=35*comb(union,8)
                    pair_count=min(coefficient_count,comb(eight_lines,2))
                    def twelve_eight_plane(first,second):
                        return (iv.pi/beta)**(I(union)/2)*(
                            (theta(I(first)*alpha)*theta(I(second)*alpha)+tail_plane)/q**2
                            +periodic_plane)
                    # Shared sign groups have size <=4: (8,10) has |dot|<=2,
                    # (10,10) has dot0. Larger second norms use Gauss reduction.
                    rare_eight=(I(pair_count)/coefficient_count*twelve_eight_plane(8,6)**n
                        +twelve_eight_plane(8,I(19)/2)**n
                        +twelve_eight_plane(10,I(19)/2)**n
                        +twelve_eight_plane(12,9)**n)
                    power_bound=min((power_bound,rare_eight),key=lambda v:v.b)
                anchors[c, t, overlap] = (iv.exp(union*beta*radius**2)
                    *power_bound/q**(m*(union-2)))
    full = {h: s['epsilon'][h] for h in range(3, 25)}
    strata = {}
    s['size14_two_relation_terms'] = {}
    s['size15_two_relation_terms'] = {}
    s['size16_two_relation_terms'] = {}
    s['size17_two_relation_terms'] = {}
    s['size17_stratum_candidates'] = {}
    from wall1_ball_slice_completion import completion_bound
    completions={r:completion_bound(s,r-1) for r in range(2,23)}
    for h in range(4, 25):
        for r in range(2, h-1):
            for c in range(3, r+2):
                one = (comb(h, c)*comb(h-c, r-c+1)*s['epsilon'][c]*mu**(r-c+1)
                       *completions[r]**(h-r-1))
                if c == r+1:
                    # Every r inputs are independent: fix the first circuit positions.
                    one /= comb(h, c)
                one /= r-c+2  # At least k+1 bases after contracting the anchor.
                two = I(0)
                for t in range(1 if r == c-1 else 2, min(r-c+2, h-c)+1):
                    for a in range(1, c):
                        if t+a < c:
                            continue
                        choices = (comb(h, c)*comb(h-c, t)*comb(c, a)
                                   *comb(h-c-t, r-c-t+2))
                        if c == r+1:
                            assert t == 1 and a == c-1
                            # Fix the extra input and the overlap as well.
                            choices = 1
                        charge = (choices*q**(c+t+a-4)*anchors[c, t, a]*mu**(r-c-t+2)
                                  *completions[r]**(h-r-2)/(r-c-t+3))
                        if c == 4 and t == 2 and a == 2:
                            charge /= 2  # Either four-circuit can be the first witness.
                        if h == 14:
                            s['size14_two_relation_terms'][r, c, t, a] = charge
                        if h == 15:
                            s['size15_two_relation_terms'][r, c, t, a] = charge
                        if h == 16:
                            s['size16_two_relation_terms'][r, c, t, a] = charge
                        if h == 17:
                            s['size17_two_relation_terms'][r, c, t, a] = charge
                        two += charge
                chosen = two if two.b < one.b else one
                if h == 17:
                    s['size17_stratum_candidates'][r,c] = {'one':one, 'two':two, 'selected':chosen}
                strata[h, r, c] = chosen
                full[h] += chosen
    for cap in range(8, 25):
        covered = {h: full[h] if h <= cap else s['base'][h] for h in range(3, 25)}
        bound = s['transfer'](covered)
        if cap == 9:
            assert bound < I('3.577e-28')
        if cap == 10:
            assert bound < I('1.646e-22')
        if cap == 11:
            assert bound < I('6.541e-17')
        if cap == 12:
            print('New size-twelve central envelope:', bound)
        if cap in (11, 12, 24):
            print('Full incidences through', cap, 'transfer log10:', iv.log10(bound), flush=True)
    # For known components these density errors use only smaller, already
    # bounded full-incidence counts. No global F_h <= mu^h premise is used.
    errors = density_errors(mu, s['rho_max'], q, full, 11)
    activities = {h: full[h]+errors[h] if h <= 11 else s['base'][h]
                  for h in range(3, 25)}
    known = s['transfer'](activities)
    assert known < I('6.541e-17')
    assert s['baseline']+s['bernoulli']+known < I('9.132e-13')
    assert F(9132, 10**16)+F(30088, 10**16) == F(3922, 10**15)
    print('Known components through 11, including density errors: < 6.541e-17.')
    print('Reference plus covered corrections < 9.132e-13; size-12..24 remainder open.')
    return s, full, strata


if __name__ == '__main__':
    witness_checks()
    fixed_position_checks()
    weighted_holder_checks()
    group_holder_checks()
    draw14_bounds()
