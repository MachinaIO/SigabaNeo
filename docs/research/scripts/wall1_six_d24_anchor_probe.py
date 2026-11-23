"""Diagnostic D24 six-point rank-four anchor cover; no production exclusion."""
import contextlib,io
from math import comb
from wall1_general_two_relations import draw14_bounds
from wall1_parallel_contraction import parallel_completion_count,marked_parallel_completion_count

from wall1_six_d24_anchor import envelope


def main():
    with contextlib.redirect_stdout(io.StringIO()):
        s,_,_=draw14_bounds(exclude_double_short_anchors=True,exclude_four_six_twenty=True,
            exclude_four_six_twenty_three=True,exclude_four_six_twenty_four=True,
            exclude_seven_four_six=True,exclude_ten_twenty_eight=True)
    iv=s['iv'];target=s['size17_two_relation_terms'][8,4,2,2]
    new,parts=envelope(s,17,8)
    print('complete D24 H6 anchor / current t2a2 term log10',iv.log10(new/target))
    for t,part in parts.items():print('crossing',t,'ratio to target log10',iv.log10(part/target))
    return s,new,parts

if __name__=='__main__':main()
