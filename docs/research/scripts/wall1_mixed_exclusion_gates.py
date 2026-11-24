"""Exact mixed full/quotient exclusion gates in a finite algebraic fixture.

Quotient-zero exclusions model a different condition from full membership
exclusions. This is not a production old-minimum or chronological-selection
proof. All signed coefficients are retained; only zero-incidence states
and exact coefficient cancellations are discarded.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import product

from conditional_graph_space import row_basis
from fixed_quotient_graph_space import FixedQuotientGraphSpace


def exclude(states, tag, vector, model):
    if tag not in ('full', 'quotient'):
        raise ValueError('unknown exclusion tag')
    updated = defaultdict(int)
    for (full, quotient), coefficient in states.items():
        updated[full, quotient] += coefficient
        if tag == 'full':
            extended = (row_basis(full + (vector,), model.prime), quotient)
        else:
            extended = (full, row_basis(quotient + (vector,), model.prime))
        if model.joint_probability(*extended):
            updated[extended] -= coefficient
    return {state: coefficient for state, coefficient in updated.items() if coefficient}


def main():
    q = 3
    model = FixedQuotientGraphSpace(q, 2, 1, 1, ((1, 0, 0),), ())
    events = (('full', (0, 0, 1)), ('full', (1, 1, 1)),
              ('quotient', (0, 1)))
    maps = tuple(product(range(q), repeat=2))

    def holds(a, tag, vector):
        if tag == 'full':
            x, y, z = vector
            return (x - a[0] * z) % q == (y - a[1] * z) % q == 0
        x, y = vector
        return (x - a[1] * y) % q == 0

    # Empty constraints and zero vectors are distinct test cases, even though
    # their incidence functions coincide. "Positive" means imposed events.
    positive_quotient = ((),) + tuple((v,) for v in product(range(q), repeat=2))
    positive_full = ((), ((0, 0, 1),), ((1, 1, 1),), ((2, 1, 1),))
    states = {((), ()): 1}
    checks = pointwise_checks = 0
    sizes = []
    masses = []
    for prefix in range(len(events) + 1):
        sizes.append(len(states))
        for a in maps:
            gate = all(not holds(a, tag, v) for tag, v in events[:prefix])
            expansion = sum(coefficient for (full, quotient), coefficient in states.items()
                            if all(holds(a, 'full', v) for v in full)
                            and all(holds(a, 'quotient', v) for v in quotient))
            assert expansion == int(gate)
            pointwise_checks += 1
        for added_full, added_quotient in product(positive_full, positive_quotient):
            rank_mass = sum((coefficient * model.joint_probability(
                full + added_full, quotient + added_quotient)
                for (full, quotient), coefficient in states.items()), Fraction(0))
            count = sum(all(not holds(a, tag, v) for tag, v in events[:prefix])
                        and all(holds(a, 'full', v) for v in added_full)
                        and all(holds(a, 'quotient', v) for v in added_quotient)
                        for a in maps)
            assert rank_mass == Fraction(count, len(maps))
            checks += 1
        masses.append(sum((coefficient * model.joint_probability(full, quotient)
                           for (full, quotient), coefficient in states.items()), Fraction(0)))
        if prefix < len(events):
            states = exclude(states, *events[prefix], model)
    assert model.joint_probability() == 1
    assert masses == [Fraction(1), Fraction(8, 9), Fraction(7, 9), Fraction(5, 9)]
    full_only = 1 - model.joint_probability(((0, 0, 1),), ())
    quotient_only = 1 - model.joint_probability((), ((0, 1),))
    assert full_only == Fraction(8, 9)
    assert quotient_only == Fraction(2, 3)
    assert full_only != quotient_only
    print('Prefix state counts:', sizes)
    print('Prefix gate masses:', masses)
    print('Full-only versus quotient-only exclusion:', full_only, quotient_only)
    print('PASS:', checks, 'joint incidence checks;', pointwise_checks,
          'pointwise grouped-expansion checks')


if __name__ == '__main__':
    main()
