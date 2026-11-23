"""Actual modulus/dimension algebra fixture; not a selected-history estimate."""
from fractions import Fraction as F
from conditional_graph_space import ConditionalGraphSpace, row_basis
from span_exclusion import grouped_subsets

q, m, d, t = 3329, 400, 117, 12
fixed = [tuple((j+1)*(i+3) % q for i in range(m))
         + tuple(int(i == j) for i in range(d)) for j in range(t)]
model = ConditionalGraphSpace(q, m, d, fixed)
assert model.free_inputs == 105
assert model.containment_probability == F(1, q**(m*t))
assert all(not any(model.reduce(v)) for v in fixed)
raw_events = [tuple((j+5)*(i+7) % q for i in range(m))
              + tuple(int(i == t+j) for i in range(d)) for j in range(8)]
events = [model.reduce(v) for v in raw_events]
assert all(len(v) == 505 for v in events)
layers = grouped_subsets((), events, model.extend, model.graphic, max_order=2)
assert [len(layer) for layer in layers] == [1, 8, 28]
for degree, layer in enumerate(layers):
    for state, multiplicity in layer.items():
        assert multiplicity == 1 and len(state) == degree
        assert model.joint_probability(state) == F(1, q**(m*degree))
p = F(1, q**m)
upper = sum((-1)**degree*sum(count*model.joint_probability(state)
                           for state, count in layer.items())
            for degree, layer in enumerate(layers))
assert upper == 1-8*p+28*p*p
assert upper >= (1-p)**8

# A pure output equation is impossible; dropping it preserves all coefficients.
impossible = model.reduce((1,)+(0,)*(m+d-1))
assert not model.graphic(model.extend((), impossible))
assert grouped_subsets((), events+[impossible], model.extend, model.graphic, 2) == layers

# A free input line is excluded from the kernel with probability 1-q^-400.
saturation = row_basis([events[0]], q)
assert model.joint_probability((), saturation) == 1-p
assert model.joint_probability(saturation, saturation) == 0
assert model.joint_probability(row_basis([events[1]], q), saturation) == p*(1-p)

# Canonical RREF must not depend on generator order or adding a dependent row.
forward = row_basis(events, q)
assert forward == row_basis(reversed(events), q)
dependent = tuple((x+2*y) % q for x, y in zip(events[0], events[1]))
assert model.extend(forward, dependent) == forward
print('Passed q=3329, raw dimension=517, fixed rank=12, residual dimension=505 checks.')
print('Degree-two grouping: 37 basis states; no finite-field points enumerated.')
