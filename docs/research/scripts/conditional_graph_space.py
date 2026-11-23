"""Exact conditional graph incidence using bases, never field-point enumeration.

The caller supplies a prime modulus. Raw vectors have output coordinates first;
quotient vectors have free input coordinates first, then output coordinates.
"""
from fractions import Fraction


def extend_basis(basis, vector, prime):
    """Return the canonical RREF row basis after adjoining one vector."""
    v = tuple(x % prime for x in vector)
    if basis and len(v) != len(basis[0]):
        raise ValueError('vector and basis dimensions differ')
    for row in basis:
        pivot = next(i for i, x in enumerate(row) if x)
        if v[pivot]:
            coefficient = v[pivot]
            v = tuple((x-coefficient*y) % prime for x, y in zip(v, row))
    if not any(v):
        return basis
    pivot = next(i for i, x in enumerate(v) if x)
    inverse = pow(v[pivot], -1, prime)
    v = tuple(x*inverse % prime for x in v)
    rows = [tuple((x-row[pivot]*y) % prime for x, y in zip(row, v))
            for row in basis]
    rows.append(v)
    rows.sort(key=lambda row: next(i for i, x in enumerate(row) if x))
    return tuple(rows)


def row_basis(vectors, prime):
    basis = ()
    for vector in vectors:
        basis = extend_basis(basis, vector, prime)
    return basis


class ConditionalGraphSpace:
    """Uniform A conditioned on containing fixed raw graph vectors.

    This conditions on membership only. Optional saturation is handled by
    joint_probability; shortestness is handled by the caller's exclusion sum.
    """

    def __init__(self, prime, outputs, inputs, fixed=()):
        self.prime, self.outputs, self.inputs = prime, outputs, inputs
        fixed = tuple(tuple(v) for v in fixed)
        if any(len(v) != outputs+inputs for v in fixed):
            raise ValueError('fixed vector dimension differs from graph dimension')
        self.fixed = row_basis((v[outputs:]+v[:outputs] for v in fixed), prime)
        self.pivots = tuple(next(i for i, x in enumerate(row) if x) for row in self.fixed)
        if any(pivot >= inputs for pivot in self.pivots):
            raise ValueError('inconsistent graph containment equations')
        self.free = tuple(i for i in range(inputs) if i not in self.pivots)
        self.free_inputs = len(self.free)
        self.containment_probability = Fraction(1, prime**(outputs*len(self.fixed)))

    def reduce(self, raw):
        if len(raw) != self.inputs+self.outputs:
            raise ValueError('raw vector dimension differs from graph dimension')
        v = tuple(x % self.prime for x in tuple(raw[self.outputs:])+tuple(raw[:self.outputs]))
        for pivot, row in zip(self.pivots, self.fixed):
            coefficient = v[pivot]
            v = tuple((x-coefficient*y) % self.prime for x, y in zip(v, row))
        return tuple(v[i] for i in self.free)+v[self.inputs:]

    def extend(self, basis, vector):
        if len(vector) != self.free_inputs+self.outputs:
            raise ValueError('residual vector dimension differs from quotient dimension')
        return extend_basis(basis, vector, self.prime)

    def graphic(self, basis):
        return all(next(i for i, x in enumerate(row) if x) < self.free_inputs for row in basis)

    def joint_probability(self, constraints, saturation=()):
        """Pr(constraints in graph, kernel on saturation is zero | fixed).

        Both arguments are RREF bases in residual coordinates. `saturation` is
        E/F, so a nonzero intersection with constraints makes the event impossible.
        """
        if not self.graphic(constraints):
            return Fraction(0)
        joined = constraints
        for row in saturation:
            joined = self.extend(joined, row)
        if len(joined) != len(constraints)+len(saturation):
            return Fraction(0)
        if len(saturation) > self.outputs:
            return Fraction(0)
        input_rank = len(row_basis((v[:self.free_inputs] for v in joined), self.prime))
        fixed_output_rank = len(joined)-input_rank
        result = Fraction(1, self.prime**(self.outputs*len(constraints)))
        for j in range(input_rank-len(constraints)):
            result *= 1-Fraction(self.prime**(fixed_output_rank+j), self.prime**self.outputs)
        return result
