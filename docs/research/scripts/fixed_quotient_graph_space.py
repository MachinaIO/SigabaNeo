"""Exact unconditional incidence inside a fixed coordinate-image stratum.

Raw full vectors are (S outputs, quotient outputs, inputs); raw quotient
vectors are (quotient outputs, inputs). The supplied modulus must be prime.
No shortest-vector or selected-history conditioning is implicit here.
"""
from fractions import Fraction
from conditional_graph_space import ConditionalGraphSpace, row_basis


class FixedQuotientGraphSpace:
    def __init__(self, prime, outputs, inputs, image_dimension, fixed_e=(), fixed_f=()):
        if not 0<=image_dimension<=outputs or inputs<0:
            raise ValueError('invalid graph or image dimensions')
        self.prime=prime
        self.outputs=outputs
        self.inputs=inputs
        self.image_dimension=image_dimension
        self.quotient_outputs=outputs-image_dimension
        e=self._vectors(fixed_e,outputs+inputs,'fixed E')
        f=self._vectors(fixed_f,outputs+inputs,'fixed F')
        self.fixed_e=row_basis(e,prime)
        self.fixed_f=row_basis(f,prime)
        if len(row_basis(self.fixed_e+self.fixed_f,prime))!=len(self.fixed_e):
            raise ValueError('F must be a subspace of E')
        if len(self.fixed_e)-len(self.fixed_f)!=image_dimension:
            raise ValueError('dim(E)-dim(F) must equal image dimension')
        self.image_space=ConditionalGraphSpace(prime,image_dimension,inputs,
                                               tuple(self._image(v) for v in self.fixed_f))
        self.quotient_space=ConditionalGraphSpace(prime,self.quotient_outputs,inputs,
                                                 tuple(self._quotient(v) for v in self.fixed_e))
        self.saturation=row_basis((self.image_space.reduce(self._image(v))
                                   for v in self.fixed_e),prime)
        if len(self.saturation)!=image_dimension:
            raise ValueError('fixed image/kernel stratum is inconsistent')

    def _vectors(self,vectors,width,name):
        result=tuple(tuple(v) for v in vectors)
        if any(len(v)!=width for v in result):
            raise ValueError(name+' vector dimension mismatch')
        return result

    def _image(self,v):
        return tuple(v[:self.image_dimension])+tuple(v[self.outputs:])

    def _quotient(self,v):
        return tuple(v[self.image_dimension:])

    def joint_probability(self,full_constraints=(),quotient_constraints=()):
        """Unconditional Pr(fixed stratum AND all supplied graph equations)."""
        full=self._vectors(full_constraints,self.outputs+self.inputs,'full constraint')
        quotient=self._vectors(quotient_constraints,self.quotient_outputs+self.inputs,
                               'quotient constraint')
        image_basis=row_basis((self.image_space.reduce(self._image(v)) for v in full),self.prime)
        quotient_basis=row_basis((self.quotient_space.reduce(v)
                                  for v in tuple(self._quotient(v) for v in full)+quotient),self.prime)
        return (self.image_space.containment_probability
                *self.image_space.joint_probability(image_basis,self.saturation)
                *self.quotient_space.containment_probability
                *self.quotient_space.joint_probability(quotient_basis))

    def scalar_nonzero_probability(self,z,zp,t,full_constraints=()):
        """Unconditional Pr(stratum, full equations, lambda(zp)=t*lambda(z)!=0).

        z,zp use raw quotient coordinates. t must be nonzero modulo prime.
        lambda is the residual quotient label, not the original full label.
        """
        z,zp=self._vectors((z,zp),self.quotient_outputs+self.inputs,'quotient label')
        full_constraints=self._vectors(full_constraints,self.outputs+self.inputs,'full constraint')
        if t%self.prime==0:
            raise ValueError('nonzero scalar required')
        difference=tuple((b-t*a)%self.prime for a,b in zip(z,zp))
        result=(self.joint_probability(full_constraints,(difference,))
                -self.joint_probability(full_constraints,(difference,z)))
        assert result>=Fraction(0)
        return result
