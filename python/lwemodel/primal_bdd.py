"""PrimalBDD with GSA, zero guessed coordinates and rank optimization."""
from .primal_hybrid import estimate


def primal_bdd(params):
    return estimate(params,False,plain=True)


cost = primal_bdd
