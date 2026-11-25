import SigabaNeoStd.Lattices.Estimator.PrimalHybrid

/-! PrimalBDD using GSA and MATZOV, with zero guessed coordinates and rank optimization. -/
namespace SigabaNeo.Lattices.Estimator.PrimalBdd
def cost (p : LWEParams) : Cost := PrimalHybrid.estimate p false true
end SigabaNeo.Lattices.Estimator.PrimalBdd
