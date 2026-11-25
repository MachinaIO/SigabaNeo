import SigabaNeoStd.Lattices.Homomorphic.GSWGates
import SigabaNeoStd.Lattices.Algo.FhatLoop

/-!
# The number of gates of `f̂` with explicit orders

The bounds of `Homomorphic/GSWGates` for the compiler with the orders of the terms `ordT` and of
the output coefficients `ordO` as parameters (`FhatLoop`): a NAND block appends at most
`|ordO| · coefGates |ordT| k` gates, and `fhatSLPL` of a program with `g` gates has at most
`1 + g · |ordO| · coefGates |ordT| k` gates; at the orders `ordT₀`, `ordO₀` of `fhatSLP` this is
`fhatGates N k g` (`length_fhatSLPL₀`).
-/

namespace SigabaNeo.Lattices.Algo

open SLP Cslib

variable {N k : ℕ} {ι : Type*}

theorem length_coefCircuitL (ordT : List ((Fin 2 × Fin k) × Fin N)) (z : Wire ι) (q : ℕ)
    (repA repB : BI N k → Wire ι) (Gv : ℕ) (a : Fin 2) (col : Fin 2 × Fin k) (t : Fin N)
    (p : SLP ι) :
    (coefCircuitL ordT z q repA repB Gv a col t p).1.length ≤ p.length + coefGates ordT.length k :=
  length_coefCore z q k repA repB Gv a col t (treeHeight N k) ordT p

theorem length_nandBlockL (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gv : OI N k → ℕ) (z : Wire ι) (q : ℕ) (repA repB : BI N k → Wire ι) (p : SLP ι) :
    (nandBlockL ordT ordO gv z q repA repB p).1.length ≤
      p.length + ordO.length * coefGates ordT.length k :=
  length_foldl_le (fun st : SLP ι × (OI N k → List (Wire ι)) => st.1.length)
    (blockStepL ordT gv z q repA repB) _
    (fun st _ => length_coefCircuitL ordT z q repA repB _ _ _ _ st.1) ordO (p, fun _ => [])

theorem length_compileSLPL {A : Type*} (ordT : List ((Fin 2 × Fin k) × Fin N))
    (ordO : List (OI N k)) (gv : OI N k → ℕ) (z : Wire (A × BI N k)) (q : ℕ) (p : SLP A)
    (w : Wire A) (prog : SLP (A × BI N k)) :
    (compileSLPL ordT ordO gv z q p w prog).1.length ≤
      prog.length + p.length * (ordO.length * coefGates ordT.length k) :=
  length_foldl_le (fun st : SLP (A × BI N k) × List (BI N k → Wire (A × BI N k)) => st.1.length)
    (compileStepL ordT ordO gv z q) _
    (fun st _ => length_nandBlockL ordT ordO gv z q _ _ st.1) p (prog, [])

/-- **The gates of `f̂` with explicit orders.** -/
theorem length_fhatSLPL {A : Type*} (ordT : List ((Fin 2 × Fin k) × Fin N)) (ordO : List (OI N k))
    (gv : OI N k → ℕ) (q : ℕ) (p : SLP A) (w : Wire A) :
    (fhatSLPL ordT ordO gv q p w).1.length ≤
      1 + p.length * (ordO.length * coefGates ordT.length k) := by
  simpa [fhatSLPL] using length_compileSLPL ordT ordO gv (.gate 0) q p w [⟨.one, .one⟩]

@[simp] theorem length_ordT₀ (N k : ℕ) : (ordT₀ N k).length = 2 * k * N := length_enumT' N k

@[simp] theorem length_ordO₀ (N k : ℕ) : (ordO₀ N k).length = 4 * k * N := length_enumO' N k

/-- **The gates of `f̂`** at the orders of `fhatSLP`: `fhatGates N k g` for `g` source gates. -/
theorem length_fhatSLPL₀ {A : Type*} (gv : OI N k → ℕ) (q : ℕ) (p : SLP A) (w : Wire A) :
    (fhatSLPL (ordT₀ N k) (ordO₀ N k) gv q p w).1.length ≤ fhatGates N k p.length := by
  have := length_fhatSLPL (ordT₀ N k) (ordO₀ N k) gv q p w
  simpa [fhatGates, nandGates] using this

end SigabaNeo.Lattices.Algo
