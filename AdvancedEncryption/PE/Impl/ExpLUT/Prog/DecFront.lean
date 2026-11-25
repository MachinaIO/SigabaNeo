import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMFront
import SigabaNeoStd.Machines.Prog.FrameIO

/-!
# The front end of the `Dec` machine: parsing the input onto the registers

The machine has `256` tapes: the `247` tapes of `RingVM` (`vmE`, the register `x` on tape
`47 + x`), the input on tape `255`, and scratch `250 … 254`. `parseD` reads the input
`encodeTuple [pw, sk, C, ct]` and appends `sk`, `C`, `ct` to the registers `76`, `73`, `77`
(**`run_parseD`**).
-/

namespace SigabaNeo.Tape

namespace RingVM

open Prog

/-- The `RingVM` tapes inside the machine. -/
def vmE : Fin 247 ↪ Fin 256 := ⟨Fin.castLE (by decide), Fin.castLE_injective _⟩

/-- The tape of register `x`. -/
def tR (x : Fin 200) : Fin 256 := ⟨47 + x.val, by have := x.isLt; omega⟩

/-- `unfrP` from the input tape `255` into `d` (scratch `251`, `252`). -/
def uI (d : Fin 256) : Fin 4 → Fin 256 := ![255, d, 251, 252]

theorem run_unfrI {d : Fin 256} (hu : Function.Injective (uI d)) (s : Store 256)
    (u r : List Bool) (h : s 255 = Turing.MultiTapeTM.frame u ++ r) (h252 : s 252 = []) :
    run (Prog.map (uI d) unfrP) s =
      Function.update (Function.update (Function.update s 255 r) d (s d ++ u)) 251 [] := by
  rw [run_map hu, run_unfrP (s ∘ uI d) u r h h252, extend_update hu, extend_update hu,
    extend_update hu, extend_comp_self]
  rfl

/-- **Parsing** `encodeTuple [pw, sk, C, ct]`: `pw` dropped, `sk`, `C`, `ct` appended to the
registers `76`, `73`, `77`. -/
def parseD : Prog 256 :=
  Prog.map (uI 253) unfrP ⨾ Prog.map (uI 123) unfrP ⨾ Prog.map (uI 120) unfrP ⨾
    Prog.map (uI 124) unfrP ⨾ clr 253

theorem run_parseD (s : Store 256) (p a b e : List Bool)
    (h255 : s 255 = SigabaNeo.encodeTuple [p, a, b, e]) (h252 : s 252 = []) (h253 : s 253 = []) :
    run parseD s = Function.update (Function.update (Function.update (Function.update
      (Function.update s 255 []) 123 (s 123 ++ a)) 120 (s 120 ++ b))
      124 (s 124 ++ e)) 251 [] := by
  have e4 : SigabaNeo.encodeTuple [p, a, b, e] = Turing.MultiTapeTM.frame p ++
      (Turing.MultiTapeTM.frame a ++ (Turing.MultiTapeTM.frame b ++
        (Turing.MultiTapeTM.frame e ++ []))) := by
    simp [encodeTuple_cons, encodeTuple_nil]
  simp only [parseD, run_seq, run_clear]
  rw [run_unfrI (d := 253) (by decide) _ p _ (by rw [h255, e4]) h252]
  rw [run_unfrI (d := 123) (by decide) _ a (Turing.MultiTapeTM.frame b ++ (Turing.MultiTapeTM.frame e ++ []))
    (by simp [Function.update_apply, tR, Fin.ext_iff]) (by simp [Function.update_apply, tR, Fin.ext_iff, h252])]
  rw [run_unfrI (d := 120) (by decide) _ b (Turing.MultiTapeTM.frame e ++ []) (by simp [Function.update_apply, tR, Fin.ext_iff]) (by simp [Function.update_apply, tR, Fin.ext_iff, h252])]
  rw [run_unfrI (d := 124) (by decide) _ e [] (by simp [Function.update_apply, tR, Fin.ext_iff]) (by simp [Function.update_apply, tR, Fin.ext_iff, h252])]
  funext t
  simp only [Function.update_apply]
  by_cases h1 : t = 251
  · simp [h1]
  by_cases h2 : t = 124
  · subst h2; simp
  by_cases h3 : t = 255
  · subst h3; simp
  by_cases h4 : t = 120
  · subst h4; simp
  by_cases h5 : t = 123
  · subst h5; simp
  by_cases h6 : t = 253
  · subst h6; simp [h253]
  simp only [h1, h2, h3, h4, h5, h6, if_false]

end RingVM

end SigabaNeo.Tape
