import SigabaNeo.Lib.Lattices.ProgAlgo.ValGsw

/-!
# The two runs of the word machine

* `fhatC` (the simulation of `f̂`, step `f` on joint words of `V` bits): `zv := f (one, one)`, the
  words `zv^k` and `true^k`, the inputs (`insC`), the constant bundle (`cbC`), the store
  `C^(W − 9) ++ ins`, the gates with the NAND block (`gloopC nandC`): **`exec_fhatC`**, `OUTW` ends
  with the word of the output bundle `fhatV …`;
* `gswC` (the simulation of the predicate): the inputs (`insGC`), the store `one^(W − 9) ++ ins`,
  the gates with the single `gate`: **`exec_gswC`**, `OUTW` ends with the value of the output wire.
-/

namespace SigabaNeo.Tape

namespace ValVM

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP SigabaNeo.Lattices.Algo SigabaNeo.Encode

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {V : ℕ} {f : List Bool → List Bool → List Bool}

/-! ### Shifting copies of a word -/

/-- One copy of `src` shifted into `dst` (through `sc`, `|cl|` bits). -/
def shiftOne (dst src sc cl : Fin 120) : Code := ofList [.cp sc src, .mv dst sc cl]

theorem exec_shiftRep {dst src sc cl ctr : Fin 120}
    (hd : dst ≠ src ∧ dst ≠ sc ∧ dst ≠ cl ∧ dst ≠ ctr) (hs : src ≠ sc ∧ src ≠ ctr)
    (hc : sc ≠ cl ∧ sc ≠ ctr ∧ cl ≠ ctr) (w : St) (hl : (w src).length = (w cl).length) :
    exec V f (.rep ctr (shiftOne dst src sc cl)) w dst =
        (w dst ++ (List.replicate (w ctr).length (w src)).flatten).drop
          ((w ctr).length * (w cl).length) ∧
      ∀ j, j ≠ dst → j ≠ sc → j ≠ ctr → exec V f (.rep ctr (shiftOne dst src sc cl)) w j = w j := by
  have I := exec_rep_inv (V := V) (f := f) (c := ctr) (B := shiftOne dst src sc cl)
    (fun r w' => w' dst = (w dst ++ (List.replicate r (w src)).flatten).drop (r * (w cl).length) ∧
      ∀ j, j ≠ dst → j ≠ sc → j ≠ ctr → w' j = w j)
    (fun r w' ih => by
      obtain ⟨h1, h2⟩ := ih
      have e : ∀ j, j ≠ dst → j ≠ sc → j ≠ ctr → Function.update w' ctr (w' ctr).tail j = w j :=
        fun j a1 a2 a3 => by rw [Function.update_of_ne a3, h2 j a1 a2 a3]
      simp only [shiftOne, exec_ofList, List.foldl_cons, List.foldl_nil, exec_cp']
      rw [exec_mv_shift (d := dst) (s := sc) (c := cl) (x := w src) (L := []) (by
          simp only [not_or]; exact ⟨hd.2.1, hd.2.2.1, hc.1⟩)
        (by rw [Function.update_of_ne hc.1.symm, e cl (Ne.symm hd.2.2.1) hc.1.symm hc.2.2, hl])
        (by rw [Function.update_self, e src hd.1.symm hs.1 hs.2, List.append_nil])]
      refine ⟨?_, fun j a1 a2 a3 => ?_⟩
      · rw [Function.update_self, Function.update_of_ne hd.2.1, Function.update_of_ne hd.2.2.2, h1,
          hl, drop_append_drop' (by simp; nlinarith [List.length_replicate (n := r) (a := w src)]),
          List.append_assoc, List.replicate_succ', List.flatten_append, List.flatten_singleton,
          Nat.succ_mul]
      · rw [Function.update_of_ne a1, Function.update_of_ne a2, Function.update_of_ne a2,
          e j a1 a2 a3]) w
    ⟨by simp, fun _ _ _ _ => rfl⟩
  exact I

end ValVM

end SigabaNeo.Tape
