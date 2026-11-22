import SigabaNeo.Lib.Machines.Prog.RegVMSim
import SigabaNeo.Lib.Lattices.ProgAlgo.SLPTape
import SigabaNeo.Lib.Lattices.Algo.FhatGates

/-!
# Generating gate tapes with the register machine: the bridge

A straight-line program `P : SLP ι` being built is held by the register machine (`RegVM`) as its
output `gatesW ix n W P 0` (the word of the program, `SLPTape`) and its gate count `P.length`
(`mk P σ`). A wire `w` is held in a register as its position `pos E ix w` (`ix i` for an input,
`n` for `1`, `n + 1 + m` for the gate `m`).

`exec_nand`: the instruction `nand d a b` appends the gate of the two wires held in `a`, `b` and
holds the new gate in `d` — it is `addNand` (the emitted position `fixv` of a wire is its
`wireIx`, `fixv_pos`). Then the Boolean gadgets of `BoolBuild` as register code (`notC`, `andC`,
`orC`, `xorC`, `muxC`, `fullAddC`), each equal to its builder.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP

variable {ι : Type*} (E : Env) (ix : ι → ℕ)

/-- The position of a wire. -/
def pos : Wire ι → ℕ
  | .input i => ix i
  | .one => E.n
  | .gate m => E.n + 1 + m

/-- The state holding the program `P`. -/
def mk (P : SLP ι) (σ : St) : St := { σ with out := Tape.Prog.gatesW ix E.n E.W P 0, t := P.length }

@[simp] theorem mk_sc (P : SLP ι) (σ : St) : (mk E ix P σ).sc = σ.sc := rfl
@[simp] theorem mk_ls (P : SLP ι) (σ : St) : (mk E ix P σ).ls = σ.ls := rfl
@[simp] theorem mk_src (P : SLP ι) (σ : St) : (mk E ix P σ).src = σ.src := rfl
@[simp] theorem mk_t (P : SLP ι) (σ : St) : (mk E ix P σ).t = P.length := rfl

theorem gatesW_append (n W : ℕ) : ∀ (P Q : SLP ι) (t : ℕ),
    Tape.Prog.gatesW ix n W (P ++ Q) t =
      Tape.Prog.gatesW ix n W P t ++ Tape.Prog.gatesW ix n W Q (t + P.length)
  | [], Q, t => by simp [Tape.Prog.gatesW]
  | g :: P, Q, t => by
    simp only [List.cons_append, Tape.Prog.gatesW, gatesW_append n W P Q (t + 1), List.append_assoc,
      List.length_cons]
    congr 4; omega

theorem fixv_pos (hix : ∀ i, ix i < E.n) {t : ℕ} (hM : E.n + 1 + t ≤ E.M) (w : Wire ι) :
    fixv E t (pos E ix w) = Tape.Prog.wireIx ix E.n t w := by
  have hm : min (E.n + 1 + t) E.M = E.n + 1 + t := min_eq_left hM
  cases w with
  | input i => have := hix i; simp only [fixv, pos, hm, Tape.Prog.wireIx]; split_ifs <;> omega
  | one => simp only [fixv, pos, hm, Tape.Prog.wireIx]; split_ifs <;> omega
  | gate m =>
    simp only [fixv, pos, hm, Tape.Prog.wireIx]
    split_ifs <;> omega

/-- **The `nand` instruction is `addNand`.** -/
theorem exec_nand (hix : ∀ i, ix i < E.n) (P : SLP ι) (σ : St) (d a b : SR) (wa wb : Wire ι)
    (ha : σ.sc a = pos E ix wa) (hb : σ.sc b = pos E ix wb) (hM : E.n + 1 + P.length ≤ E.M) :
    exec E (.nand d a b) (mk E ix P σ) =
      mk E ix (addNand P wa wb).1
        { σ with sc := Function.update σ.sc d (pos E ix (addNand P wa wb).2) } := by
  simp only [exec, mk, addNand, ha, hb, fixv_pos E ix hix hM, List.length_append,
    List.length_singleton, gatesW_append, Nat.zero_add, min_eq_left hM]
  simp [Tape.Prog.gatesW, uw, Tape.Prog.unaryW, pos]

/-! ### Monotone gate count -/

theorem t_le_exec : ∀ (c : Code) (σ : St), σ.t ≤ (exec E c σ).t
  | .nand _ _ _, σ => by simp [exec]
  | .one _, _ | .zero _, _ | .mov _ _, _ | .inc _, _ | .add _ _, _ | .sub _ _, _ | .lnil _, _
  | .lpush _ _, _ | .lpop _ _, _ | .lmov _ _, _ | .rdsrc _, _ | .skip, _ => le_of_eq rfl
  | .seq p q, σ => (t_le_exec p σ).trans (t_le_exec q _)
  | .ifLt a b p q, σ => by
      simp only [exec]; split_ifs
      · exact t_le_exec p σ
      · exact t_le_exec q σ
  | .rep a body, σ => by
      simp only [exec]
      generalize σ.sc a = m
      induction m generalizing σ with
      | zero => exact le_rfl
      | succ m ih => rw [Function.iterate_succ_apply]; exact (t_le_exec body σ).trans (ih _)

theorem t_le_iter (c : Code) : ∀ (m : ℕ) (σ : St), σ.t ≤ ((exec E c)^[m] σ).t
  | 0, σ => le_rfl
  | m + 1, σ => by
    rw [Function.iterate_succ_apply]; exact (t_le_exec E c σ).trans (t_le_iter c m _)

/-! ### Logic gadgets -/

/-- The register of `1`. -/
abbrev rONE : SR := 0
/-- The register of `z` (a wire of value `false`, the gate `0`). -/
abbrev rZ : SR := 1

/-- The constant registers: `1` and `z` hold their positions. -/
def Consts (σ : St) : Prop := σ.sc rONE = E.n ∧ σ.sc rZ = E.n + 1

def notC (d a : SR) : Code := .nand d rONE a
def andC (d a b u : SR) : Code := .seq (.nand u a b) (notC d u)
def orC (d a b u v : SR) : Code := .seq (notC u a) (.seq (notC v b) (.nand d u v))
def xorC (d a b m u v : SR) : Code :=
  .seq (.nand m a b) (.seq (.nand u a m) (.seq (.nand v b m) (.nand d u v)))
def muxC (d s a b m u v : SR) : Code :=
  .seq (notC m s) (.seq (.nand u s a) (.seq (.nand v m b) (.nand d u v)))

variable {E ix}

/-- Registers outside `S` are unchanged. -/
def Fr (S : List SR) (f g : SR → ℕ) : Prop := ∀ r, r ∉ S → g r = f r

theorem Fr.refl (S : List SR) (f : SR → ℕ) : Fr S f f := fun _ _ => rfl

theorem Fr.trans {S : List SR} {f g h : SR → ℕ} (h1 : Fr S f g) (h2 : Fr S g h) : Fr S f h :=
  fun r hr => (h2 r hr).trans (h1 r hr)

theorem Fr.mono {S S' : List SR} (hS : S ⊆ S') {f g : SR → ℕ} (h : Fr S f g) : Fr S' f g :=
  fun r hr => h r (fun h' => hr (hS h'))

theorem Fr.update {S : List SR} {f : SR → ℕ} {d : SR} (hd : d ∈ S) (v : ℕ) :
    Fr S f (Function.update f d v) := fun r hr =>
  Function.update_of_ne (fun h => hr (by rw [h]; exact hd)) _ _

/-- A gadget: from `mk P σ`, the code ends in `mk P' σ'`, with `σ'` differing from `σ` only on the
registers `S` (and holding `pos w` in `d`). -/
def Gad (c : Code) (S : List SR) (P P' : SLP ι) (σ : St) (d : SR) (w : Wire ι) : Prop :=
  ∃ sc', exec E c (mk E ix P σ) = mk E ix P' { σ with sc := sc' } ∧ sc' d = pos E ix w ∧ Fr S σ.sc sc'

theorem exec_notC (hix : ∀ i, ix i < E.n) (hc : Consts E σ) (P : SLP ι) (d a : SR) (wa : Wire ι)
    (ha : σ.sc a = pos E ix wa) (hM : E.n + 1 + P.length ≤ E.M) :
    exec E (notC d a) (mk E ix P σ) =
      mk E ix (notW P wa).1 { σ with sc := Function.update σ.sc d (pos E ix (notW P wa).2) } :=
  exec_nand E ix hix P σ d rONE a .one wa hc.1 ha hM

end FhatGen

end SigabaNeo.Lattices
