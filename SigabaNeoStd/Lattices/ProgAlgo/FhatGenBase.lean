import SigabaNeoStd.Machines.Prog.RegVMSim
import SigabaNeoStd.Lattices.ProgAlgo.SLPTape
import SigabaNeoStd.Lattices.Algo.FhatGates

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

/-! ### Register values stay below the template width -/

/-- Every scalar register is at most `M`. -/
def ScOK (σ : St) : Prop := ∀ r, σ.sc r ≤ E.M

theorem scOK_exec (hnM : E.n ≤ E.M) (hWM : E.W ≤ E.M) :
    ∀ (c : Code) (σ : St), Inv E σ → ScOK E σ → ScOK E (exec E c σ)
  | .nand d _ _, σ, _, h | .one d, σ, _, h | .zero d, σ, _, h | .mov d _, σ, _, h
  | .inc d, σ, _, h | .add d _, σ, _, h | .sub d _, σ, _, h => fun r => by
      by_cases hr : r = d
      · subst hr; simp [exec]; (try omega); (try exact h _); (try (have := h r; omega))
      · simp [exec, Function.update_of_ne hr]; exact h r
  | .lnil _, σ, _, h | .lpush _ _, σ, _, h | .lmov _ _, σ, _, h | .skip, σ, _, h => h
  | .lpop d l, σ, hI, h => fun r => by
      by_cases hr : r = d
      · subst hr; simp only [exec, Function.update_self]
        rcases hl : σ.ls l with _ | ⟨x, L⟩
        · simp
        · simpa using (hI.1 l).2 x (by simp [hl])
      · simp [exec, Function.update_of_ne hr]; exact h r
  | .rdsrc d, σ, hI, h => fun r => by
      by_cases hr : r = d
      · subst hr; simp only [exec, Function.update_self]
        rcases hl : σ.src with _ | ⟨x, L⟩
        · simp
        · simpa using (hI.2 x (by simp [hl])).trans hWM
      · simp [exec, Function.update_of_ne hr]; exact h r
  | .seq p q, σ, hI, h => scOK_exec hnM hWM q _ (inv_exec E p σ hI) (scOK_exec hnM hWM p σ hI h)
  | .ifLt a b p q, σ, hI, h => by
      simp only [exec]; split_ifs
      · exact scOK_exec hnM hWM p σ hI h
      · exact scOK_exec hnM hWM q σ hI h
  | .rep a body, σ, hI, h => by
      simp only [exec]
      generalize σ.sc a = m
      induction m generalizing σ with
      | zero => exact h
      | succ m ih =>
        rw [Function.iterate_succ_apply]
        exact ih _ (inv_exec E body σ hI) (scOK_exec hnM hWM body σ hI h)

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

theorem Consts.upd {σ : St} (hc : Consts E σ) {d : SR} (h0 : d ≠ rONE) (h1 : d ≠ rZ) (v : ℕ) :
    Consts E { σ with sc := Function.update σ.sc d v } :=
  ⟨by simp [Function.update_of_ne (Ne.symm h0), hc.1], by simp [Function.update_of_ne (Ne.symm h1), hc.2]⟩

/-- `exec` of a sequence. -/
@[simp] theorem exec_seq (p q : Code) (σ : St) : exec E (.seq p q) σ = exec E q (exec E p σ) := rfl

theorem exec_andC (hix : ∀ i, ix i < E.n) {σ : St} (hc : Consts E σ) (P : SLP ι) (d a b u : SR)
    (wa wb : Wire ι) (hu : u ≠ rONE) (hu' : u ≠ rZ) (ha : σ.sc a = pos E ix wa)
    (hb : σ.sc b = pos E ix wb) (hM : E.n + P.length + 2 ≤ E.M) :
    Gad (E := E) (ix := ix) (andC d a b u) [d, u] P (andW P wa wb).1 σ d (andW P wa wb).2 := by
  unfold Gad
  rw [andC, exec_seq, exec_nand E ix hix P σ u a b wa wb ha hb (by omega),
    exec_notC hix (hc.upd hu hu' _) _ d u (addNand P wa wb).2 (by simp)
      (by simp [addNand]; omega)]
  exact ⟨_, rfl, by simp [andW], (Fr.update (by simp) _).trans (Fr.update (by simp) _)⟩

theorem exec_orC (hix : ∀ i, ix i < E.n) {σ : St} (hc : Consts E σ) (P : SLP ι) (d a b u v : SR)
    (wa wb : Wire ι) (hu : u ≠ rONE) (hu' : u ≠ rZ) (hvb : b ≠ u)
    (huv : u ≠ v) (ha : σ.sc a = pos E ix wa) (hb : σ.sc b = pos E ix wb)
    (hM : E.n + P.length + 3 ≤ E.M) :
    Gad (E := E) (ix := ix) (orC d a b u v) [d, u, v] P (orW P wa wb).1 σ d (orW P wa wb).2 := by
  unfold Gad
  rw [orC, exec_seq, exec_seq, exec_notC hix hc P u a wa ha (by omega),
    exec_notC hix (hc.upd hu hu' _) _ v b wb (by simp [Function.update_of_ne hvb, hb])
      (by simp [notW, addNand]; omega),
    exec_nand E ix hix _ _ d u v (notW P wa).2 (notW (notW P wa).1 wb).2
      (by simp [Function.update_of_ne huv]) (by simp) (by simp [notW, addNand]; omega)]
  exact ⟨_, rfl, by simp [orW], ((Fr.update (by simp) _).trans (Fr.update (by simp) _)).trans
    (Fr.update (by simp) _)⟩

theorem exec_xorC (hix : ∀ i, ix i < E.n) {σ : St} (P : SLP ι) (d a b m u v : SR)
    (wa wb : Wire ι) (hma : a ≠ m) (hmb : b ≠ m) (hub : b ≠ u) (hmu : m ≠ u)
    (huv : u ≠ v) (ha : σ.sc a = pos E ix wa) (hb : σ.sc b = pos E ix wb)
    (hM : E.n + P.length + 4 ≤ E.M) :
    Gad (E := E) (ix := ix) (xorC d a b m u v) [d, m, u, v] P (xorW P wa wb).1 σ d
      (xorW P wa wb).2 := by
  unfold Gad
  rw [xorC, exec_seq, exec_seq, exec_seq, exec_nand E ix hix P σ m a b wa wb ha hb (by omega),
    exec_nand E ix hix _ _ u a m wa (addNand P wa wb).2 (by simp [Function.update_of_ne hma, ha])
      (by simp) (by simp [addNand]; omega),
    exec_nand E ix hix _ _ v b m wb (addNand P wa wb).2
      (by simp [Function.update_of_ne hmb, Function.update_of_ne hub, hb])
      (by simp [Function.update_of_ne hmu]) (by simp [addNand]; omega),
    exec_nand E ix hix _ _ d u v (addNand (addNand P wa wb).1 wa (addNand P wa wb).2).2
      (addNand (addNand (addNand P wa wb).1 wa (addNand P wa wb).2).1 wb (addNand P wa wb).2).2
      (by simp [Function.update_of_ne huv]) (by simp) (by simp [addNand]; omega)]
  exact ⟨_, rfl, by simp [xorW], (((Fr.update (by simp) _).trans (Fr.update (by simp) _)).trans
    (Fr.update (by simp) _)).trans (Fr.update (by simp) _)⟩

theorem exec_muxC (hix : ∀ i, ix i < E.n) {σ : St} (hc : Consts E σ) (P : SLP ι)
    (d s a b m u v : SR) (ws wa wb : Wire ι) (hsm : s ≠ m)
    (ham : a ≠ m) (hbm : b ≠ m) (hbu : b ≠ u) (hmu : m ≠ u) (huv : u ≠ v)
    (hs : σ.sc s = pos E ix ws) (ha : σ.sc a = pos E ix wa) (hb : σ.sc b = pos E ix wb)
    (hM : E.n + P.length + 4 ≤ E.M) :
    Gad (E := E) (ix := ix) (muxC d s a b m u v) [d, m, u, v] P (muxW P ws wa wb).1 σ d
      (muxW P ws wa wb).2 := by
  unfold Gad
  rw [muxC, exec_seq, exec_seq, exec_seq, exec_notC hix hc P m s ws hs (by omega),
    exec_nand E ix hix _ _ u s a ws wa (by simp [Function.update_of_ne hsm, hs])
      (by simp [Function.update_of_ne ham, ha]) (by simp [notW, addNand]; omega),
    exec_nand E ix hix _ _ v m b (notW P ws).2 wb (by simp [Function.update_of_ne hmu])
      (by simp [Function.update_of_ne hbm, Function.update_of_ne hbu, hb])
      (by simp [notW, addNand]; omega),
    exec_nand E ix hix _ _ d u v (addNand (notW P ws).1 ws wa).2
      (addNand (addNand (notW P ws).1 ws wa).1 (notW P ws).2 wb).2
      (by simp [Function.update_of_ne huv]) (by simp) (by simp [notW, addNand]; omega)]
  exact ⟨_, rfl, by simp [muxW], (((Fr.update (by simp) _).trans (Fr.update (by simp) _)).trans
    (Fr.update (by simp) _)).trans (Fr.update (by simp) _)⟩

/-! ### The full adder -/

/-- The full adder on the registers `16 17 18` (summands and carry), into `19` (sum) and `20`
(carry), with the scratch `21 … 32`. -/
def fullAddC : Code :=
  .seq (xorC 21 16 17 22 23 24) (.seq (xorC 19 21 18 25 26 27) (.seq (.nand 28 16 17)
    (.seq (orC 29 16 17 30 31) (.seq (.nand 32 29 18) (.nand 20 28 32)))))

/-- The registers written by `fullAddC`. -/
def faRegs : List SR := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]

theorem exec_fullAddC (hix : ∀ i, ix i < E.n) {σ : St} (hc : Consts E σ) (P : SLP ι)
    (wa wb wc : Wire ι) (ha : σ.sc 16 = pos E ix wa) (hb : σ.sc 17 = pos E ix wb)
    (hcc : σ.sc 18 = pos E ix wc) (hM : E.n + P.length + 14 ≤ E.M) :
    ∃ sc', exec E fullAddC (mk E ix P σ) = mk E ix (fullAdd P wa wb wc).1 { σ with sc := sc' } ∧
      sc' 19 = pos E ix (fullAdd P wa wb wc).2.1 ∧ sc' 20 = pos E ix (fullAdd P wa wb wc).2.2 ∧
      Fr faRegs σ.sc sc' := by
  obtain ⟨sc1, h1, d1, f1⟩ := exec_xorC (E := E) (ix := ix) hix (σ := σ) P 21 16 17 22 23 24 wa wb
    (by decide) (by decide) (by decide) (by decide) (by decide) ha hb (by omega)
  set P1 := (xorW P wa wb).1
  obtain ⟨sc2, h2, d2, f2⟩ := exec_xorC (E := E) (ix := ix) hix (σ := { σ with sc := sc1 }) P1
    19 21 18 25 26 27 (xorW P wa wb).2 wc (by decide) (by decide) (by decide) (by decide)
    (by decide) d1 (by dsimp only; rw [f1 18 (by decide)]; exact hcc) (by simp [P1, length_xorW]; omega)
  dsimp only at f2 h2
  set P2 := (xorW P1 (xorW P wa wb).2 wc).1
  have h3 := exec_nand E ix hix P2 { σ with sc := sc2 } 28 16 17 wa wb
    (by dsimp only; rw [f2 16 (by decide), f1 16 (by decide)]; exact ha)
    (by dsimp only; rw [f2 17 (by decide), f1 17 (by decide)]; exact hb)
    (by simp [P2, P1, length_xorW]; omega)
  set P3 := (addNand P2 wa wb).1
  have hc3 : Consts E { σ with sc := Function.update sc2 28 (pos E ix (addNand P2 wa wb).2) } := by
    refine ⟨?_, ?_⟩ <;> simp only [Function.update_of_ne (by decide : (0 : SR) ≠ 28),
      Function.update_of_ne (by decide : (1 : SR) ≠ 28)]
    · rw [f2 0 (by decide), f1 0 (by decide)]; exact hc.1
    · rw [f2 1 (by decide), f1 1 (by decide)]; exact hc.2
  obtain ⟨sc4, h4, d4, f4⟩ := exec_orC (E := E) (ix := ix) hix hc3 P3 29 16 17 30 31 wa wb
    (by decide) (by decide) (by decide) (by decide)
    (by simp [Function.update_of_ne (by decide : (16 : SR) ≠ 28)];
        rw [f2 16 (by decide), f1 16 (by decide)]; exact ha)
    (by simp [Function.update_of_ne (by decide : (17 : SR) ≠ 28)];
        rw [f2 17 (by decide), f1 17 (by decide)]; exact hb)
    (by simp [P3, P2, P1, length_xorW, length_addNand]; omega)
  dsimp only at f4 h4
  set P4 := (orW P3 wa wb).1
  have h5 := exec_nand E ix hix P4 { σ with sc := sc4 } 32 29 18 (orW P3 wa wb).2 wc d4
    (by dsimp only; rw [f4 18 (by decide)]; simp [Function.update_of_ne (by decide : (18 : SR) ≠ 28)];
        rw [f2 18 (by decide), f1 18 (by decide)]; exact hcc)
    (by simp [P4, P3, P2, P1, length_xorW, length_addNand, length_orW]; omega)
  set P5 := (addNand P4 (orW P3 wa wb).2 wc).1
  have h6 := exec_nand E ix hix P5
      { σ with sc := (Function.update sc4 32 (pos E ix (addNand P4 (orW P3 wa wb).2 wc).2)) }
      20 28 32 (addNand P2 wa wb).2
      (addNand P4 (orW P3 wa wb).2 wc).2
    (by dsimp only; simp [Function.update_of_ne (by decide : (28 : SR) ≠ 32)]; rw [f4 28 (by decide)]; simp)
    (by simp) (by simp [P5, P4, P3, P2, P1, length_xorW, length_addNand, length_orW]; omega)
  dsimp only at h3 h5 h6
  rw [fullAddC, exec_seq, exec_seq, exec_seq, exec_seq, exec_seq, h1, h2, h3, h4, h5, h6]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne (by decide : (19 : SR) ≠ 20),
      Function.update_of_ne (by decide : (19 : SR) ≠ 32)]
    rw [f4 19 (by decide)]; simp [Function.update_of_ne (by decide : (19 : SR) ≠ 28)]
    rw [d2]; rfl
  · simp; rfl
  · intro r hr
    have hr' : r ∉ ([21, 22, 23, 24] : List SR) ∧ r ∉ ([19, 25, 26, 27] : List SR) ∧ r ≠ 28 ∧
        r ∉ ([29, 30, 31] : List SR) ∧ r ≠ 32 ∧ r ≠ 20 := by
      simp only [faRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> tauto
    simp only [Function.update_of_ne hr'.2.2.2.2.2, Function.update_of_ne hr'.2.2.2.2.1]
    rw [f4 r (by simp at hr' ⊢; tauto), Function.update_of_ne hr'.2.2.1, f2 r hr'.2.1, f1 r hr'.1]

end FhatGen

end SigabaNeo.Lattices
