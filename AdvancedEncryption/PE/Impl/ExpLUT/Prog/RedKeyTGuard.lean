import PE.Impl.ExpLUT.Prog.RedKeyTFront
import SigabaNeo.Lib.Machines.Prog.AppendWCost

/-!
# Module 9: bounds of the tests of `rkKeyPT`

Per-tape envelopes on the `247` tapes, with `S` the bound of tape `0` (the raw secret) and `P`
the bound of tape `1` (`C`, `P = predLen`):

* `gE S P`: tape `0 ≤ S`, tapes `1 … 6 ≤ P`, all others `0` (during the tests);
* `gF S P`: tape `0 ≤ S`, tapes `1, 2 ≤ P`, all others `0` (after the tests; scratch cleared).

**`bounds_rkLeChkT`**, **`bounds_clrEqChkT`**: from `ℓ ≤ gF` (every input bound of the component
is below `gF S predLen`), the static length bound stays below `gF` and the time is at most
`(20 P + 210) (2 S + 5)`. The proofs are generic in the length program (`natU`) so the kernel
never unfolds `natU predLen`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Prog.RedKeyM
open AdvancedEncryption.ExpLUT.Params
open scoped SigabaNeo.Tape.Prog

/-- The envelope during the tests. -/
def gE (S P : ℕ) (t : Fin 247) : ℕ := if t.val = 0 then S else if t.val ≤ 6 then P else 0

/-- The envelope after the tests. -/
def gF (S P : ℕ) (t : Fin 247) : ℕ := if t.val = 0 then S else if t.val ≤ 2 then P else 0

theorem gF_le_gE (S P : ℕ) : gF S P ≤ gE S P := fun t => by
  simp only [gF, gE]; split_ifs <;> omega

theorem gE_le {S P : ℕ} (h : P ≤ S) (t : Fin 247) : gE S P t ≤ S := by
  simp only [gE]; split_ifs <;> omega

theorem io2_le_gF (S P : ℕ) : io2 (R := 245) S P 0 ≤ gF S P := fun t => by
  simp only [io2, gF]; split_ifs <;> omega

/-! ### The tests as explicit programs -/

theorem rkLeChk_eq : rkLeChk = natU 3 5 6 predLen ⨾ cp 4 1 ⨾ dropT 4 3 5 ⨾
    ifBlank 4 (setB 2 true) (setB 2 false) ⨾ clr 3 ⨾ clr 4 := by
  show Prog.seq (Prog.map rkChkMap (natU 2 4 5 predLen)) _ = _
  rw [map_natU]; rfl

theorem rkEqChk_eq : rkEqChk = natU 3 5 6 predLen ⨾ cp 4 1 ⨾ dropT 4 3 5 ⨾
    ifBlank 4 (dropT 3 1 5 ⨾ ifBlank 3 (setB 2 true) (setB 2 false)) (setB 2 false) ⨾
      clr 3 ⨾ clr 4 :=
  map_lenEqP rkChkMap predLen

/-! ### The envelope calculus -/

section Env

variable (S P : ℕ)

/-- `p` keeps the envelope `gE` with `m` units of `2 S + 5` steps. -/
def UG (p : SigabaNeo.Tape.Prog 247) (m : ℕ) : Prop :=
  ∀ ℓ : Fin 247 → ℕ, ℓ ≤ gE S P →
    Prog.timeBoundT p ℓ ≤ m * (2 * S + 5) ∧ Prog.lenBoundT p ℓ ≤ gE S P

variable {S P}

theorem ug_seq {p q : SigabaNeo.Tape.Prog 247} {m m' : ℕ} (hp : UG S P p m) (hq : UG S P q m') :
    UG S P (p ⨾ q) (m + m') := fun ℓ hℓ => by
  have a := hp ℓ hℓ; have b := hq _ a.2
  exact ⟨by rw [timeBoundT_seq, Nat.add_mul]; omega, b.2⟩

theorem ug_mono {p : SigabaNeo.Tape.Prog 247} {m m' : ℕ} (hp : UG S P p m) (hm : m ≤ m') :
    UG S P p m' := fun ℓ hℓ =>
  ⟨(hp ℓ hℓ).1.trans (Nat.mul_le_mul_right _ hm), (hp ℓ hℓ).2⟩

theorem ug_if {p q : SigabaNeo.Tape.Prog 247} {m : ℕ} (i : Fin 247) (hp : UG S P p m)
    (hq : UG S P q m) : UG S P (Prog.ifBlank i p q) (m + 1) := fun ℓ hℓ => by
  have a := hp ℓ hℓ; have b := hq ℓ hℓ
  refine ⟨?_, fun t => max_le (a.2 t) (b.2 t)⟩
  show max _ _ + 1 ≤ _
  rw [Nat.add_mul, Nat.one_mul]; have := max_le a.1 b.1; omega

theorem ug_prim (hPS : P ≤ S) (q : Prim 247) (hpad : q.pad ≤ 1)
    (hq : ∀ ℓ : Fin 247 → ℕ, ℓ ≤ gE S P → Prim.lenT q ℓ ≤ gE S P) : UG S P (Prog.prim q) 1 :=
  fun ℓ hℓ => by
    refine ⟨?_, hq ℓ hℓ⟩
    show 2 * (supB ℓ + q.pad) + 3 ≤ _
    have := SigabaNeo.Tape.Prog.supB_le_of fun t => (hℓ t).trans (gE_le hPS t)
    omega

theorem ug_clr (hPS : P ≤ S) (t : Fin 247) : UG S P (clr t) 1 :=
  ug_prim hPS _ (by simp [Prim.pad]) fun ℓ hℓ u => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hℓ u

theorem ug_cp41 (hPS : P ≤ S) : UG S P (cp (4 : Fin 247) 1) 1 :=
  ug_prim hPS _ (by simp [Prim.pad]) fun ℓ hℓ u => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs with h
    · subst h; exact (hℓ 1).trans (by simp [gE])
    · exact hℓ u

theorem ug_setB2 (hPS : P ≤ S) (hP : 1 ≤ P) (b : Bool) : UG S P (setB (2 : Fin 247) b) 2 :=
  fun ℓ hℓ => by
    have hs : supB ℓ ≤ S := SigabaNeo.Tape.Prog.supB_le_of fun t => (hℓ t).trans (gE_le hPS t)
    have hs' : supB (Prim.lenT (.clear (2 : Fin 247)) ℓ) ≤ S := SigabaNeo.Tape.Prog.supB_le_of fun t => by
      simp only [Prim.lenT, Function.update_apply]; split_ifs
      · exact Nat.zero_le _
      · exact (hℓ t).trans (gE_le hPS t)
    refine ⟨?_, fun u => ?_⟩
    · show 2 * (supB ℓ + 0) + 3 + (2 * (supB (Prim.lenT (.clear (2 : Fin 247)) ℓ) + 1) + 3) ≤ _
      omega
    · show Prim.lenT (.snoc 2 b) (Prim.lenT (.clear (2 : Fin 247)) ℓ) u ≤ _
      simp only [Prim.lenT, Function.update_apply]; split_ifs with h
      · subst h; simp [gE]; omega
      · exact hℓ u

/-- `dropT t x a` with `x`, `a` among the test tapes `1 … 6`. -/
theorem ug_dropT (hPS : P ≤ S) (t x a : Fin 247) (hta : t ≠ a) (hxa : x ≠ a)
    (hx : gE S P x = P) (ha : gE S P a = P) : UG S P (Prog.dropT t x a) (3 * P + 3) :=
  fun ℓ hℓ => by
    have h := dropT_bounds hta hxa ℓ (S := S) fun u => (hℓ u).trans (gE_le hPS u)
    have hx' : ℓ x ≤ P := hx ▸ hℓ x
    refine ⟨h.1.trans (Nat.mul_le_mul_right _ (by omega)), fun u => (h.2 u).trans ?_⟩
    simp only [Function.update_apply]; split_ifs with hu
    · subst hu; rw [ha]; exact (hℓ x).trans hx.le
    · exact hℓ u

/-- `natU 3 5 6 n` (`n ≤ P`). -/
theorem ug_natU (hPS : P ≤ S) (n : ℕ) (hn : n ≤ P) :
    UG S P (Prog.natU (3 : Fin 247) 5 6 n) (12 * n + 100) := fun ℓ hℓ => by
  have h := natU_bounds (o := (3 : Fin 247)) (a := 5) (b := 6) (by decide) (by decide)
    (by decide) n ℓ (S := S) (fun u => (hℓ u).trans (gE_le hPS u)) (hn.trans hPS)
  refine ⟨h.1, fun u => (h.2 u).trans ?_⟩
  split_ifs with h3 h56
  · subst h3; simp [gE]; exact hn
  · rcases h56 with rfl | rfl
    · exact max_le (hℓ 5) (by simp [gE]; exact hn)
    · exact max_le (hℓ 6) (by simp [gE]; exact hn)
  · exact hℓ u

/-! ### The tests, generic in the length program `A` -/

theorem ug_leCore (hPS : P ≤ S) (hP : 1 ≤ P) {A : SigabaNeo.Tape.Prog 247} {m : ℕ}
    (hA : UG S P A m) :
    UG S P ((A ⨾ cp 4 1 ⨾ Prog.dropT 4 3 5 ⨾ Prog.ifBlank 4 (setB 2 true) (setB 2 false) ⨾
      clr 3 ⨾ clr 4) ⨾ clr 5 ⨾ clr 6) (m + 3 * P + 14) := by
  have hc := ug_seq (ug_clr hPS 3) (ug_clr hPS 4)
  have hc' := ug_seq (ug_clr hPS 5) (ug_clr hPS 6)
  have hi := ug_if 4 (ug_setB2 hPS hP true) (ug_setB2 hPS hP false)
  have hd := ug_dropT hPS 4 3 5 (by decide) (by decide) (by simp [gE]) (by simp [gE])
  exact ug_mono (ug_seq (ug_seq hA (ug_seq (ug_cp41 hPS) (ug_seq hd (ug_seq hi hc)))) hc') (by omega)

theorem ug_eqCore (hPS : P ≤ S) (hP : 1 ≤ P) {A : SigabaNeo.Tape.Prog 247} {m : ℕ}
    (hA : UG S P A m) :
    UG S P ((A ⨾ cp 4 1 ⨾ Prog.dropT 4 3 5 ⨾
      Prog.ifBlank 4 (Prog.dropT 3 1 5 ⨾ Prog.ifBlank 3 (setB 2 true) (setB 2 false))
        (setB 2 false) ⨾ clr 3 ⨾ clr 4) ⨾ clr 5 ⨾ clr 6) (m + 6 * P + 20) := by
  have hc := ug_seq (ug_clr hPS 3) (ug_clr hPS 4)
  have hc' := ug_seq (ug_clr hPS 5) (ug_clr hPS 6)
  have hB := ug_seq (ug_dropT hPS 3 1 5 (by decide) (by decide) (by simp [gE]) (by simp [gE]))
    (ug_if 3 (ug_setB2 hPS hP true) (ug_setB2 hPS hP false))
  have hC := ug_mono (ug_setB2 hPS hP false) (show 2 ≤ 3 * P + 3 + (2 + 1) by omega)
  have hd := ug_dropT hPS 4 3 5 (by decide) (by decide) (by simp [gE]) (by simp [gE])
  exact ug_mono (ug_seq (ug_seq hA (ug_seq (ug_cp41 hPS) (ug_seq hd (ug_seq (ug_if 4 hB hC) hc)))) hc')
    (by omega)

/-- The scratch tapes `3 … 6` cleared at the end: the length bound drops to `gF`. -/
theorem clr3456_le (ℓ : Fin 247 → ℕ) (hℓ : ℓ ≤ gE S P) :
    Prim.lenT (.clear 6) (Prim.lenT (.clear 5) (Prim.lenT (.clear 4) (Prim.lenT (.clear 3) ℓ)))
      ≤ gF S P := fun u => by
  simp only [Prim.lenT, Function.update_apply]
  split_ifs with h6 h5 h4 h3 <;> try exact Nat.zero_le _
  have hu := hℓ u
  have v6 : u.val ≠ 6 := fun e => h6 (Fin.ext e)
  have v5 : u.val ≠ 5 := fun e => h5 (Fin.ext e)
  have v4 : u.val ≠ 4 := fun e => h4 (Fin.ext e)
  have v3 : u.val ≠ 3 := fun e => h3 (Fin.ext e)
  simp only [gE, gF] at hu ⊢
  split_ifs at hu ⊢ <;> omega

theorem len_leCore (A : SigabaNeo.Tape.Prog 247) (ℓ : Fin 247 → ℕ) :
    Prog.lenBoundT ((A ⨾ cp 4 1 ⨾ Prog.dropT 4 3 5 ⨾ Prog.ifBlank 4 (setB 2 true) (setB 2 false) ⨾
      clr 3 ⨾ clr 4) ⨾ clr 5 ⨾ clr 6) ℓ =
    Prim.lenT (.clear 6) (Prim.lenT (.clear 5) (Prim.lenT (.clear 4) (Prim.lenT (.clear 3)
      (Prog.lenBoundT (A ⨾ cp 4 1 ⨾ Prog.dropT 4 3 5 ⨾
        Prog.ifBlank 4 (setB 2 true) (setB 2 false)) ℓ)))) := rfl

theorem len_eqCore (A : SigabaNeo.Tape.Prog 247) (ℓ : Fin 247 → ℕ) :
    Prog.lenBoundT ((A ⨾ cp 4 1 ⨾ Prog.dropT 4 3 5 ⨾
      Prog.ifBlank 4 (Prog.dropT 3 1 5 ⨾ Prog.ifBlank 3 (setB 2 true) (setB 2 false))
        (setB 2 false) ⨾ clr 3 ⨾ clr 4) ⨾ clr 5 ⨾ clr 6) ℓ =
    Prim.lenT (.clear 6) (Prim.lenT (.clear 5) (Prim.lenT (.clear 4) (Prim.lenT (.clear 3)
      (Prog.lenBoundT (A ⨾ cp 4 1 ⨾ Prog.dropT 4 3 5 ⨾
        Prog.ifBlank 4 (Prog.dropT 3 1 5 ⨾ Prog.ifBlank 3 (setB 2 true) (setB 2 false))
          (setB 2 false)) ℓ)))) := rfl

end Env

/-! ### The tests of `rkKeyPT` -/

theorem predLen_pos : 1 ≤ predLen := by norm_num [predLen]

/-- **The first test**: `gF → gF`. -/
theorem bounds_rkLeChkT {S : ℕ} (hPS : predLen ≤ S) (ℓ : Fin 247 → ℕ) (hℓ : ℓ ≤ gF S predLen) :
    Prog.timeBoundT rkLeChkT ℓ ≤ (20 * predLen + 210) * (2 * S + 5) ∧
      Prog.lenBoundT rkLeChkT ℓ ≤ gF S predLen := by
  have hE := hℓ.trans (gF_le_gE S predLen)
  have hN := ug_natU hPS predLen le_rfl
  have hu := (ug_leCore hPS predLen_pos hN) ℓ hE
  have hc := (ug_seq hN (ug_seq (ug_cp41 hPS) (ug_seq
    (ug_dropT hPS 4 3 5 (by decide) (by decide) (by simp [gE]) (by simp [gE]))
    (ug_if 4 (ug_setB2 hPS predLen_pos true) (ug_setB2 hPS predLen_pos false))))) ℓ hE
  rw [rkLeChkT, rkLeChk_eq]
  refine ⟨hu.1.trans (Nat.mul_le_mul_right _ (by omega)), ?_⟩
  rw [len_leCore]
  exact clr3456_le _ hc.2

/-- **The second test, after `clr 2`**: `gF → gF`. -/
theorem bounds_clrEqChkT {S : ℕ} (hPS : predLen ≤ S) (ℓ : Fin 247 → ℕ) (hℓ : ℓ ≤ gF S predLen) :
    Prog.timeBoundT (clr 2 ⨾ rkEqChkT) ℓ ≤ (20 * predLen + 210) * (2 * S + 5) ∧
      Prog.lenBoundT (clr 2 ⨾ rkEqChkT) ℓ ≤ gF S predLen := by
  have hE := hℓ.trans (gF_le_gE S predLen)
  have h2 := ug_clr hPS 2 ℓ hE
  set ℓ' := Prog.lenBoundT (clr (2 : Fin 247)) ℓ
  have hF : ℓ' ≤ gF S predLen := fun u => by
    show Prim.lenT (.clear 2) ℓ u ≤ _
    simp only [Prim.lenT, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hℓ u
  have hN := ug_natU hPS predLen le_rfl
  have hu := (ug_eqCore hPS predLen_pos hN) ℓ' h2.2
  have hB := ug_seq (ug_dropT hPS 3 1 5 (by decide) (by decide) (by simp [gE]) (by simp [gE]))
    (ug_if 3 (ug_setB2 hPS predLen_pos true) (ug_setB2 hPS predLen_pos false))
  have hC := ug_mono (ug_setB2 hPS predLen_pos false) (show 2 ≤ 3 * predLen + 3 + (2 + 1) by omega)
  have hc := (ug_seq hN (ug_seq (ug_cp41 hPS) (ug_seq
    (ug_dropT hPS 4 3 5 (by decide) (by decide) (by simp [gE]) (by simp [gE]))
    (ug_if 4 hB hC)))) ℓ' h2.2
  rw [rkEqChkT, rkEqChk_eq]
  refine ⟨?_, ?_⟩
  · rw [timeBoundT_seq]
    have := h2.1; have := hu.1
    nlinarith
  · show Prog.lenBoundT _ ℓ' ≤ _
    rw [len_eqCore]
    exact clr3456_le _ hc.2

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
