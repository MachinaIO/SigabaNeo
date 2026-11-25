import PE.Impl.ExpLUT.Prog.RedSetup
import PE.Impl.ExpLUT.Prog.RedSetupPUC
import PE.Impl.DualUse.Prog.Blocks

/-!
# The setup component of the reduction with its bounds (package G2, item 2)

`redSetupP D e` (`Prog/RedSetup`) maps the state word of an instance and the attribute bits to the
word of a raw secret, but leaves the scratch tapes' *static* length bounds positive. Here:

* `redSetupC D e := redSetupP D e ⨾ clearL scr40` (clear the tapes `1 … 39`; they are blank
  already, so the law is unchanged, **`law_redSetupC`**), and the component
  **`setupRX D hR e := liftP hR (redSetupC D e) : XProg (R + 2)`** for `38 ≤ R`, with
  **`law_setupRX`** (the `law_setup` field of `RawComps` at `χfl = floodR D e`), **`wf_setupRX`**,
  `ok_setupRX` (for `Ok := fun _ => True`);
* the per-tape bounds (`VB`): the prefix (`vb_rsPre`), the uniform words (`vb_unifCanonP'`), the
  flooding words and the programming bits (`vb_smp` with the shape bounds `bFl`, `bZr`), the final
  clear; **`vb_redSetupC`**, and on `R + 2` tapes **`time_setupRX`** (`≤ rsT …`) and
  **`len_setupRX`** (`≤ io2 (rsL …) 0 0`), for inputs `io2 a b 0` with `a ≤ X`, `b ≤ 128`, any
  scratch bound `S ≥ X + 128` large enough for the samplers' counts.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Cslib Cslib.Probability
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### The program -/

/-- The tapes `1 … 39`. -/
def scr40 : List (Fin 40) := (List.finRange 40).filter fun t => t ≠ 0

theorem mem_scr40 (t : Fin 40) : t ∈ scr40 ↔ t ≠ 0 := by simp [scr40]

theorem length_scr40 : scr40.length = 39 := by decide

variable (D : Dims)

/-- **The setup component with its scratch cleared** (`40` tapes). -/
noncomputable def redSetupC (e : ℕ) : XProg 40 := seq (redSetupP D e) (clearL scr40)

variable {D}

theorem io2_apply {R : ℕ} {α : Type} (a b d : α) (t : Fin (R + 2)) :
    io2 (R := R) a b d t = if t.val = 0 then a else if t.val = 1 then b else d := rfl

theorem clear_io2 (w : List Bool) :
    (fun t => if t ∈ scr40 then [] else io2 (R := 38) w [] [] t) = io2 (R := 38) w [] [] := by
  funext t
  by_cases ht : t = 0
  · subst ht; simp [mem_scr40]
  · have h1 : t.val ≠ 0 := fun h => ht (Fin.ext h)
    simp only [mem_scr40, ne_eq, ht, not_false_eq_true, ite_true, io2_apply, h1, ite_false]
    split_ifs <;> rfl

theorem bind_clear {α : Type} (μ : PMF α) (f : α → List Bool) :
    (μ.map fun σ => io2 (R := 38) (f σ) [] []).bind (clearL scr40).law =
      μ.map fun σ => io2 (R := 38) (f σ) [] [] := by
  rw [PMF.bind_map]
  simp only [Function.comp_def, law_clearL, clear_io2]
  rfl

/-- **The law of the cleared setup component.** -/
theorem law_redSetupC {e : ℕ} (he : e < D.K) (i : CInst D) (x : Attribute w8) :
    (redSetupC D e).law (io2 (R := 38) (dwR D (enc D i)) (encAttribute w8 x) []) =
      (rawSetup D (floodR D e) i x).map fun σ => io2 (R := 38) ((rawEnc D).enc σ) [] [] := by
  rw [redSetupC, law_seq, law_redSetupP he]
  exact bind_clear _ _

theorem wf_redSetupC (e : ℕ) : (redSetupC D e).WF := ⟨wf_redSetupP e, wf_clearL _⟩

/-! ### The component on `R + 2` tapes -/

variable (D) in
/-- **The setup component of the reduction** on `R + 2` tapes (`38 ≤ R`). -/
noncomputable def setupRX {R : ℕ} (hR : 38 ≤ R) (e : ℕ) : XProg (R + 2) :=
  liftP hR (redSetupC D e)

/-- **The law of the setup component** (the `law_setup` field of `RawComps` at
`χfl = floodR D e`). -/
theorem law_setupRX {R : ℕ} (hR : 38 ≤ R) {e : ℕ} (he : e < D.K) (w : List Bool)
    (x : Attribute w8) (hw : IWR D w) :
    (setupRX D hR e).law (io2 (R := R) w (encAttribute w8 x) []) =
      (setupR D (rawSetup D (floodR D e)) (instR D) w x).map
        fun σ => io2 (R := R) ((rawEnc D).enc σ) [] [] := by
  obtain ⟨i, rfl⟩ := hw
  rw [setupR, instR_dwR]
  exact law_liftP_map hR (law_redSetupC he i x)

theorem wf_setupRX {R : ℕ} (hR : 38 ≤ R) (e : ℕ) : (setupRX D hR e).WF :=
  wf_liftP hR (wf_redSetupC e)

variable (D) in
/-- The `ok_setup` field for the trivial admissibility predicate. -/
theorem ok_setupRX (χfl : PMF (Rg D)) (w : List Bool) (x : Attribute w8) (_ : IWR D w) :
    ∀ σ ∈ (setupR D (rawSetup D χfl) (instR D) w x).support, (fun _ => True) σ :=
  fun _ _ => trivial

/-! ### The prefix -/

/-- The time of the prefix from tapes at most `M`. -/
def preT (M : ℕ) : ℕ := (2 * M + 3) + 2 * (128 * (6 * (M + 2 * 128) + 13) + 2 * (M + 2 * 128) + 3)

/-- **The prefix**: drop the marker, prepend the `≤ 128` attribute bits. -/
theorem vb_rsPre (X Y : ℕ) (hY : Y ≤ 128) :
    VB (prog rsPre) (io2 (R := 38) X Y 0) (preT (X + 128)) (io2 (R := 38) (X + 128) 0 0) := by
  intro ℓ hℓ
  have hle : ∀ t, ℓ t ≤ X + 128 := fun t => (hℓ t).trans (by
    simp only [io2_apply]; split_ifs <;> omega)
  have hs := supB_le_of hle
  set ℓ1 := (Prim.tail (0 : Fin 40)).lenT ℓ with hℓ1
  have hle1 : ∀ t, ℓ1 t ≤ X + 128 := fun t => by
    simp only [hℓ1, Prim.lenT, Function.update_apply]; split_ifs
    · subst_vars; have := hle 0; omega
    · exact hle t
  constructor
  · show 2 * (supB ℓ + 0) + 3 + Prog.timeBoundT (Prog.prependN 128 1 0 2 3) ℓ1 ≤ _
    have h1 := Prog.timeBoundT_le_timeBound (Prog.prependN 128 (1 : Fin 40) 0 2 3) ℓ1
    have h2 := Prog.timeBound_prependN_le (src := (1 : Fin 40)) (dst := 0) (t₁ := 2) (t₂ := 3) 128
      (supB ℓ1)
    have hs1 := supB_le_of hle1
    unfold preT
    omega
  · show Prog.lenBoundT (Prog.prependN 128 1 0 2 3) ℓ1 ≤ _
    refine (Prog.lenBoundT_prependN_le 128 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) ℓ1).trans fun t => ?_
    have h0 := hℓ 0
    have h1 := hℓ 1
    have ht := hℓ t
    simp only [io2_apply] at h0 h1 ht ⊢
    simp only [hℓ1, Prim.lenT, Function.update_apply]
    split_ifs at h0 h1 ht ⊢ <;> simp_all <;> omega

/-! ### The samplers' shape bounds -/

variable (D) in
/-- The shape bound of the flooding words (`nFl N` coefficients of `e` fair bits, zero-padded). -/
def bFl (e : ℕ) : Bnd := (bEntF D.K e).count (nFl D * D.N)

variable (D) in
/-- The shape bound of the programming bits. -/
noncomputable def bZr : Bnd := bCoins (nZ D)

/-! ### The whole component -/

variable (D) in
/-- The uniform words' bits. -/
abbrev mU : ℕ := nU D * (D.N * D.K)

variable (D) in
/-- The output bound: scratch bound, then the appended words. -/
noncomputable def rsL (e S : ℕ) : ℕ := S + mU D + (bFl D e).a + (bZr D).a

variable (D) in
/-- The final bound on every tape before the clear. -/
noncomputable def rsM (e S : ℕ) : ℕ := S + D.K + mU D + (bFl D e).s + (bFl D e).a + (bZr D).s +
  (bZr D).a

variable (D) in
/-- **The time of the setup component** from an input word of at most `X` bits, scratch bound
`S`. -/
noncomputable def rsT (e X S : ℕ) : ℕ :=
  preT (X + 128) + ((ucT' D.N D.K (nU D) S + ((bFl D e).T (S + mU D) (S + D.K + mU D) +
    (bZr D).T (S + mU D + (bFl D e).a) (S + D.K + mU D + (bFl D e).s))) +
    (39 * (2 * (rsM D e S + 1) + 3) + (2 * (rsM D e S + 1) + 3)))

/-- The hypotheses on the scratch bound. -/
structure RsHyp (D : Dims) (e X S : ℕ) : Prop where
  hX : X + 128 ≤ S
  hU : mU D ≤ S
  hK : D.K ≤ S
  hL : nU D * D.N ≤ S
  hF : (bFl D e).S₀ ≤ S + D.K + mU D
  hZ : (bZr D).S₀ ≤ S + D.K + mU D + (bFl D e).s

theorem e7_val (j : Fin 7) : (e7 j).val = j.val := rfl

set_option maxHeartbeats 2000000 in
/-- **The per-tape bound of the cleared setup component.** -/
theorem vb_redSetupC (e X Y S : ℕ) (hY : Y ≤ 128) (h : RsHyp D e X S) :
    VB (redSetupC D e) (io2 (R := 38) X Y 0) (rsT D e X S) (io2 (R := 38) (rsL D e S) 0 0) := by
  obtain ⟨hX, hU, hK, hL, hF, hZ⟩ := h
  have s0 := vb_rsPre X Y hY
  have s1 := vb_unifCanonP' D.N D.K (nU D) S hU hK hL (by omega)
  have e01 : io2 (R := 38) (X + 128) 0 0 ≤ ucIn' S := fun t => by
    simp only [io2_apply, ucIn']; split_ifs <;> omega
  -- the flooding words
  let c1 : Fin 40 → ℕ := fun j => if j.val = 0 then S + mU D + (bFl D e).a else S + D.K + mU D + (bFl D e).s
  have s2 : VB (frame e7 (repF (nFl D * D.N) (entF D.K e))) (ucOut' S D.K (mU D))
      ((bFl D e).T (S + mU D) (S + D.K + mU D)) c1 := by
    refine vb_smp e7 (atbb_repF (atbb_entF D.K e) (preserves6_entF _ _) _) (x := S + mU D)
      (S := S + D.K + mU D) ?_ ?_ hF ?_ ?_ ?_
    · exact le_of_eq rfl
    · intro j hj
      have : (e7 j).val ≠ 0 := by rw [e7_val]; exact fun h => hj (Fin.ext h)
      simp only [ucOut', this, ite_false]; split_ifs <;> omega
    · exact le_of_eq rfl
    · intro j hj
      have : (e7 j).val ≠ 0 := by rw [e7_val]; exact fun h => hj (Fin.ext h)
      simp only [c1, this, ite_false]; exact le_rfl
    · intro t; simp only [ucOut', c1]; split_ifs <;> omega
  -- the programming bits
  let c2 : Fin 40 → ℕ := fun j => if j.val = 0 then S + mU D + (bFl D e).a + (bZr D).a else
    S + D.K + mU D + (bFl D e).s + (bZr D).s
  have s3 : VB (frame e7 (coinsF (nZ D))) c1
      ((bZr D).T (S + mU D + (bFl D e).a) (S + D.K + mU D + (bFl D e).s)) c2 := by
    refine vb_smp e7 (atbb_coinsF (nZ D)) (x := S + mU D + (bFl D e).a)
      (S := S + D.K + mU D + (bFl D e).s) ?_ ?_ hZ ?_ ?_ ?_
    · exact le_of_eq rfl
    · intro j hj
      have : (e7 j).val ≠ 0 := by rw [e7_val]; exact fun h => hj (Fin.ext h)
      simp only [c1, this, ite_false]; exact le_rfl
    · exact le_of_eq rfl
    · intro j hj
      have : (e7 j).val ≠ 0 := by rw [e7_val]; exact fun h => hj (Fin.ext h)
      simp only [c2, this, ite_false]; exact le_rfl
    · intro t; simp only [c1, c2]; split_ifs <;> omega
  -- the clear
  have hM : ∀ t, c2 t ≤ rsM D e S := fun t => by
    simp only [c2, rsM]; split_ifs <;> omega
  have s4 := vb_clearL scr40 hM
  rw [length_scr40] at s4
  have eout : (fun t => if t ∈ scr40 then 0 else c2 t) ≤ io2 (R := 38) (rsL D e S) 0 0 := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp [mem_scr40, c2, io2_apply, rsL]
    · have h1 : t.val ≠ 0 := fun h => ht (Fin.ext h)
      simp only [mem_scr40, ne_eq, ht, not_false_eq_true, ite_true]
      exact Nat.zero_le _
  have := (s0.seq ((s1.mono e01 le_rfl le_rfl).seq (s2.seq s3))).seq s4
  unfold redSetupC redSetupP rsSmp
  refine (this.mono le_rfl (le_of_eq ?_) eout)
  unfold rsT
  omega

/-- **The time of the setup component** on `R + 2` tapes. -/
theorem time_setupRX {R : ℕ} (hR : 38 ≤ R) (e X S : ℕ) {a b : ℕ} (ha : a ≤ X) (hb : b ≤ 128)
    (h : RsHyp D e X S) :
    XProg.timeBoundT (setupRX D hR e) (io2 (R := R) a b 0) ≤ rsT D e X S := by
  rw [setupRX, timeBoundT_liftP]
  refine (vb_redSetupC e X b S hb h _ fun t => ?_).1
  simp only [io2_apply]; split_ifs <;> omega

/-- **The output length of the setup component** on `R + 2` tapes. -/
theorem len_setupRX {R : ℕ} (hR : 38 ≤ R) (e X S : ℕ) {a b : ℕ} (ha : a ≤ X) (hb : b ≤ 128)
    (h : RsHyp D e X S) :
    XProg.lenBoundT (setupRX D hR e) (io2 (R := R) a b 0) ≤ io2 (R := R) (rsL D e S) 0 0 := by
  refine lenBoundT_liftP_le hR _ ?_
  refine (vb_redSetupC e X b S hb h _ fun t => ?_).2
  simp only [io2_apply]; split_ifs <;> omega

end AdvancedEncryption.ExpLUT.Prog
