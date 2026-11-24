import PE.Impl.ExpLUT.Prog.DecLut

/-!
# Segments of the inputs and the step `Mul` on the ring-word machine (Dec, package F4)

* `segC src tmpl dst sc i`: `dst :=` the segment `i` (of the width of the template `tmpl`) of the
  word on `src` (scratch `sc`); `dropsC`: drop `n` widths.
* **`mulC i`**: from `A` (`177`), `c` (`176`) and the inputs of position `i` (`A^in_i` on `62`,
  `a_i` on `60`, the bottom row of `C^in_i` on `69`, `c^in_i` on `70`), `mulPK` on `160` and
  `mulCT` on `161` (registers `120 … 139` scratch).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

/-- Drop `n` widths of `tmpl` from `sc`. -/
def dropsC (sc tmpl : Fin 200) : ℕ → Code
  | 0 => .nop
  | n + 1 => .seq (dropsC sc tmpl n) (.drop sc tmpl)

theorem exec_dropsC (sc tmpl : Fin 200) (h : sc ≠ tmpl) (w : St) :
    ∀ n, exec D.N D.K (dropsC sc tmpl n) w = Function.update w sc ((w sc).drop (n * (w tmpl).length))
  | 0 => by simp [dropsC, exec]
  | n + 1 => by
    show exec D.N D.K (.drop sc tmpl) (exec D.N D.K (dropsC sc tmpl n) w) = _
    rw [exec_dropsC sc tmpl h w n]
    simp only [exec, if_neg h, Function.update_self, Function.update_of_ne (Ne.symm h),
      Function.update_idem, List.drop_drop]
    congr 2; ring

/-- `dst :=` the segment `i` of `src` of the width of `tmpl`. -/
def segC (src tmpl dst sc : Fin 200) (i : ℕ) : Code :=
  ofList [.cp sc src, dropsC sc tmpl i, .cp dst tmpl, .mv dst sc tmpl]

theorem exec_segC (w : St) (src tmpl dst sc : Fin 200) (i : ℕ) (h1 : sc ≠ tmpl) (h2 : dst ≠ sc)
    (h3 : dst ≠ tmpl) (hz : w tmpl = List.replicate (w tmpl).length false)
    (hl : (i + 1) * (w tmpl).length ≤ (w src).length) :
    (exec D.N D.K (segC src tmpl dst sc i) w) dst =
        (((w src).drop (i * (w tmpl).length)).take (w tmpl).length) ∧
      ∀ k, k ≠ dst → k ≠ sc → (exec D.N D.K (segC src tmpl dst sc i) w) k = w k := by
  set m := (w tmpl).length
  set X := (w src).drop (i * m)
  have e1 : exec D.N D.K (dropsC sc tmpl i) (exec D.N D.K (.cp sc src) w) =
      Function.update (Function.update w sc (w src)) sc X := by
    rw [exec_dropsC sc tmpl h1]
    simp [exec, Function.update_of_ne (Ne.symm h1), X, m]
  have hXl : m ≤ X.length := by simp [X, List.length_drop]; rw [Nat.add_mul] at hl; omega
  have hX : X = X.take m ++ X.drop m := (List.take_append_drop _ _).symm
  set u := Function.update (Function.update (Function.update w sc (w src)) sc X) dst (w tmpl)
  have hu : exec D.N D.K (segC src tmpl dst sc i) w = exec D.N D.K (.mv dst sc tmpl) u := by
    show exec D.N D.K (.mv dst sc tmpl) (exec D.N D.K (.cp dst tmpl)
      (exec D.N D.K (dropsC sc tmpl i) (exec D.N D.K (.cp sc src) w))) = _
    rw [e1]
    simp only [exec, u, Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h1)]
  have ut : u tmpl = w tmpl := by
    simp only [u, Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h1)]
  have us : u sc = X := by simp only [u, Function.update_of_ne (Ne.symm h2), Function.update_self]
  rw [hu, exec_mv_shift (v := X.take m) (L := X.drop m)
    (by simp only [not_or]; exact ⟨h2, h3, h1⟩) (by rw [ut, List.length_take]; omega)
    (by rw [us]; exact hX)]
  refine ⟨?_, fun k hk1 hk2 => ?_⟩
  · simp only [Function.update_self, ut, u, Function.update_self]
    rw [hz, List.drop_left' (by simp)]
  · simp only [Function.update_apply, hk1, hk2, ↓reduceIte, u]

/-! ### `Mul` -/

/-- **The step `Mul` at position `i`.** -/
def mulC (i : ℕ) : Code := ofList [
  segC 62 77 120 121 i, deintCall 120 122 123, accCall 177 122 124, accCall 177 123 125,
  joinC 124 125 160, segC 70 10 126 121 i, accCall 177 126 127, segC 60 6 128 121 i,
  segC 69 6 129 121 i, joinC 128 129 130, ginvCall 176 130 131, addCall 127 131 161]

variable (D) in
/-- The inputs of `Mul` at position `i`. -/
structure MulIn (i : ℕ) (w : St) (A : Matrix (Fin 2) (Col D.K) (Rg D)) (c : Col D.K → Rg D)
    (Ain : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)) (cin : Dig D.K → Col D.K → Rg D)
    (a bot : Col D.K → Rg D) : Prop where
  lc : LC D w
  A : ∃ as, w 177 = as.flatten ∧ RepM D as A
  c : ∃ cs, w 176 = cs.flatten ∧ RepV D cs c
  Ain : ∃ f₀ f₁, ((w 62).drop (i * famMLen D)).take (famMLen D) = famMW f₀ f₁ ∧
    (i + 1) * famMLen D ≤ (w 62).length ∧ RepFV D f₀ (fun d => Ain d 0) ∧ RepFV D f₁ (fun d => Ain d 1)
  cin : ∃ fc, ((w 70).drop (i * (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))))).take
      (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))) = famVW fc ∧
    (i + 1) * (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))) ≤ (w 70).length ∧ RepFV D fc cin
  a : ∃ vs, ((w 60).drop (i * (2 * D.K * (D.N * D.K)))).take (2 * D.K * (D.N * D.K)) = vs.flatten ∧
    (i + 1) * (2 * D.K * (D.N * D.K)) ≤ (w 60).length ∧ RepV D vs a
  bot : ∃ vs, ((w 69).drop (i * (2 * D.K * (D.N * D.K)))).take (2 * D.K * (D.N * D.K)) = vs.flatten ∧
    (i + 1) * (2 * D.K * (D.N * D.K)) ≤ (w 69).length ∧ RepV D vs bot

/-- The frame of `Mul`. -/
def MFr (w w' : St) : Prop :=
  ∀ k : Fin 200, (k.val < 80 ∨ (140 ≤ k.val ∧ k.val < 160) ∨ 162 ≤ k.val) → w' k = w k

theorem segFr {w w' : St} {dst sc : Fin 200} (h : ∀ k, k ≠ dst → k ≠ sc → w' k = w k) {k : Fin 200}
    (hk : k.val < 80 ∨ 120 ≤ k.val) (h1 : k ≠ dst) (h2 : k ≠ sc) : w' k = w k := h k h1 h2

set_option maxHeartbeats 4000000 in
/-- **`Mul` on the machine.** -/
theorem exec_mulC (i : ℕ) (w : St) {A : Matrix (Fin 2) (Col D.K) (Rg D)} {c a bot : Col D.K → Rg D}
    {Ain : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)} {cin : Dig D.K → Col D.K → Rg D}
    (h : MulIn D i w A c Ain cin a bot) :
    (∃ as, (exec D.N D.K (mulC i) w) 160 = as.flatten ∧
        RepM D as (fun r j => ∑ ri : Col D.K, (Ain (ri.1, j, ri.2) r ᵥ* (setting D).ginv A) ri)) ∧
      (∃ cs, (exec D.N D.K (mulC i) w) 161 = cs.flatten ∧
        RepV D cs (fun j => (∑ ri : Col D.K, (cin (ri.1, j, ri.2) ᵥ* (setting D).ginv A) ri) +
          (c ᵥ* (setting D).ginv ![a, bot]) j)) ∧
      MFr w (exec D.N D.K (mulC i) w) := by
  have hw := h.lc.ec
  obtain ⟨as, hA0, hA⟩ := h.A
  obtain ⟨cs, hc0, hc⟩ := h.c
  obtain ⟨f₀, f₁, hAin, hAinl, hF₀, hF₁⟩ := h.Ain
  obtain ⟨fc, hcin, hcinl, hfc⟩ := h.cin
  obtain ⟨va, ha, hal, hva⟩ := h.a
  obtain ⟨vb, hb, hbl, hvb⟩ := h.bot
  have z77 : w 77 = List.replicate (w 77).length false := by rw [h.lc.r77]; simp
  have z10 : w 10 = List.replicate (w 10).length false := by rw [hw.r10]; simp
  have z6 : w 6 = List.replicate (w 6).length false := by rw [hw.r6]; simp
  have l77 : (w 77).length = famMLen D := by rw [h.lc.r77, List.length_replicate]
  have l10 : (w 10).length = 2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K)) := by
    rw [hw.r10, List.length_replicate]
  have l6 : (w 6).length = 2 * D.K * (D.N * D.K) := by rw [hw.r6, List.length_replicate]
  -- 1: the family A^in_i on 120, its rows on 122, 123
  obtain ⟨s1, g1⟩ := exec_segC (D := D) w 62 77 120 121 i (by decide) (by decide)
    (by decide) z77 (by rw [l77]; exact hAinl)
  rw [l77, hAin] at s1
  set w1 := exec D.N D.K (segC 62 77 120 121 i) w
  have v1 : ∀ k : Fin 200, (k.val < 80 ∨ 122 ≤ k.val) → w1 k = w k := fun k hk =>
    g1 k (by intro e; subst e; simp at hk) (by intro e; subst e; simp at hk)
  have e1 : EC D w1 := hw.of_agree fun k hk => v1 k (Or.inl hk)
  obtain ⟨d2, d3, f2⟩ := exec_deintCall w1 e1 120 122 123 (by decide) (by decide) hF₀ hF₁ s1
  set w2 := exec D.N D.K (deintCall 120 122 123) w1
  have e2 := EC.of_fr2 e1 f2 (by decide) (by decide)
  -- 2: the rows of mulPK on 124, 125, the matrix on 160
  obtain ⟨r0, a4, q4, f4⟩ := exec_accCall w2 e2 177 122 124 (by decide) hA hF₀
    (by rw [frs2 f2 (by decide), v1 177 (by decide), hA0]) d2
  set w4 := exec D.N D.K (accCall 177 122 124) w2
  have e4 := EC.of_fr e2 f4 (by decide)
  obtain ⟨r1, a5, q5, f5⟩ := exec_accCall w4 e4 177 123 125 (by decide) hA hF₁
    (by rw [frs f4 (by decide), frs2 f2 (by decide), v1 177 (by decide), hA0])
    (by rw [frs f4 (by decide), d3])
  set w5 := exec D.N D.K (accCall 177 123 125) w4
  have e5 := EC.of_fr e4 f5 (by decide)
  obtain ⟨a6, q6, f6⟩ := exec_joinC w5 e5 124 125 160 (by decide) (by decide) (by decide) (by decide)
    (by decide) (M := fun r j => ∑ ri : Col D.K, (Ain (ri.1, j, ri.2) r ᵥ* (setting D).ginv A) ri)
    q4 q5 (by rw [frs f5 (by decide), a4]) a5
  set w6 := exec D.N D.K (joinC 124 125 160) w5
  have e6 := EC.of_fr2 e5 f6 (by decide) (by decide)
  -- 3: the family c^in_i on 126, its Mul sum on 127
  have lo6 : ∀ k : Fin 200, k.val < 80 → w6 k = w k := fun k hk => by
    rw [f6 k (Or.inl hk) (by intro e; subst e; simp at hk) (by intro e; subst e; simp at hk),
      f5 k (Or.inl hk) (by intro e; subst e; simp at hk), f4 k (Or.inl hk) (by intro e; subst e; simp at hk),
      f2 k (Or.inl hk) (by intro e; subst e; simp at hk) (by intro e; subst e; simp at hk), v1 k (Or.inl hk)]
  obtain ⟨s7, g7⟩ := exec_segC (D := D) w6 70 10 126 121 i (by decide) (by decide) (by decide)
    (by rw [lo6 10 (by decide)]; exact z10) (by rw [lo6 10 (by decide), lo6 70 (by decide), l10]; exact hcinl)
  rw [lo6 10 (by decide), lo6 70 (by decide), l10, hcin] at s7
  set w7 := exec D.N D.K (segC 70 10 126 121 i) w6
  have v7 : ∀ k : Fin 200, (k.val < 80 ∨ 127 ≤ k.val ∨ (122 ≤ k.val ∧ k.val < 126)) → w7 k = w6 k :=
    fun k hk => g7 k (by intro e; subst e; simp at hk) (by intro e; subst e; simp at hk)
  have e7 : EC D w7 := e6.of_agree fun k hk => v7 k (Or.inl hk)
  obtain ⟨t8, a8, q8, f8⟩ := exec_accCall w7 e7 177 126 127 (by decide) hA hfc
    (by rw [v7 177 (by decide), frs2 f6 (by decide), frs f5 (by decide), frs f4 (by decide),
      frs2 f2 (by decide), v1 177 (by decide), hA0]) s7
  set w8 := exec D.N D.K (accCall 177 126 127) w7
  have e8 := EC.of_fr e7 f8 (by decide)
  have lo8 : ∀ k : Fin 200, k.val < 80 → w8 k = w k := fun k hk => by
    rw [f8 k (Or.inl hk) (by intro e; subst e; simp at hk), v7 k (Or.inl hk), lo6 k hk]
  -- 4: C^in_i on 130
  obtain ⟨s9, g9⟩ := exec_segC (D := D) w8 60 6 128 121 i (by decide) (by decide) (by decide)
    (by rw [lo8 6 (by decide)]; exact z6) (by rw [lo8 6 (by decide), lo8 60 (by decide), l6]; exact hal)
  rw [lo8 6 (by decide), lo8 60 (by decide), l6, ha] at s9
  set w9 := exec D.N D.K (segC 60 6 128 121 i) w8
  have v9 : ∀ k : Fin 200, k ≠ 128 → k ≠ 121 → w9 k = w8 k := g9
  have e9 : EC D w9 := e8.of_agree fun k hk =>
    v9 k (by intro e; subst e; simp at hk) (by intro e; subst e; simp at hk)
  have lo9 : ∀ k : Fin 200, k.val < 80 → w9 k = w k := fun k hk => by
    rw [v9 k (by intro e; subst e; simp at hk) (by intro e; subst e; simp at hk), lo8 k hk]
  obtain ⟨s10, g10⟩ := exec_segC (D := D) w9 69 6 129 121 i (by decide) (by decide) (by decide)
    (by rw [lo9 6 (by decide)]; exact z6) (by rw [lo9 6 (by decide), lo9 69 (by decide), l6]; exact hbl)
  rw [lo9 6 (by decide), lo9 69 (by decide), l6, hb] at s10
  set w10 := exec D.N D.K (segC 69 6 129 121 i) w9
  have v10 : ∀ k : Fin 200, k ≠ 129 → k ≠ 121 → w10 k = w9 k := g10
  have e10 : EC D w10 := e9.of_agree fun k hk =>
    v10 k (by intro e; subst e; simp at hk) (by intro e; subst e; simp at hk)
  obtain ⟨a11, q11, f11⟩ := exec_joinC w10 e10 128 129 130 (by decide) (by decide) (by decide)
    (by decide) (by decide) (M := ![a, bot]) hva hvb
    (by rw [v10 128 (by decide) (by decide), s9]) s10
  set w11 := exec D.N D.K (joinC 128 129 130) w10
  have e11 := EC.of_fr2 e10 f11 (by decide) (by decide)
  -- 5: c G⁻¹(C^in_i) on 131, the sum on 161
  have c176 : w11 176 = cs.flatten := by
    rw [frs2 f11 (by decide), v10 176 (by decide) (by decide), v9 176 (by decide) (by decide),
      frs f8 (by decide), v7 176 (by decide), frs2 f6 (by decide), frs f5 (by decide),
      frs f4 (by decide), frs2 f2 (by decide), v1 176 (by decide), hc0]
  obtain ⟨t12, a12, q12, f12⟩ := exec_ginvCall w11 e11 176 130 131 (by decide) hc q11 c176 a11
  set w12 := exec D.N D.K (ginvCall 176 130 131) w11
  have e12 := EC.of_fr e11 f12 (by decide)
  have c127 : w12 127 = t8.flatten := by
    rw [frs f12 (by decide), frs2 f11 (by decide), v10 127 (by decide) (by decide),
      v9 127 (by decide) (by decide), a8]
  obtain ⟨a13, q13, f13⟩ := exec_addCall w12 e12 127 131 161 (by decide) q8 q12 c127 a12
  set w13 := exec D.N D.K (addCall 127 131 161) w12
  have e : exec D.N D.K (mulC i) w = w13 := rfl
  have bk : ∀ k : Fin 200, (k.val < 80 ∨ (140 ≤ k.val ∧ k.val < 160) ∨ 162 ≤ k.val) → w13 k = w k :=
    fun k hk => by
      have hk' : k.val < 80 ∨ 120 ≤ k.val := by omega
      have n : ∀ d : Fin 200, ((120 ≤ d.val ∧ d.val < 140) ∨ d.val = 160 ∨ d.val = 161) → k ≠ d :=
        fun d hd e => by subst e; omega
      rw [f13 k hk' (n 161 (by decide)), f12 k hk' (n 131 (by decide)),
        f11 k hk' (n 130 (by decide)) (n 139 (by decide)), v10 k (n 129 (by decide)) (n 121 (by decide)),
        v9 k (n 128 (by decide)) (n 121 (by decide)), f8 k hk' (n 127 (by decide)),
        g7 k (n 126 (by decide)) (n 121 (by decide)), f6 k hk' (n 160 (by decide)) (n 139 (by decide)),
        f5 k hk' (n 125 (by decide)), f4 k hk' (n 124 (by decide)),
        f2 k hk' (n 122 (by decide)) (n 123 (by decide)), g1 k (n 120 (by decide)) (n 121 (by decide))]
  refine ⟨⟨_, ?_, q6⟩, ⟨_, by rw [e, a13], q13.congr fun j => rfl⟩, fun k hk => by rw [e]; exact bk k hk⟩
  rw [e, frs f13 (by decide), frs f12 (by decide), frs2 f11 (by decide),
    v10 160 (by decide) (by decide), v9 160 (by decide) (by decide), frs f8 (by decide),
    v7 160 (by decide), a6]

end AdvancedEncryption.ExpLUT.Prog
