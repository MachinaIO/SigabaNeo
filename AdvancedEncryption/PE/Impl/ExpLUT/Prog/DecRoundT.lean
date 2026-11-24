import PE.Impl.ExpLUT.Prog.DecRound

/-!
# One round `Aut_{g_t}` on the ring-word machine (Dec, package F4)

**`exec_roundC`**: from `A` (`120`), `c` (`121`), `H_{g_t}` (`122`), `H_{g_t^{-1}}` (`123`),
`h_{g_t}` (`124`), `h_{g_t^{-1}}` (`125`), the family `A^aut_t` (`126`, matrices) and `c^aut_t`
(`127`, vectors), `roundC t` leaves `autPK` on `120` and `autCT` on `121` (the pair `autStep`
of `DecAlg`); the registers outside `[80, 140)` and `122 … 127` are unchanged.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

/-- **One round** `Aut_{g_t}`. -/
def roundC (t : ℕ) : Code := ofList [
  autCall t 120 128 76 7, autCall t 121 129 8 6, deintCall 126 130 131,
  accCall 128 130 132, accCall 128 131 133, joinC 132 133 134, matCall 122 134 135,
  autCall t 123 136 76 7, autCall t 125 137 8 6, row1C 136 138, subCall 138 137 137,
  row0C 136 138, joinC 138 137 136, ginvCall 124 134 130, accCall 128 127 131,
  ginvCall 129 136 132, addCall 131 132 133, addCall 130 133 121, .cp 120 135]

/-- The inputs of a round. -/
structure RoundIn (D : Dims) (w : St) (A : Matrix (Fin 2) (Col D.K) (Rg D)) (c : Col D.K → Rg D)
    (Hf Hi : Matrix (Fin 2) (Col D.K) (Rg D)) (hf hi : Col D.K → Rg D)
    (Aaut : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)) (caut : Dig D.K → Col D.K → Rg D) : Prop where
  ec : EC D w
  A : ∃ as, w 120 = as.flatten ∧ RepM D as A
  c : ∃ cs, w 121 = cs.flatten ∧ RepV D cs c
  Hf : ∃ ms, w 122 = ms.flatten ∧ RepM D ms Hf
  Hi : ∃ ms, w 123 = ms.flatten ∧ RepM D ms Hi
  hf : ∃ vs, w 124 = vs.flatten ∧ RepV D vs hf
  hi : ∃ vs, w 125 = vs.flatten ∧ RepV D vs hi
  Aaut : ∃ f₀ f₁, w 126 = (List.zipWith (· ++ ·) (f₀.map List.flatten) (f₁.map List.flatten)).flatten ∧
    RepFV D f₀ (fun d => Aaut d 0) ∧ RepFV D f₁ (fun d => Aaut d 1)
  caut : ∃ fc, w 127 = (fc.map List.flatten).flatten ∧ RepFV D fc caut

/-- The frame of a round. -/
def RFr (w w' : St) : Prop :=
  ∀ j : Fin 200, (j.val < 80 ∨ 140 ≤ j.val ∨ (122 ≤ j.val ∧ j.val < 128)) → w' j = w j

theorem frs {dst : Fin 200} {w w' : St} (h : Fr dst w w') {j : Fin 200} (hj : 120 ≤ j.val)
    (hd : j ≠ dst := by decide) : w' j = w j := h j (Or.inr hj) hd

theorem frl {dst : Fin 200} {w w' : St} (h : Fr dst w w') {j : Fin 200} (hj : j.val < 80)
    (hd : j ≠ dst) : w' j = w j := h j (Or.inl hj) hd

theorem frs2 {d₁ d₂ : Fin 200} {w w' : St} (h : Fr2 d₁ d₂ w w') {j : Fin 200} (hj : 120 ≤ j.val)
    (h1 : j ≠ d₁ := by decide) (h2 : j ≠ d₂ := by decide) : w' j = w j := h j (Or.inr hj) h1 h2

theorem EC.of_fr2 {d₁ d₂ : Fin 200} {w w' : St} (hw : EC D w) (h : Fr2 d₁ d₂ w w')
    (h1 : 80 ≤ d₁.val) (h2 : 80 ≤ d₂.val) : EC D w' :=
  hw.of_agree fun j hj => h j (Or.inl hj) (by intro e; subst e; omega) (by intro e; subst e; omega)

theorem ne_of_lt80 {j d : Fin 200} (hj : j.val < 80 ∨ 140 ≤ j.val ∨ (122 ≤ j.val ∧ j.val < 128))
    (hd : (120 ≤ d.val ∧ d.val < 122) ∨ (128 ≤ d.val ∧ d.val < 140)) : j ≠ d := by
  intro e; subst e; omega

theorem rfr_of {dst : Fin 200} {w w' : St} (h : Fr dst w w') {j : Fin 200}
    (hj : j.val < 80 ∨ 140 ≤ j.val ∨ (122 ≤ j.val ∧ j.val < 128))
    (hd : (120 ≤ dst.val ∧ dst.val < 122) ∨ (128 ≤ dst.val ∧ dst.val < 140)) : w' j = w j :=
  h j (by omega) (ne_of_lt80 hj hd)

theorem rfr_of2 {d₁ d₂ : Fin 200} {w w' : St} (h : Fr2 d₁ d₂ w w') {j : Fin 200}
    (hj : j.val < 80 ∨ 140 ≤ j.val ∨ (122 ≤ j.val ∧ j.val < 128))
    (hd₁ : (120 ≤ d₁.val ∧ d₁.val < 122) ∨ (128 ≤ d₁.val ∧ d₁.val < 140))
    (hd₂ : (120 ≤ d₂.val ∧ d₂.val < 122) ∨ (128 ≤ d₂.val ∧ d₂.val < 140)) : w' j = w j :=
  h j (by omega) (ne_of_lt80 hj hd₁) (ne_of_lt80 hj hd₂)

section Round

variable (t : ℕ)

/-- `σ_{g_t}`. -/
noncomputable abbrev sg (a : Rg D) : Rg D := (setting D).E.σ ((setting D).kf t) a

/-- The matrix `A'_k = mulPK(σ(A), A^aut)` of a round. -/
noncomputable def midM (A : Matrix (Fin 2) (Col D.K) (Rg D))
    (Aaut : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)) : Matrix (Fin 2) (Col D.K) (Rg D) :=
  fun a j => ∑ ri : Col D.K, (Aaut (ri.1, j, ri.2) a ᵥ* (setting D).ginv (fun a c => sg t (A a c))) ri

/-- The gadget ciphertext `C_{g_t}` of a round. -/
noncomputable def cgM (Hi : Matrix (Fin 2) (Col D.K) (Rg D)) (hi : Col D.K → Rg D) :
    Matrix (Fin 2) (Col D.K) (Rg D) :=
  ![fun j => sg t (Hi 0 j), (fun j => sg t (Hi 1 j)) - fun j => sg t (hi j)]

/-- The new encoding of a round. -/
noncomputable def cNew (A : Matrix (Fin 2) (Col D.K) (Rg D)) (c : Col D.K → Rg D)
    (Hi : Matrix (Fin 2) (Col D.K) (Rg D)) (hf hi : Col D.K → Rg D)
    (Aaut : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)) (caut : Dig D.K → Col D.K → Rg D) :
    Col D.K → Rg D := fun j =>
  (hf ᵥ* (setting D).ginv (midM t A Aaut)) j +
    ((∑ ri : Col D.K, (caut (ri.1, j, ri.2) ᵥ* (setting D).ginv (fun a c => sg t (A a c))) ri) +
      ((fun j => sg t (c j)) ᵥ* (setting D).ginv (cgM t Hi hi)) j)

end Round

theorem midM_eq (t : ℕ) (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Aaut : Dig (setting D).τ → Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    midM t A Aaut = autMid (setting D) ((setting D).kf t) Aaut A := by
  funext a j
  simp only [autMid, mulPK_eq]
  rfl

theorem cgM_eq (t : ℕ) (Hi : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (hi : Col (setting D).τ → Rg D) :
    cgM t Hi hi = gcAut (setting D) ((setting D).kf t) Hi hi := by
  funext a j
  fin_cases a
  · show _ = (setting D).E.σ ((setting D).kf t) (Hi 0 j) -
      if (0 : Fin 2) = 1 then (setting D).E.σ ((setting D).kf t) (hi j) else 0
    simp [cgM, sg]
  · show _ = (setting D).E.σ ((setting D).kf t) (Hi 1 j) -
      if (1 : Fin 2) = 1 then (setting D).E.σ ((setting D).kf t) (hi j) else 0
    simp [cgM, sg]

/-- The public matrix of a round is `autPK`. -/
theorem roundPK_eq (t : ℕ) (A Hf : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Aaut : Dig (setting D).τ → Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (a : Fin 2)
    (c : Col (setting D).τ) :
    (Hf a ᵥ* (setting D).ginv (midM t A Aaut)) c =
      autPK (setting D) ((setting D).kf t) Hf Aaut A a c := by
  rw [autPK_row, midM_eq]

/-- The encoding of a round is `autCT`. -/
theorem roundCT_eq (t : ℕ) (A Hi : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (c hf hi : Col (setting D).τ → Rg D)
    (Aaut : Dig (setting D).τ → Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (caut : Dig (setting D).τ → Col (setting D).τ → Rg D) (j : Col (setting D).τ) :
    cNew t A c Hi hf hi Aaut caut j =
      autCT (setting D) ((setting D).kf t) Hi Aaut A hf hi caut c j := by
  rw [autCT_eq]
  unfold cNew
  rw [midM_eq, cgM_eq]
  rfl

theorem RepV.congr {vs : List (List Bool)} {v v' : Col D.K → Rg D} (h : RepV D vs v)
    (e : ∀ c, v c = v' c) : RepV D vs v' := ⟨h.len, h.wid, fun c => (h.val c).trans (e c)⟩

theorem RepM.congr {ms : List (List Bool)} {M M' : Matrix (Fin 2) (Col D.K) (Rg D)} (h : RepM D ms M)
    (e : ∀ a c, M a c = M' a c) : RepM D ms M' := ⟨h.len, h.wid, fun a c => (h.val a c).trans (e a c)⟩

set_option maxHeartbeats 4000000 in
/-- **One round on the machine.** -/
theorem exec_roundC (t : ℕ) (ht : t < 22) (w : St) {A Hf Hi : Matrix (Fin 2) (Col D.K) (Rg D)}
    {c hf hi : Col D.K → Rg D} {Aaut : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)}
    {caut : Dig D.K → Col D.K → Rg D} (h : RoundIn D w A c Hf Hi hf hi Aaut caut) :
    (∃ as, (exec D.N D.K (roundC t) w) 120 = as.flatten ∧
        RepM D as (fun a => Hf a ᵥ* (setting D).ginv (midM t A Aaut))) ∧
      (∃ cs, (exec D.N D.K (roundC t) w) 121 = cs.flatten ∧
        RepV D cs (cNew t A c Hi hf hi Aaut caut)) ∧
      RFr w (exec D.N D.K (roundC t) w) := by
  have hw := h.ec
  obtain ⟨as, hA0, hA⟩ := h.A
  obtain ⟨cs, hc0, hc⟩ := h.c
  obtain ⟨Hfs, hHf0, hHf⟩ := h.Hf
  obtain ⟨His, hHi0, hHi⟩ := h.Hi
  obtain ⟨hfs, hhf0, hhf⟩ := h.hf
  obtain ⟨his, hhi0, hhi⟩ := h.hi
  obtain ⟨f₀, f₁, hF0, hF₀, hF₁⟩ := h.Aaut
  obtain ⟨fc, hfc0, hfc⟩ := h.caut
  have l76 : ∀ w' : St, EC D w' → (w' 76).length = 4 * D.K := fun w' h' => by
    rw [h'.r76, List.length_replicate]
  have l7 : ∀ w' : St, EC D w' → (w' 7).length = 4 * D.K * (D.N * D.K) := fun w' h' => by
    rw [h'.ck.mat, List.length_replicate]
  have l8 : ∀ w' : St, EC D w' → (w' 8).length = 2 * D.K := fun w' h' => by
    rw [h'.r8, List.length_replicate]
  have l6 : ∀ w' : St, EC D w' → (w' 6).length = 2 * D.K * (D.N * D.K) := fun w' h' => by
    rw [h'.r6, List.length_replicate]
  -- 1: σ(A) on 128
  obtain ⟨a1, f1⟩ := exec_autCall w hw t ht 120 128 76 7 (by decide) (by decide) hA.wid hA0
    (by rw [l76 w hw, hA.len]) (by rw [l7 w hw, hA.len])
  set w1 := exec D.N D.K (autCall t 120 128 76 7) w
  have e1 := EC.of_fr hw f1 (by decide)
  have rA' := hA.map_aut t
  -- 2: σ(c) on 129
  obtain ⟨a2, f2⟩ := exec_autCall w1 e1 t ht 121 129 8 6 (by decide) (by decide) hc.wid
    (by rw [frs f1 (by decide), hc0]) (by rw [l8 w1 e1, hc.len]) (by rw [l6 w1 e1, hc.len])
  set w2 := exec D.N D.K (autCall t 121 129 8 6) w1
  have e2 := EC.of_fr e1 f2 (by decide)
  have rc' := hc.map_aut t
  -- 3: the rows of A^aut on 130, 131
  obtain ⟨a3, b3, f3⟩ := exec_deintCall w2 e2 126 130 131 (by decide) (by decide) hF₀ hF₁
    (by rw [frs f2 (by decide), frs f1 (by decide), hF0])
  set w3 := exec D.N D.K (deintCall 126 130 131) w2
  have e3 := EC.of_fr2 e2 f3 (by decide) (by decide)
  -- 4, 5: the rows of the middle matrix on 132, 133
  obtain ⟨m0, a4, r4, f4⟩ := exec_accCall w3 e3 128 130 132 (by decide) rA' hF₀
    (by rw [frs2 f3 (by decide), frs f2 (by decide), a1]) a3
  set w4 := exec D.N D.K (accCall 128 130 132) w3
  have e4 := EC.of_fr e3 f4 (by decide)
  obtain ⟨m1, a5, r5, f5⟩ := exec_accCall w4 e4 128 131 133 (by decide) rA' hF₁
    (by rw [frs f4 (by decide), frs2 f3 (by decide), frs f2 (by decide), a1])
    (by rw [frs f4 (by decide), b3])
  set w5 := exec D.N D.K (accCall 128 131 133) w4
  have e5 := EC.of_fr e4 f5 (by decide)
  -- 6: the middle matrix on 134
  obtain ⟨a6, r6, f6⟩ := exec_joinC w5 e5 132 133 134 (by decide) (by decide) (by decide) (by decide)
    (by decide) (M := midM t A Aaut) r4 r5 (by rw [frs f5 (by decide), a4]) a5
  set w6 := exec D.N D.K (joinC 132 133 134) w5
  have e6 := EC.of_fr2 e5 f6 (by decide) (by decide)
  -- 7: the new public matrix on 135
  obtain ⟨an, a7, r7, f7⟩ := exec_matCall w6 e6 122 134 135 (by decide) hHf r6
    (by rw [frs2 f6 (by decide), frs f5 (by decide), frs f4 (by decide), frs2 f3 (by decide),
      frs f2 (by decide), frs f1 (by decide), hHf0]) a6
  set w7 := exec D.N D.K (matCall 122 134 135) w6
  have e7 := EC.of_fr e6 f7 (by decide)
  -- 8, 9: σ(H_{g_t^{-1}}) on 136, σ(h_{g_t^{-1}}) on 137
  obtain ⟨a8, f8⟩ := exec_autCall w7 e7 t ht 123 136 76 7 (by decide) (by decide) hHi.wid
    (by rw [frs f7 (by decide), frs2 f6 (by decide), frs f5 (by decide), frs f4 (by decide),
      frs2 f3 (by decide), frs f2 (by decide), frs f1 (by decide), hHi0])
    (by rw [l76 w7 e7, hHi.len]) (by rw [l7 w7 e7, hHi.len])
  set w8 := exec D.N D.K (autCall t 123 136 76 7) w7
  have e8 := EC.of_fr e7 f8 (by decide)
  have rHi' := hHi.map_aut t
  obtain ⟨a9, f9⟩ := exec_autCall w8 e8 t ht 125 137 8 6 (by decide) (by decide) hhi.wid
    (by rw [frs f8 (by decide), frs f7 (by decide), frs2 f6 (by decide), frs f5 (by decide),
      frs f4 (by decide), frs2 f3 (by decide), frs f2 (by decide), frs f1 (by decide), hhi0])
    (by rw [l8 w8 e8, hhi.len]) (by rw [l6 w8 e8, hhi.len])
  set w9 := exec D.N D.K (autCall t 125 137 8 6) w8
  have e9 := EC.of_fr e8 f9 (by decide)
  have rhi' := hhi.map_aut t
  -- 10, 11: row 1 of C_{g_t} on 137
  obtain ⟨a10, f10⟩ := exec_row1C w9 e9 136 138 (by decide) rHi' (by rw [frs f9 (by decide), a8])
  set w10 := exec D.N D.K (row1C 136 138) w9
  have e10 := EC.of_fr e9 f10 (by decide)
  obtain ⟨a11, r11, f11⟩ := exec_subCall w10 e10 138 137 137 (by decide) rHi'.row₁ rhi' a10
    (by rw [frs f10 (by decide), a9])
  set w11 := exec D.N D.K (subCall 138 137 137) w10
  have e11 := EC.of_fr e10 f11 (by decide)
  -- 12, 13: C_{g_t} on 136
  obtain ⟨a12, f12⟩ := exec_row0C w11 e11 136 138 (by decide) (by decide) (by decide) rHi'
    (by rw [frs f11 (by decide), frs f10 (by decide), frs f9 (by decide), a8])
  set w12 := exec D.N D.K (row0C 136 138) w11
  have e12 := EC.of_fr2 e11 f12 (by decide) (by decide)
  obtain ⟨a13, r13, f13⟩ := exec_joinC w12 e12 138 137 136 (by decide) (by decide) (by decide)
    (by decide) (by decide) (M := cgM t Hi hi) rHi'.row₀ r11 a12
    (by rw [frs2 f12 (by decide), a11])
  set w13 := exec D.N D.K (joinC 138 137 136) w12
  have e13 := EC.of_fr2 e12 f13 (by decide) (by decide)
  -- 14: h_{g_t} G⁻¹(A'_k) on 130
  obtain ⟨t1, a14, r14, f14⟩ := exec_ginvCall w13 e13 124 134 130 (by decide) hhf r6
    (by rw [frs2 f13 (by decide), frs2 f12 (by decide), frs f11 (by decide), frs f10 (by decide),
      frs f9 (by decide), frs f8 (by decide), frs f7 (by decide), frs2 f6 (by decide),
      frs f5 (by decide), frs f4 (by decide), frs2 f3 (by decide), frs f2 (by decide),
      frs f1 (by decide), hhf0])
    (by rw [frs2 f13 (by decide), frs2 f12 (by decide), frs f11 (by decide), frs f10 (by decide),
      frs f9 (by decide), frs f8 (by decide), frs f7 (by decide), a6])
  set w14 := exec D.N D.K (ginvCall 124 134 130) w13
  have e14 := EC.of_fr e13 f14 (by decide)
  -- 15: the Mul sum with c^aut on 131
  obtain ⟨t2, a15, r15, f15⟩ := exec_accCall w14 e14 128 127 131 (by decide) rA' hfc
    (by rw [frs f14 (by decide), frs2 f13 (by decide), frs2 f12 (by decide), frs f11 (by decide),
      frs f10 (by decide), frs f9 (by decide), frs f8 (by decide), frs f7 (by decide),
      frs2 f6 (by decide), frs f5 (by decide), frs f4 (by decide), frs2 f3 (by decide),
      frs f2 (by decide), a1])
    (by rw [frs f14 (by decide), frs2 f13 (by decide), frs2 f12 (by decide), frs f11 (by decide),
      frs f10 (by decide), frs f9 (by decide), frs f8 (by decide), frs f7 (by decide),
      frs2 f6 (by decide), frs f5 (by decide), frs f4 (by decide), frs2 f3 (by decide),
      frs f2 (by decide), frs f1 (by decide), hfc0])
  set w15 := exec D.N D.K (accCall 128 127 131) w14
  have e15 := EC.of_fr e14 f15 (by decide)
  -- 16: σ(c) G⁻¹(C_{g_t}) on 132
  obtain ⟨t3, a16, r16, f16⟩ := exec_ginvCall w15 e15 129 136 132 (by decide) rc' r13
    (by rw [frs f15 (by decide), frs f14 (by decide), frs2 f13 (by decide), frs2 f12 (by decide),
      frs f11 (by decide), frs f10 (by decide), frs f9 (by decide), frs f8 (by decide),
      frs f7 (by decide), frs2 f6 (by decide), frs f5 (by decide), frs f4 (by decide),
      frs2 f3 (by decide), a2])
    (by rw [frs f15 (by decide), frs f14 (by decide), a13])
  set w16 := exec D.N D.K (ginvCall 129 136 132) w15
  have e16 := EC.of_fr e15 f16 (by decide)
  -- 17, 18: the sum on 121
  obtain ⟨a17, r17, f17⟩ := exec_addCall w16 e16 131 132 133 (by decide) r15 r16
    (by rw [frs f16 (by decide), a15]) a16
  set w17 := exec D.N D.K (addCall 131 132 133) w16
  have e17 := EC.of_fr e16 f17 (by decide)
  obtain ⟨a18, r18, f18⟩ := exec_addCall w17 e17 130 133 121 (by decide) r14 r17
    (by rw [frs f17 (by decide), frs f16 (by decide), frs f15 (by decide), a14]) a17
  set w18 := exec D.N D.K (addCall 130 133 121) w17
  have e : exec D.N D.K (roundC t) w = Function.update w18 120 (w18 135) := rfl
  have h135 : w18 135 = an.flatten := by
    rw [frs f18 (by decide), frs f17 (by decide), frs f16 (by decide), frs f15 (by decide),
      frs f14 (by decide), frs2 f13 (by decide), frs2 f12 (by decide), frs f11 (by decide),
      frs f10 (by decide), frs f9 (by decide), frs f8 (by decide), a7]
  refine ⟨⟨an, by rw [e, Function.update_self, h135], r7⟩,
    ⟨_, by rw [e, Function.update_of_ne (by decide), a18], r18.congr fun j => rfl⟩, fun j hj => ?_⟩
  have hj120 : j ≠ 120 := ne_of_lt80 hj (by decide)
  rw [e, Function.update_of_ne hj120, rfr_of f18 hj (by decide), rfr_of f17 hj (by decide),
    rfr_of f16 hj (by decide), rfr_of f15 hj (by decide), rfr_of f14 hj (by decide),
    rfr_of2 f13 hj (by decide) (by decide), rfr_of2 f12 hj (by decide) (by decide),
    rfr_of f11 hj (by decide), rfr_of f10 hj (by decide), rfr_of f9 hj (by decide),
    rfr_of f8 hj (by decide), rfr_of f7 hj (by decide), rfr_of2 f6 hj (by decide) (by decide),
    rfr_of f5 hj (by decide), rfr_of f4 hj (by decide), rfr_of2 f3 hj (by decide) (by decide),
    rfr_of f2 hj (by decide), rfr_of f1 hj (by decide)]

end AdvancedEncryption.ExpLUT.Prog
