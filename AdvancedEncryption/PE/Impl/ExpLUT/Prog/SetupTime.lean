import PE.Impl.ExpLUT.Prog.SetupSize

/-!
# The clock of `Setup` by per-tape bounds

The clock of the compiled `Setup` (`time_setupMP`: loader, per-tape time bound of `setupP X`,
emitter) in closed form.

* **The samplers** (`vb_ucF`, `vb_TF`): each framed sampler runs on its own tapes only, from blank
  scratch bounded by a common scratch bound `S`: `n` canonical uniform words cost
  `ucT N K n S` (`n N K` fair bits, two templates, `canonRP` certified by the abstract
  interpreter, `check_ucTail`, an append); the sampler of `T` costs its shape bound.
* **The deterministic part** (templates, `Ā T`, `g − Ā T`) from a bound `M` of every tape, the
  templates and the words of `Ā` and `T` at their lengths: `matMulMP` and `gadRowP` certified by the
  abstract interpreter (`check_matMulMP`, `check_gadRowP`), each sweep costing `2 M + 3`.
* **The output**: ten appends and two frames, additive in `M`.

`time_setupMP_le`: **`(setupMP X).time ≤ setupTF …`**, the closed form; `time_setupMP_conf`
at `N = 2^24`, `K = 2^16`, `b = 22`, `m̄ = 3 · 2^40 + 408`, the binary sampler.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym
open AdvancedEncryption.DualUse.Prog

/-! ### The canonical uniform sampler on its own tapes -/

/-- The variables of the tail: `0` the top size, `1` `L = n N`, `2` `K`. -/
def ucVars (S L K : ℕ) : List ℕ := [S, L, K]

def pLv : Poly := [([0, 1], 1)]
def pKv : Poly := [([0, 0, 1], 1)]
def pLKv : Poly := [([0, 1, 1], 1)]

/-- The tapes before the tail: tape `1` the fair bits, `7` `8` the templates `K`, `n N`. -/
def σuc : Asg := [[], pLKv] ++ List.replicate 5 pTop ++ [pKv, pLv] ++ List.replicate 31 pTop

/-- The tapes after the tail (the first 34). -/
def claimUc : Asg :=
  [[], [], pTop, pTop, pTop, pTop, pTop, [], [], [], [], [], pTop, pTop, pTop, pLv,
    pAdd pTop pKv] ++ List.replicate 16 pTop ++ [pLKv]

/-- The sweeps of the tail. -/
def wUc : Poly := [([], 12), ([0, 1], 19), ([0, 1, 1], 18)]

set_option maxRecDepth 100000 in
theorem check_ucTail : check 8 ucTail σuc claimUc wUc = true := by decide +kernel


/-- Before the sampler: the output and the fair-bit tape blank, the scratch at most `S`. -/
def ucIn (S : ℕ) : Fin 40 → ℕ := fun j => if j.val ≤ 1 then 0 else S

/-- After the sampler: the output at most `x`, tape `1` blank, the scratch at most `S`. -/
def ucOut (x S : ℕ) : Fin 40 → ℕ := fun j => if j.val = 0 then x else if j.val = 1 then 0 else S

/-- The time of `n` canonical uniform words from scratch at most `S`. -/
def ucT (N K n S : ℕ) : ℕ :=
  countT (n * (N * K)) 1 0 tCoin 0 S + ((2 * K + 1) * (4 * S + 12) +
    ((2 * (n * N) + 1) * (4 * S + 12) + ((2 * S + 3) * (12 + 19 * (n * N) + 18 * (n * N * K)) +
      appT' (S + K) (n * (N * K)))))

set_option maxHeartbeats 4000000 in
/-- **The canonical uniform sampler on its own tapes.** -/
theorem vb_unifCanonP (N K n S : ℕ) (hS : n * (N * K) ≤ S) (hK : K ≤ S) (hL : n * N ≤ S)
    (h1 : 1 ≤ S) :
    VB (unifCanonP N K n) (ucIn S) (ucT N K n S) (ucOut (n * (N * K)) (S + K)) := by
  set m := n * (N * K) with hm
  set L := n * N with hLdef
  have hmL : m = L * K := by rw [hm, hLdef]; ring
  -- the fair bits
  let v1 : Fin 40 → ℕ := fun j => if j.val = 0 then 0 else if j.val = 1 then m else S
  have s1 : VB (frame eU (coinsF m)) (ucIn S) (countT m 1 0 tCoin 0 S) v1 := by
    refine vb_smp eU (atbb_coinsF m) (x := 0) (S := S) ?_ ?_ ?_ ?_ ?_ ?_
    · show ucIn S 1 ≤ 0; simp [ucIn]
    · intro j _; simp only [ucIn]; split_ifs <;> omega
    · show max 1 m ≤ S; omega
    · show 0 + m * 1 ≤ v1 1; simp [v1]
    · intro j hj
      show S + m * 0 ≤ v1 (eU j)
      fin_cases j <;> simp_all [v1, eU]
    · intro t; simp only [ucIn, v1]; split_ifs <;> omega
  -- the templates
  have s2 := VB.natP (t := (7 : Fin 40)) (c := 34) (by decide) K (a := v1) (M := S)
    (fun i => by simp only [v1]; split_ifs <;> omega) hK
  have s3 := VB.natP (t := (8 : Fin 40)) (c := 34) (by decide) L (a := natB 7 34 K v1) (M := S)
    (fun i => by simp only [natB, v1]; split_ifs <;> omega) hL
  let v2 : Fin 40 → ℕ := fun j => if j.val = 0 then 0 else if j.val = 1 then m else
    if j.val = 7 then K else if j.val = 8 then L else S
  have e23 : natB 8 34 L (natB 7 34 K v1) ≤ v2 := by
    intro j
    simp only [natB, v1, v2]
    split_ifs <;> simp_all <;> omega
  -- the tail
  let v3 : Fin 40 → ℕ := fun j => if j.val ≤ 1 then 0 else if j.val = 33 then m else S + K
  have s4 : VB (prog ucTail) v2 ((2 * S + 3) * (12 + 19 * L + 18 * (L * K))) v3 := by
    have h := VB.checkMap check_ucTail (ucVars S L K) (u := id) Function.injective_id (a := v2)
      (b := v3) ?_ ?_ ?_ ?_ ?_
    · rw [Prog.map_id] at h
      refine h.mono le_rfl (le_of_eq ?_) le_rfl
      simp [wUc, ucVars, pEval, mEval, top]; ring
    · intro j
      fin_cases j <;> simp [v2, σuc, aGet, pEval, mEval, ucVars, pTop, pLv, pKv, pLKv, hmL, top]
    · intro t
      show v2 t ≤ S
      simp only [v2]; split_ifs <;> omega
    · intro j hj
      fin_cases j <;> simp_all [v3, claimUc, aGet, pEval, mEval, ucVars, pTop, pLv, pKv, pLKv, hmL,
        top] <;> omega
    · intro j hj
      have hl : claimUc.length = 34 := rfl
      rw [hl] at hj
      show S ≤ v3 j
      simp only [v3]; split_ifs <;> omega
    · intro t ht; exact absurd rfl (ht t)
  -- the append
  have s5 := vb_appendTapeP (r := (0 : Fin 40)) (a := 33) (S := 35) (c := 36) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) v3 (M := S + K)
    (fun t => by simp only [v3]; split_ifs <;> omega) (by simp [v3]; omega)
  have e5 : appOut (0 : Fin 40) 33 35 36 v3 ≤ ucOut m (S + K) := by
    intro j
    simp only [appOut, Function.update_apply, ucOut, v3]
    split_ifs <;> simp_all <;> omega
  have hv33 : v3 33 = m := by simp [v3]
  rw [hv33] at s5
  have := s1.seq (s2.seq ((s3.mono le_rfl le_rfl e23).seq (s4.seq (s5.mono le_rfl le_rfl e5))))
  refine this.mono le_rfl (le_of_eq ?_) le_rfl
  unfold ucT
  rw [← hm, ← hLdef]

/-! ### The samplers inside the store of `Setup` -/

/-- The bounds while sampling: tape `1` blank, the scratch `0 … 39` at most `S`, the others `f`. -/
def smpV (f : Fin 128 → ℕ) (S : ℕ) : Fin 128 → ℕ :=
  fun t => if t.val = 1 then 0 else if t.val < 40 then S else f t

theorem smpV_mono {f g : Fin 128 → ℕ} {S S' : ℕ} (hf : f ≤ g) (hS : S ≤ S') :
    smpV f S ≤ smpV g S' := by
  intro t; simp only [smpV]; split_ifs <;> first | omega | exact hf t

theorem eUC_ne (F : Fin 128) (hF : 40 ≤ F.val) (j : Fin 40) (hj : j.val ≠ 0) :
    eUC F hF j = ⟨j.val, by omega⟩ := by
  show (if j.val = 0 then F else ⟨j.val, _⟩) = _
  simp only [hj, ↓reduceIte]

set_option maxHeartbeats 1000000 in
/-- **A framed canonical uniform sampler** writing the blank field `F`. -/
theorem vb_ucF (F : Fin 128) (hF : 40 ≤ F.val) (N K n S : ℕ) (f : Fin 128 → ℕ) (hf : f F = 0)
    (hS : n * (N * K) ≤ S) (hK : K ≤ S) (hL : n * N ≤ S) (h1 : 1 ≤ S) :
    VB (frame (eUC F hF) (unifCanonP N K n)) (smpV f S) (ucT N K n S)
      (smpV (Function.update f F (n * (N * K))) (S + K)) := by
  have hF1 : F.val ≠ 1 := by omega
  have h := VB.frame (eUC F hF) (a := smpV f S) ((vb_unifCanonP N K n S hS hK hL h1).mono
    (a' := fun j => smpV f S (eUC F hF j)) (fun j => by
      by_cases hj : j.val = 0
      · have : j = 0 := Fin.ext hj
        subst this
        simp [smpV, ucIn, hF1, show ¬ F.val < 40 by omega, hf]
      · have e : eUC F hF j = ⟨j.val, by omega⟩ := eUC_ne F hF j hj
        show smpV f S (eUC F hF j) ≤ ucIn S j
        rw [e]
        simp only [smpV, ucIn]
        split_ifs <;> omega) le_rfl le_rfl)
  refine h.mono le_rfl le_rfl (embedF_le (fun j => ?_) (fun t => ?_))
  · by_cases hj : j.val = 0
    · have : j = 0 := Fin.ext hj
      subst this
      simp [smpV, ucOut, hF1, show ¬ F.val < 40 by omega]
    · have e : eUC F hF j = ⟨j.val, by omega⟩ := eUC_ne F hF j hj
      rw [e]
      simp only [smpV, ucOut]
      split_ifs <;> omega
  · simp only [smpV, Function.update_apply]
    split_ifs <;> first | omega | (subst_vars; omega) | exact le_rfl

/-- The tapes of the sampler of `T`. -/
theorem eT_apply (j : Fin 7) : eT j = ![83, 127, 2, 3, 4, 5, 6] j := rfl

variable {D : Dims} {χT : PMF (Rg D)}

set_option maxHeartbeats 1000000 in
/-- **The framed sampler of `T`**, writing the blank field `83`. -/
theorem vb_TF (X : RingSampler D χT) (f : Fin 128 → ℕ) (S : ℕ) (h83 : f 83 = 0)
    (h127 : f 127 ≤ S) (hS₀ : X.B.S₀ ≤ S) (hn : D.mb * D.K ≤ S) :
    VB (frame eT (repF (D.mb * D.K) X.P)) (smpV f S) ((X.B.count (D.mb * D.K)).T 0 S)
      (smpV (Function.update (Function.update f 83 (D.mb * D.K * X.B.a)) 127
        (S + D.mb * D.K * X.B.s)) (S + D.mb * D.K * X.B.s)) := by
  refine vb_smp eT (atbb_repF X.atb X.pres6 (D.mb * D.K)) (x := 0) (S := S) ?_ ?_ ?_ ?_ ?_ ?_
  · show smpV f S 83 ≤ 0; simp [smpV, h83]
  · intro j hj
    fin_cases j <;> simp_all [eT_apply, smpV]
  · show max X.B.S₀ (D.mb * D.K) ≤ S; omega
  · show 0 + D.mb * D.K * X.B.a ≤ _; simp [smpV]
  · intro j hj
    show S + D.mb * D.K * X.B.s ≤ _
    fin_cases j <;> simp_all [eT_apply, smpV]
  · intro t
    simp only [smpV, Function.update_apply]
    split_ifs <;> first | omega | (subst_vars; omega) | exact le_rfl

/-! ### The deterministic part -/

/-- A counter written over a bound `g`, its scratch already at least `n`. -/
theorem vb_natPU {k : ℕ} {t c : Fin k} (hct : c ≠ t) (n : ℕ) (g : Fin k → ℕ) {M : ℕ}
    (hg : ∀ i, g i ≤ M) (hn : n ≤ M) (hc : n ≤ g c) :
    VB (natP t c n) g ((2 * n + 1) * (4 * M + 12)) (Function.update g t n) := by
  refine (VB.natP hct n hg hn).mono le_rfl le_rfl fun i => ?_
  simp only [natB, Function.update_apply]
  split_ifs with h1 h2
  · exact le_rfl
  · subst h2; exact max_le le_rfl hc
  · exact le_rfl

/-- The bounds before the templates: `Ā` and `T` at their lengths, every other tape at most `M`. -/
def tmIn (D : Dims) (M : ℕ) : Fin 128 → ℕ := fun t =>
  if t.val = 82 then D.mb * (D.N * D.K) else if t.val = 83 then D.mb * D.K * (D.N * D.K) else M

/-- The bounds after the templates. -/
def tmOut (D : Dims) (M : ℕ) : Fin 128 → ℕ := fun t =>
  if t.val = 40 then D.K else if t.val = 41 then D.N else if t.val = 42 then D.N * D.K else
  if t.val = 43 then 1 else if t.val = 44 then D.mb else if t.val = 45 then D.K else
  if t.val = 46 then D.K * (D.N * D.K) else if t.val = 47 then D.K - 1 else
  if t.val = 48 then D.N * D.K else tmIn D M t

/-- The time of the templates. -/
def tmplT (D : Dims) (M : ℕ) : ℕ :=
  (2 * D.K + 1) * (4 * M + 12) + ((2 * D.N + 1) * (4 * M + 12) +
  ((2 * (D.N * D.K) + 1) * (4 * M + 12) + ((2 * 1 + 1) * (4 * M + 12) +
  ((2 * D.mb + 1) * (4 * M + 12) + ((2 * D.K + 1) * (4 * M + 12) +
  ((2 * (D.K * (D.N * D.K)) + 1) * (4 * M + 12) + ((2 * (D.K - 1) + 1) * (4 * M + 12) +
  ((2 * (D.N * D.K - 1) + 1) * (4 * M + 12) + (2 * (M + 1) + 3)))))))))

theorem NK_pos (D : Dims) : 1 ≤ D.N * D.K :=
  Nat.one_le_iff_ne_zero.mpr (by have := D.K_pos; have := D.N_pos; positivity)

set_option maxHeartbeats 4000000 in
/-- **The templates.** -/
theorem vb_tmplP (M : ℕ) (hM : D.K * (D.N * D.K) ≤ M) (hmb : D.mb * D.K * (D.N * D.K) ≤ M) :
    VB (tmplP D) (tmIn D M) (tmplT D M) (tmOut D M) := by
  have hNK := NK_pos D
  have hK := D.K_pos
  have hN := D.N_pos
  have hmb1 : D.mb * (D.N * D.K) ≤ M :=
    le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hK)) hmb
  have hK1 : D.K ≤ M := le_trans (Nat.le_mul_of_pos_right _ hNK) hM
  have hNK1 : D.N * D.K ≤ M := le_trans (Nat.le_mul_of_pos_left _ hK) hM
  have hN1 : D.N ≤ M := le_trans (Nat.le_mul_of_pos_right _ hK) hNK1
  have hmb2 : D.mb ≤ M := le_trans (Nat.le_mul_of_pos_right _ hNK) hmb1
  have g0 : ∀ i, tmIn D M i ≤ M := fun i => by simp only [tmIn]; split_ifs <;> omega
  have c0 : tmIn D M 125 = M := by simp [tmIn]
  have u : ∀ (g : Fin 128 → ℕ) (t : Fin 128) (n : ℕ), (∀ i, g i ≤ M) → n ≤ M →
      ∀ i, Function.update g t n i ≤ M := fun g t n hg hn i => by
    simp only [Function.update_apply]; split_ifs <;> [exact hn; exact hg i]
  unfold tmplP tmplT
  refine (vb_natPU (t := 40) (c := 125) (by decide) D.K _ g0 hK1 (by rw [c0]; exact hK1)).seq ?_
  refine (vb_natPU (t := 41) (c := 125) (by decide) D.N _ (u _ _ _ g0 hK1) hN1
    (by simp [c0]; exact hN1)).seq ?_
  refine (vb_natPU (t := 42) (c := 125) (by decide) (D.N * D.K) _
    (u _ _ _ (u _ _ _ g0 hK1) hN1) hNK1 (by simp [c0]; exact hNK1)).seq ?_
  refine (vb_natPU (t := 43) (c := 125) (by decide) 1 _
    (u _ _ _ (u _ _ _ (u _ _ _ g0 hK1) hN1) hNK1) (by omega) (by simp [c0]; omega)).seq ?_
  refine (vb_natPU (t := 44) (c := 125) (by decide) D.mb _
    (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ g0 hK1) hN1) hNK1) (by omega)) hmb2
    (by simp [c0]; exact hmb2)).seq ?_
  refine (vb_natPU (t := 45) (c := 125) (by decide) D.K _
    (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ g0 hK1) hN1) hNK1) (by omega)) hmb2) hK1
    (by simp [c0]; exact hK1)).seq ?_
  refine (vb_natPU (t := 46) (c := 125) (by decide) (D.K * (D.N * D.K)) _
    (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ g0 hK1) hN1) hNK1) (by omega)) hmb2)
      hK1) hM (by simp [c0]; exact hM)).seq ?_
  refine (vb_natPU (t := 47) (c := 125) (by decide) (D.K - 1) _
    (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ g0 hK1) hN1) hNK1) (by omega))
      hmb2) hK1) hM) (by omega) (by simp [c0]; omega)).seq ?_
  refine (vb_natPU (t := 48) (c := 125) (by decide) (D.N * D.K - 1) _
    (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ g0 hK1) hN1) hNK1)
      (by omega)) hmb2) hK1) hM) (by omega)) (by omega) (by simp [c0]; omega)).seq ?_
  refine (VB.prim (.cons 48 true) (M := M) (fun i => u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _
    (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ (u _ _ _ g0 hK1) hN1) hNK1) (by omega)) hmb2) hK1) hM)
      (by omega)) (by omega) i)).mono le_rfl le_rfl ?_
  intro t
  simp only [Prim.lenT]
  by_cases h48 : t = 48
  · subst h48; simp [tmOut]; omega
  rw [Function.update_of_ne h48, Function.update_of_ne h48]
  by_cases h47 : t = 47
  · subst h47; simp [tmOut]
  rw [Function.update_of_ne h47]
  by_cases h46 : t = 46
  · subst h46; simp [tmOut]
  rw [Function.update_of_ne h46]
  by_cases h45 : t = 45
  · subst h45; simp [tmOut]
  rw [Function.update_of_ne h45]
  by_cases h44 : t = 44
  · subst h44; simp [tmOut]
  rw [Function.update_of_ne h44]
  by_cases h43 : t = 43
  · subst h43; simp [tmOut]
  rw [Function.update_of_ne h43]
  by_cases h42 : t = 42
  · subst h42; simp [tmOut]
  rw [Function.update_of_ne h42]
  by_cases h41 : t = 41
  · subst h41; simp [tmOut]
  rw [Function.update_of_ne h41]
  by_cases h40 : t = 40
  · subst h40; simp [tmOut]
  rw [Function.update_of_ne h40]
  have : ∀ v : ℕ, v ∈ [40, 41, 42, 43, 44, 45, 46, 47, 48] → t.val ≠ v := by
    intro v hv he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact h40 (Fin.ext he) | exact h41 (Fin.ext he) | exact h42 (Fin.ext he) |
        exact h43 (Fin.ext he) | exact h44 (Fin.ext he) | exact h45 (Fin.ext he) |
        exact h46 (Fin.ext he) | exact h47 (Fin.ext he) | exact h48 (Fin.ext he)
  simp only [tmOut, this 40 (by simp), this 41 (by simp), this 42 (by simp), this 43 (by simp),
    this 44 (by simp), this 45 (by simp), this 46 (by simp), this 47 (by simp), this 48 (by simp),
    ↓reduceIte, le_refl]

/-! ### The gadget columns -/

open SigabaNeo.Tape.Prog.SpecT in
/-- The sweeps of `matMulMP` (variables `top, N, K, m, n, l`). -/
def wMatM : Poly :=
  [([], 5), ([0, 0, 0, 1], 8), ([0, 0, 0, 1, 0, 1], 15), ([0, 0, 0, 1, 1, 1], 48),
    ([0, 1, 1, 1, 1, 1], 76), ([0, 0, 0, 1, 1, 2], 4), ([0, 1, 1, 1, 1, 2], 3),
    ([0, 1, 0, 1, 1, 1], 73), ([0, 2, 0, 1, 1, 1], 71), ([0, 2, 1, 1, 1, 1], 107),
    ([0, 2, 2, 1, 1, 1], 22), ([0, 0, 1, 1, 1, 1], 7), ([0, 1, 1, 1, 0, 1], 9),
    ([0, 0, 0, 1, 1], 4), ([0, 1, 1, 1, 1], 3)]

open SigabaNeo.Tape.Prog.SpecT in
/-- `matMulMP` from any scratch below the top size. -/
def σMatT : Asg := σMat ++ List.replicate 49 pTop

open SigabaNeo.Tape.Prog.SpecT in
set_option maxRecDepth 100000 in
/-- **The certificate of `matMulMP`.** -/
theorem check_matMulMP : check 8 Prog.matMulMP σMatT σMat' wMatM = true := by decide +kernel

open SigabaNeo.Tape.Prog.SpecT in
/-- `gadRowP`: the output register, `P` (`K` ring words), templates `K`, `N`, `N K`, `K − 1`
(at most `K`), the word of `1`. -/
def σGr' : Asg := [pTop, mo 1 [1, 2], pK, pN, pNK, pK, pNK]

/-- `gadRowP` from any scratch below the top size. -/
def σGr : Asg := σGr' ++ List.replicate 35 pTop

/-- The sweeps of `gadRowP`. -/
def wGr : Poly :=
  [([], 8), ([0, 0, 1], 27), ([0, 1, 1], 63), ([0, 0, 2], 11), ([0, 1, 2], 89), ([0, 1, 3], 18)]

set_option maxRecDepth 100000 in
/-- **The certificate of `gadRowP`.** -/
theorem check_gadRowP : check 8 Prog.gadRowP σGr σGr' wGr = true := by decide +kernel

/-- The time of the gadget columns from tapes at most `M`. -/
def detT (D : Dims) (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + ((2 * M + 3) * pEval (Prog.SpecT.vars M D.N D.K 1 D.mb D.K 0) wMatM +
    (2 * M + 3) * pEval (Prog.SpecT.vars M D.N D.K 0 0 0 0) wGr)

theorem aGet_rep (σ : Asg) (n : ℕ) (p : Poly) (i : ℕ) (h1 : σ.length ≤ i)
    (h2 : i < σ.length + n) : aGet (σ ++ List.replicate n p) i = p := by
  simp only [aGet, List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
    List.getElem?_replicate]
  simp only [show i - σ.length < n by omega, ↓reduceIte]; rfl

theorem tmOut_eq (D : Dims) (M : ℕ) (t : Fin 128)
    (h : t.val < 40 ∨ (50 < t.val ∧ t.val < 82) ∨ 83 < t.val) : tmOut D M t = M := by
  simp only [tmOut, tmIn]; split_ifs <;> omega

/-- The inputs of a certified program: its first `n` tapes as listed, the others at most the top. -/
theorem hin_of {m : ℕ} {u : Fin m → Fin 128} {a : Fin 128 → ℕ} {σ : Asg} {ρ : List ℕ}
    (hlow : ∀ j : Fin m, j.val < σ.length → a (u j) ≤ pEval ρ (aGet σ j.val))
    (htop : ∀ t, a t ≤ top ρ) :
    ∀ j : Fin m, a (u j) ≤ pEval ρ (aGet (σ ++ List.replicate (m - σ.length) pTop) j.val) := by
  intro j
  by_cases hj : j.val < σ.length
  · have e : aGet (σ ++ List.replicate (m - σ.length) pTop) j.val = aGet σ j.val := by
      simp only [aGet, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    rw [e]; exact hlow j hj
  · rw [aGet_rep _ _ _ _ (by omega) (by omega), pEval_of_isTop rfl]
    exact htop _

set_option maxHeartbeats 8000000 in
open SigabaNeo.Tape.Prog.SpecT in
/-- **The gadget columns** (`detCore`): from the templates, every tape ends at most `M`. -/
theorem vb_detCore (M : ℕ) (hM : D.K * (D.N * D.K) ≤ M) (hmb : D.mb * D.K * (D.N * D.K) ≤ M) :
    VB (prog detCore) (tmOut D M) (detT D M) (fun _ => M) := by
  have hNK := NK_pos D
  have hK := D.K_pos
  have hN := D.N_pos
  have hmb1 : D.mb * (D.N * D.K) ≤ M :=
    le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hK)) hmb
  have hK1 : D.K ≤ M := le_trans (Nat.le_mul_of_pos_right _ hNK) hM
  have hNK1 : D.N * D.K ≤ M := le_trans (Nat.le_mul_of_pos_left _ hK) hM
  have hN1 : D.N ≤ M := le_trans (Nat.le_mul_of_pos_right _ hK) hNK1
  have hmb2 : D.mb ≤ M := le_trans (Nat.le_mul_of_pos_right _ hNK) hmb1
  have g0 : ∀ i, tmOut D M i ≤ M := fun i => by simp only [tmOut, tmIn]; split_ifs <;> omega
  have s1 := VB.prim (.copy 50 46) g0
  have e1 : Prim.lenT (.copy (50 : Fin 128) 46) (tmOut D M) =
      Function.update (tmOut D M) 50 (D.K * (D.N * D.K)) := by
    simp [Prim.lenT, tmOut]
  rw [e1] at s1
  set a1 := Function.update (tmOut D M) 50 (D.K * (D.N * D.K)) with ha1
  have g1 : ∀ i, a1 i ≤ M := fun i => by
    simp only [ha1, Function.update_apply]; split_ifs <;> [exact hM; exact g0 i]
  set a2 := Function.update a1 49 (D.K * (D.N * D.K)) with ha2
  have g2 : ∀ i, a2 i ≤ M := fun i => by
    simp only [ha2, Function.update_apply]; split_ifs <;> [exact hM; exact g1 i]
  have hscM : ∀ j : Fin 59, 10 ≤ j.val →
      (uM j).val < 40 ∨ (50 < (uM j).val ∧ (uM j).val < 82) ∨ 83 < (uM j).val := by decide
  have s2 := VB.checkMap check_matMulMP (vars M D.N D.K 1 D.mb D.K 0) uM_inj (a := a1)
    (b := a2) (hin_of (fun j hj => ?_) g1) g1 (fun j hj => ?_)
    (fun j hj => by
      have hl : σMat'.length = 10 := rfl
      rw [hl] at hj
      have h := hscM j hj
      have h49 : uM j ≠ 49 := fun e => by rw [e] at h; simp at h
      have h50 : uM j ≠ 50 := fun e => by rw [e] at h; simp at h
      show M ≤ a2 (uM j)
      rw [ha2, Function.update_of_ne h49, ha1, Function.update_of_ne h50, tmOut_eq D M _ h])
    (fun t ht => by
      have h49 : t ≠ 49 := fun e => ht 0 (by rw [e]; rfl)
      rw [ha2, Function.update_of_ne h49])
  rotate_left
  · obtain ⟨v, hv⟩ := j
    have hl : σMat.length = 10 := rfl
    rw [hl] at hj
    simp only at hj
    interval_cases v <;> simp [ha1, uM, tmOut, tmIn, σMat, aGet, pEval, mEval, vars, pTop, top,
      pmnNK, pnlNK, pmlNK, pK, pN, pNK, pm, pn, pl, mo] <;> first | omega | (ring_nf; omega) | skip
  · obtain ⟨v, hv⟩ := j
    have hl : σMat'.length = 10 := rfl
    rw [hl] at hj
    simp only at hj
    interval_cases v <;> simp [ha2, ha1, uM, tmOut, tmIn, σMat', aGet, pEval, mEval, vars,
      pmnNK, pnlNK, pmlNK, pK, pN, pNK, pm, pn, pl, mo] <;> first | omega | (ring_nf; omega) | skip
  have s3 := VB.checkMap check_gadRowP (vars M D.N D.K 0 0 0 0) uG_inj (a := a2)
    (b := fun _ => M) (hin_of (σ := σGr') (fun j hj => ?_) g2) g2 (fun j hj => ?_)
    (fun _ _ => le_rfl) (fun t _ => g2 t)
  rotate_left
  · obtain ⟨v, hv⟩ := j
    have hl : σGr'.length = 7 := rfl
    rw [hl] at hj
    simp only at hj
    interval_cases v <;> simp [ha2, ha1, uG, tmOut, tmIn, σGr', aGet, pEval, mEval, vars, pTop, top,
      pK, pN, pNK, mo] <;> first | omega | (ring_nf; nlinarith) | skip
  · obtain ⟨v, hv⟩ := j
    have hl : σGr'.length = 7 := rfl
    rw [hl] at hj
    simp only at hj
    interval_cases v <;> simp [σGr', aGet, pEval, mEval, vars, pTop, top, pK, pN, pNK, mo] <;>
      first | omega | (ring_nf; nlinarith) | skip
  exact (s1.seq (s2.seq s3) :)

/-! ### The output -/

/-- The bounds while writing the output: the key word `0` at most `acc`, the output `124` at most
`out`, the counter `123` at most `cnt`, the others at most `M`. -/
def oV (acc out cnt M : ℕ) : Fin 128 → ℕ := fun t =>
  if t.val = 0 then acc else if t.val = 124 then out else if t.val = 123 then cnt else M

set_option maxHeartbeats 1000000 in
/-- **An append of a field** (at most `M`) to the key word. -/
theorem vb_appCO (a : Fin 128) (ha0 : a.val ≠ 0) (ha124 : a.val ≠ 124) (ha123 : a.val ≠ 123)
    (acc out cnt M Mall : ℕ) (h1 : acc + M ≤ Mall) (h2 : out ≤ Mall) (h3 : cnt ≤ Mall) :
    VB (appC 0 a) (oV acc out cnt M) ((2 * (Mall + 1) + 3) + appT' Mall M)
      (oV (acc + M) out M M) := by
  have hM : ∀ i, oV acc out cnt M i ≤ Mall := fun i => by simp only [oV]; split_ifs <;> omega
  have s1 := VB.prim (.copy 121 a) hM
  have e1 : Prim.lenT (.copy (121 : Fin 128) a) (oV acc out cnt M) =
      Function.update (oV acc out cnt M) 121 M := by
    simp [Prim.lenT, oV, ha0, ha124, ha123]
  rw [e1] at s1
  have s2 := vb_appendTapeP (r := (0 : Fin 128)) (a := 121) (S := 122) (c := 123) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Function.update (oV acc out cnt M) 121 M) (M := Mall)
    (fun i => by simp only [Function.update_apply]; split_ifs <;> [omega; exact hM i])
    (by simp [oV]; omega)
  have e2 : Function.update (oV acc out cnt M) 121 M 121 = M := by simp
  rw [e2] at s2
  refine (s1.seq s2).mono le_rfl le_rfl fun t => ?_
  simp only [appOut, Function.update_apply, oV, Fin.ext_iff, Fin.isValue]
  split_ifs <;> simp_all <;> omega

set_option maxHeartbeats 1000000 in
/-- **The frame of the key word** appended to the output. -/
theorem vb_frO (acc out cnt M Mall : ℕ) (h1 : out + 2 * acc + 1 ≤ Mall) (h2 : M ≤ Mall)
    (h3 : cnt ≤ Mall) (h4 : acc ≤ Mall) :
    VB (frameApP 124 0 122 123) (oV acc out cnt M) (frT' Mall acc)
      (oV acc (out + 2 * acc + 1) acc M) := by
  have hM : ∀ i, oV acc out cnt M i ≤ Mall := fun i => by simp only [oV]; split_ifs <;> omega
  have s := vb_frameApP (r := (124 : Fin 128)) (a := 0) (S := 122) (c := 123) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (oV acc out cnt M) (M := Mall) hM
    (by simp [oV]; omega)
  have e0 : oV acc out cnt M 0 = acc := by simp [oV]
  rw [e0] at s
  refine s.mono le_rfl le_rfl fun t => ?_
  simp only [frOut, Function.update_apply, oV, Fin.ext_iff, Fin.isValue]
  split_ifs <;> simp_all <;> omega

/-- The bound of every tape while writing the output. -/
abbrev mAll (M : ℕ) : ℕ := 40 * M + 2

/-- The time of the output from tapes at most `M`. -/
def outT (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + 9 * ((2 * (mAll M + 1) + 3) + appT' (mAll M) M) +
    frT' (mAll M) (9 * M) + frT' (mAll M) (10 * M)

set_option maxHeartbeats 4000000 in
/-- **The output**: from tapes at most `M`, the output tape ends at most `39 M + 2`. -/
theorem vb_outP (M : ℕ) :
    VB outP (fun _ => M) (outT M) (oV (10 * M) (39 * M + 2) (10 * M) M) := by
  have s0 := VB.prim (.copy (0 : Fin 128) 82) (a := fun _ => M) (M := M) (fun _ => le_rfl)
  have e0 : Prim.lenT (.copy (0 : Fin 128) 82) (fun _ => M) ≤ oV M M M M := fun t => by
    simp only [Prim.lenT, Function.update_apply, oV]; split_ifs <;> omega
  have ap := fun (a : Fin 128) (ha0 : a.val ≠ 0) (ha124 : a.val ≠ 124) (ha123 : a.val ≠ 123)
    (acc out cnt : ℕ) (h1 : acc + M ≤ mAll M) (h2 : out ≤ mAll M) (h3 : cnt ≤ mAll M) =>
    vb_appCO a ha0 ha124 ha123 acc out cnt M (mAll M) h1 h2 h3
  set M9 := M + M + M + M + M + M + M + M + M with hM9
  have a1 := ap 50 (by decide) (by decide) (by decide) M M M (by unfold mAll; omega)
    (by unfold mAll; omega) (by unfold mAll; omega)
  have a2 := ap 84 (by decide) (by decide) (by decide) (M + M) M M (by unfold mAll; omega)
    (by unfold mAll; omega) (by unfold mAll; omega)
  have a3 := ap 85 (by decide) (by decide) (by decide) (M + M + M) M M (by unfold mAll; omega)
    (by unfold mAll; omega) (by unfold mAll; omega)
  have a4 := ap 86 (by decide) (by decide) (by decide) (M + M + M + M) M M (by unfold mAll; omega)
    (by unfold mAll; omega) (by unfold mAll; omega)
  have a5 := ap 87 (by decide) (by decide) (by decide) (M + M + M + M + M) M M
    (by unfold mAll; omega) (by unfold mAll; omega) (by unfold mAll; omega)
  have a6 := ap 88 (by decide) (by decide) (by decide) (M + M + M + M + M + M) M M
    (by unfold mAll; omega) (by unfold mAll; omega) (by unfold mAll; omega)
  have a7 := ap 89 (by decide) (by decide) (by decide) (M + M + M + M + M + M + M) M M
    (by unfold mAll; omega) (by unfold mAll; omega) (by unfold mAll; omega)
  have a8 := ap 90 (by decide) (by decide) (by decide) (M + M + M + M + M + M + M + M) M M
    (by unfold mAll; omega) (by unfold mAll; omega) (by unfold mAll; omega)
  have f1 := vb_frO M9 M M M (mAll M) (by unfold mAll; omega) (by unfold mAll; omega)
    (by unfold mAll; omega) (by unfold mAll; omega)
  have a9 := ap 83 (by decide) (by decide) (by decide) M9 (M + 2 * M9 + 1) M9
    (by unfold mAll; omega) (by unfold mAll; omega) (by unfold mAll; omega)
  have f2 := vb_frO (M9 + M) (M + 2 * M9 + 1) M M (mAll M) (by unfold mAll; omega)
    (by unfold mAll; omega) (by unfold mAll; omega) (by unfold mAll; omega)
  have h := (s0.mono le_rfl le_rfl e0).seq (a1.seq (a2.seq (a3.seq (a4.seq (a5.seq (a6.seq
    (a7.seq (a8.seq (f1.seq (a9.seq f2))))))))))
  refine h.mono le_rfl (le_of_eq ?_) fun t => ?_
  · have : 9 * M = M9 := by rw [hM9]; ring
    rw [← this, show 9 * M + M = 10 * M by ring]; unfold outT; ring
  · simp only [oV]; split_ifs <;> omega

/-! ### The whole program -/

theorem upd_le {f g : Fin 128 → ℕ} {F : Fin 128} {x : ℕ} (hf : f ≤ g) (hx : x ≤ g F) :
    Function.update f F x ≤ g := fun t => by
  simp only [Function.update_apply]; split_ifs with h
  · subst h; exact hx
  · exact hf t

/-- The scratch bound after the sampler of `T`. -/
abbrev sT (D : Dims) (B : Bnd) (S : ℕ) : ℕ := S + D.K + D.mb * D.K * B.s

/-- The time of the samplers from the scratch bound `S`. -/
def smpT (D : Dims) (B : Bnd) (S : ℕ) : ℕ :=
  ucT D.N D.K D.mb S + ((B.count (D.mb * D.K)).T 0 (S + D.K) +
  (ucT D.N D.K (nB2 D) (sT D B S) + (ucT D.N D.K (nH D) (sT D B S + D.K) +
  (ucT D.N D.K (nA D) (sT D B S + D.K + D.K) + (ucT D.N D.K (nA0 D) (sT D B S + D.K + D.K + D.K) +
  (ucT D.N D.K (nAin D) (sT D B S + D.K + D.K + D.K + D.K) +
  (ucT D.N D.K (nAaut D) (sT D B S + D.K + D.K + D.K + D.K + D.K) +
  ucT D.N D.K 2 (sT D B S + D.K + D.K + D.K + D.K + D.K + D.K))))))))

/-- **The closed form of the clock of `Setup`**: the loader (input at most `nI` bits), the
samplers (scratch at most `S`), the templates, the gadget columns and the output (every tape at
most `M`), the emitter. -/
def setupTF (D : Dims) (B : Bnd) (nI S M : ℕ) : ℕ :=
  (2 * nI + 2) + (smpT D B S + (tmplT D M + (detT D M + outT M))) + (2 * (39 * M + 2) + 2)

/-- The hypotheses on the bounds `S` (scratch of the samplers) and `M` (every tape afterwards). -/
structure SetupBounds (D : Dims) (B : Bnd) (nI S M : ℕ) : Prop where
  hS : ∀ n ∈ [D.mb, nB2 D, nH D, nA D, nA0 D, nAin D, nAaut D, 2], n * (D.N * D.K) ≤ S
  hS₀ : B.S₀ ≤ S
  ha : B.a ≤ D.N * D.K
  hM : sT D B S + 7 * D.K ≤ M
  hnI : nI ≤ M
  hKM : D.K * (D.N * D.K) ≤ M
  hmbM : D.mb * D.K * (D.N * D.K) ≤ M

set_option maxHeartbeats 16000000 in
/-- **The per-tape bounds of `setupP`.** -/
theorem vb_setupP (X : RingSampler D χT) {nI S M : ℕ} (hb : SetupBounds D X.B nI S M) :
    VB (setupP X) (Prog.inputBound 126 nI) (smpT D X.B S + (tmplT D M + (detT D M + outT M)))
      (oV (10 * M) (39 * M + 2) (10 * M) M) := by
  obtain ⟨hS, hS₀, ha, hM, hnI, hKM, hmbM⟩ := hb
  have hNK := NK_pos D
  have hK := D.K_pos
  have cnt : ∀ n ∈ [D.mb, nB2 D, nH D, nA D, nA0 D, nAin D, nAaut D, 2], ∀ S' : ℕ, S ≤ S' →
      n * (D.N * D.K) ≤ S' ∧ D.K ≤ S' ∧ n * D.N ≤ S' ∧ 1 ≤ S' := by
    intro n hn S' hS'
    have h := hS n hn
    have h2 := hS 2 (by simp)
    refine ⟨h.trans hS', ?_, ?_, ?_⟩
    · have : D.K ≤ 2 * (D.N * D.K) := by nlinarith [D.N_pos]
      omega
    · have : n * D.N ≤ n * (D.N * D.K) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hK)
      omega
    · omega
  have hmbK : D.mb * D.K ≤ S := by
    have := hS D.mb (by simp)
    have : D.mb * D.K ≤ D.mb * (D.N * D.K) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ D.N_pos)
    omega
  set f0 : Fin 128 → ℕ := Function.update (fun _ => 0) 126 nI with hf0
  have i0 : Prog.inputBound 126 nI ≤ smpV f0 S := fun t => by
    simp only [Prog.inputBound, smpV, hf0, Function.update_apply]
    split_ifs <;> first | omega | (subst_vars; simp_all)
  set S1 := S + D.K
  set f1 := Function.update f0 82 (D.mb * (D.N * D.K))
  have v1 := vb_ucF 82 (by decide) D.N D.K D.mb S f0 (by simp [hf0])
    (cnt D.mb (by simp) S le_rfl).1 (cnt D.mb (by simp) S le_rfl).2.1
    (cnt D.mb (by simp) S le_rfl).2.2.1 (cnt D.mb (by simp) S le_rfl).2.2.2
  set S2 := sT D X.B S
  set f2 := Function.update (Function.update f1 83 (D.mb * D.K * X.B.a)) 127
    (S1 + D.mb * D.K * X.B.s)
  have v2 := vb_TF X f1 S1 (by simp [f1, hf0]) (by simp [f1, hf0]) (by omega) (by omega)
  have l2 : S1 + D.mb * D.K * X.B.s = S2 := rfl
  rw [l2] at v2
  have u := fun (F : Fin 128) (hF : 40 ≤ F.val) (n : ℕ)
    (hn : n ∈ [D.mb, nB2 D, nH D, nA D, nA0 D, nAin D, nAaut D, 2]) (f : Fin 128 → ℕ) (S' : ℕ)
    (hS' : S ≤ S') (hf : f F = 0) =>
    vb_ucF F hF D.N D.K n S' f hf (cnt n hn S' hS').1 (cnt n hn S' hS').2.1 (cnt n hn S' hS').2.2.1
      (cnt n hn S' hS').2.2.2
  have v3 := u 84 (by decide) (nB2 D) (by simp) f2 S2 (by omega) (by simp [f2, f1, hf0])
  have v4 := u 85 (by decide) (nH D) (by simp) (Function.update f2 84 (nB2 D * (D.N * D.K)))
    (S2 + D.K) (by omega) (by simp [f2, f1, hf0])
  have v5 := u 86 (by decide) (nA D) (by simp) (Function.update (Function.update f2 84
    (nB2 D * (D.N * D.K))) 85 (nH D * (D.N * D.K))) (S2 + D.K + D.K) (by omega)
    (by simp [f2, f1, hf0])
  have v6 := u 87 (by decide) (nA0 D) (by simp) (Function.update (Function.update
    (Function.update f2 84 (nB2 D * (D.N * D.K))) 85 (nH D * (D.N * D.K))) 86
      (nA D * (D.N * D.K))) (S2 + D.K + D.K + D.K) (by omega) (by simp [f2, f1, hf0])
  have v7 := u 88 (by decide) (nAin D) (by simp) (Function.update (Function.update
    (Function.update (Function.update f2 84 (nB2 D * (D.N * D.K))) 85 (nH D * (D.N * D.K))) 86
      (nA D * (D.N * D.K))) 87 (nA0 D * (D.N * D.K))) (S2 + D.K + D.K + D.K + D.K) (by omega)
    (by simp [f2, f1, hf0])
  have v8 := u 89 (by decide) (nAaut D) (by simp) (Function.update (Function.update
    (Function.update (Function.update (Function.update f2 84 (nB2 D * (D.N * D.K))) 85
      (nH D * (D.N * D.K))) 86 (nA D * (D.N * D.K))) 87 (nA0 D * (D.N * D.K))) 88
        (nAin D * (D.N * D.K))) (S2 + D.K + D.K + D.K + D.K + D.K) (by omega)
    (by simp [f2, f1, hf0])
  have v9 := u 90 (by decide) 2 (by simp) (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update f2 84 (nB2 D * (D.N * D.K))) 85
      (nH D * (D.N * D.K))) 86 (nA D * (D.N * D.K))) 87 (nA0 D * (D.N * D.K))) 88
        (nAin D * (D.N * D.K))) 89 (nAaut D * (D.N * D.K)))
    (S2 + D.K + D.K + D.K + D.K + D.K + D.K) (by omega) (by simp [f2, f1, hf0])
  have t1 := vb_tmplP (D := D) M hKM hmbM
  have t2 := vb_detCore (D := D) M hKM hmbM
  have t3 := vb_outP M
  -- the samplers end below the bounds of the templates
  have j1 : smpV (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update f2 84 (nB2 D * (D.N * D.K))) 85
        (nH D * (D.N * D.K))) 86 (nA D * (D.N * D.K))) 87 (nA0 D * (D.N * D.K))) 88
          (nAin D * (D.N * D.K))) 89 (nAaut D * (D.N * D.K))) 90 (2 * (D.N * D.K)))
        (S2 + D.K + D.K + D.K + D.K + D.K + D.K + D.K) ≤ tmIn D M := by
    have h84 := hS _ (by simp : nB2 D ∈ _)
    have h85 := hS _ (by simp : nH D ∈ _)
    have h86 := hS _ (by simp : nA D ∈ _)
    have h87 := hS _ (by simp : nA0 D ∈ _)
    have h88 := hS _ (by simp : nAin D ∈ _)
    have h89 := hS _ (by simp : nAaut D ∈ _)
    have h90 := hS _ (by simp : 2 ∈ _)
    have h82 := hS _ (by simp : D.mb ∈ _)
    have h83 : D.mb * D.K * X.B.a ≤ D.mb * D.K * (D.N * D.K) := Nat.mul_le_mul_left _ ha
    have hS2 : S2 ≤ M := by omega
    have hS1 : S1 + D.mb * D.K * X.B.s ≤ M := by simp only [S1, S2, sT] at hS2 ⊢; omega
    have hSM : S ≤ M := by simp only [S2, sT] at hS2; omega
    have g0 : f0 ≤ tmIn D M := fun t => by
      simp only [hf0, Function.update_apply, tmIn]; split_ifs <;> omega
    have g9 := upd_le (upd_le (upd_le (upd_le (upd_le (upd_le (upd_le (upd_le (upd_le (upd_le g0
      (x := D.mb * (D.N * D.K)) (F := 82) (by simp [tmIn])) (x := D.mb * D.K * X.B.a) (F := 83)
        (by simp [tmIn]; exact h83)) (x := S1 + D.mb * D.K * X.B.s) (F := 127) (by simp [tmIn]; omega))
      (x := nB2 D * (D.N * D.K)) (F := 84) (by simp [tmIn]; omega))
      (x := nH D * (D.N * D.K)) (F := 85) (by simp [tmIn]; omega))
      (x := nA D * (D.N * D.K)) (F := 86) (by simp [tmIn]; omega))
      (x := nA0 D * (D.N * D.K)) (F := 87) (by simp [tmIn]; omega))
      (x := nAin D * (D.N * D.K)) (F := 88) (by simp [tmIn]; omega))
      (x := nAaut D * (D.N * D.K)) (F := 89) (by simp [tmIn]; omega))
      (x := 2 * (D.N * D.K)) (F := 90) (by simp [tmIn]; omega)
    intro t
    simp only [smpV]
    split_ifs with h1 h2
    · exact Nat.zero_le _
    · simp only [tmIn, show t.val ≠ 82 by omega, show t.val ≠ 83 by omega, ↓reduceIte]; omega
    · exact g9 t
  have h := v1.seq (v2.seq (v3.seq (v4.seq (v5.seq (v6.seq (v7.seq (v8.seq ((v9.mono le_rfl
    le_rfl j1).seq (t1.seq (t2.seq t3))))))))))
  refine h.mono i0 (le_of_eq ?_) le_rfl
  simp only [smpT, S2, S1, sT]
  ring_nf

/-- **The clock of `Setup`**, for inputs of at most `nI` bits. -/
theorem time_setupMP_le (X : RingSampler D χT) {nI S M : ℕ} (hb : SetupBounds D X.B nI S M)
    (hnI : nInS ≤ nI) : (setupMP X).time ≤ setupTF D X.B nI S M := by
  rw [time_setupMP]
  have h := vb_setupP X hb (Prog.inputBound 126 nInS) (fun t => by
    simp only [Prog.inputBound, Function.update_apply]; split_ifs <;> omega)
  have h124 := h.2 124
  simp only [oV] at h124
  unfold totalTimeT setupTF
  have : lenBoundT (setupP X) (Prog.inputBound 126 nInS) 124 ≤ 39 * M + 2 := by
    simpa using h124
  omega

end AdvancedEncryption.ExpLUT.Prog
