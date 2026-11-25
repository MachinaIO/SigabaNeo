import PE.Impl.ExpLUT.Prog.RedChalAut
open SigabaNeo.Tape.RingVM.Hash
/-!
# The bottom rows of `C^in` in the challenge (package G2, `chalP`)

* `bexp`, **`bexp_symbol8`**: the exponent selected by the eight attribute bits (MSB first);
* **`exec_rhoSteps`**: `P := X^{w x_t} P` from the bits of the symbol `x_t` (`rhoJ` with the
  templates `2N − w 2^{7−j}`);
* `cbPost`: the post-map `y ↦ y + 2^i P` with `P` doubling in `xP` (`hpost_cb`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG Matrix AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

/-! ### The exponent of the attribute bits -/

/-- The exponent selected by the first `j` bits of `x` with the weights `m`. -/
def bexp (m : ℕ → ℕ) (x : List Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (if hd (x.drop j) then m j else 0) + bexp m x j

theorem bexp_mul (w : ℕ) (m : ℕ → ℕ) (x : List Bool) (j : ℕ) :
    bexp (fun i => w * m i) x j = w * bexp m x j := by
  induction j with
  | zero => simp [bexp]
  | succ j ih =>
    simp only [bexp]
    split_ifs <;> simp [ih, Nat.mul_add]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- **The eight bits of a symbol select its value.** -/
theorem bexp_symbol8 : ∀ a : Symbol w8, bexp (fun i => 2 ^ (7 - i)) (symbolBits w8 a) 8 = a.val := by
  decide

variable {D : Dims}

theorem setting_X' : (setting D).E.X = monoX D.N := rfl

theorem two_le_N : 2 ≤ D.N := by
  have h := D.hlt
  have : 1 ≤ D.e := by
    by_contra h0
    have : D.e = 0 := by omega
    rw [this] at h; simp at h
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ D.e := Nat.pow_le_pow_right (by norm_num) this

/-- **`X^m` by `2N − m` rotations.** -/
theorem decRM_rho_sub' {x : List Bool} (hx : x.length = D.N * D.K) {m : ℕ} (hm : m ≤ 2 * D.N) :
    decRM D.N D.K ((rhoMW D.K)^[2 * D.N - m] x) = (setting D).E.X ^ m * decRM D.N D.K x := by
  rw [decRM_rhoMW_iter_mul D.N_pos hx, xInvG_pow_eq two_le_N (Nat.sub_le _ _),
    Nat.sub_sub_self hm, setting_X']

/-! ### The rotations -/

theorem rhoR_val {j : ℕ} (hj : j < 8) : rhoR j = ⟨37 + j, by omega⟩ := by
  simp only [rhoR, Nat.mod_eq_of_lt hj]

/-- **One attribute bit.** -/
theorem exec_rhoStep (j : ℕ) (hj : j < 8) (w : St) {b : Bool} {L : List Bool}
    (hA : w rAttr = b :: L) (hB : (w rBit).length = 1) (hC : (w xC1).length = 1)
    (hP : (w rP).length = D.N * D.K) {m : ℕ} (hm : m ≤ 2 * D.N)
    (hT : (w (rhoR j)).length = 2 * D.N - m) :
    exec D.N D.K (rhoStep j) w rAttr = L ∧ (exec D.N D.K (rhoStep j) w rBit).length = 1 ∧
      (exec D.N D.K (rhoStep j) w rP).length = D.N * D.K ∧
      decRM D.N D.K (exec D.N D.K (rhoStep j) w rP) =
        (setting D).E.X ^ (if b then m else 0) * decRM D.N D.K (w rP) ∧
      ∀ i, i ∉ [rBit, rAttr, rP] → exec D.N D.K (rhoStep j) w i = w i := by
  have hr : rhoR j = ⟨37 + j, by omega⟩ := rhoR_val hj
  have e1 := exec_mv_pop (N := D.N) (K := D.K) (d := rBit) (s := rAttr) (c := xC1) (by decide)
    (w := w) (v := [b]) (L := L) (by rw [hB, hC]) (by rw [hC]; rfl) hA
  have ex : exec D.N D.K (rhoStep j) w = exec D.N D.K (.ifb rBit (.rhoJ rP rP (rhoR j)) .nop)
      (Function.update (Function.update w rAttr L) rBit [b]) := by
    show exec D.N D.K (.ifb rBit (.rhoJ rP rP (rhoR j)) .nop) (exec D.N D.K (.mv rBit rAttr xC1) w) = _
    rw [e1]
  rw [ex]
  have hne : rP ≠ rhoR j := by rw [hr]; intro h; have := congrArg Fin.val h; simp at this; omega
  have hne2 : rBit ≠ rhoR j := by rw [hr]; intro h; have := congrArg Fin.val h; simp at this; omega
  have hne3 : rAttr ≠ rhoR j := by rw [hr]; intro h; have := congrArg Fin.val h; simp at this; omega
  cases b
  · simp only [exec, Function.update_self, hd, List.headD_cons, Bool.false_eq_true, ite_false]
    refine ⟨by simp [Function.update_apply], by simp, by simp [Function.update_apply, hP], ?_, ?_⟩
    · simp [Function.update_apply]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [Function.update_apply, hi.1, hi.2.1]
  · simp only [exec, Function.update_self, hd, List.headD_cons, ite_true]
    have hT' : (Function.update (Function.update w rAttr L) rBit [true] (rhoR j)).length =
        2 * D.N - m := by
      rw [Function.update_of_ne (Ne.symm hne2), Function.update_of_ne (Ne.symm hne3), hT]
    have hP' : (Function.update (Function.update w rAttr L) rBit [true] rP) = w rP := by
      simp [Function.update_apply]
    rw [hT', hP', opd_eq hP]
    refine ⟨by simp [Function.update_apply], by simp [Function.update_apply],
      by simp [Function.update_apply, hP], ?_, ?_⟩
    · simp [Function.update_apply, decRM_rho_sub' hP hm]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [Function.update_apply, hi.1, hi.2.1, hi.2.2]

/-- **The eight attribute bits of a symbol**: `P := X^{w x} P`. -/
theorem exec_rhoSteps (hN : wSt * 2 ^ 7 ≤ 2 * D.N) (w : St) (a : Symbol w8) (L : List Bool)
    (hA : w rAttr = symbolBits w8 a ++ L) (hB : (w rBit).length = 1) (hC : (w xC1).length = 1)
    (hP : (w rP).length = D.N * D.K)
    (hT : ∀ j < 8, (w (rhoR j)).length = 2 * D.N - wtR j) :
    exec D.N D.K (ofList ((List.range 8).map rhoStep)) w rAttr = L ∧
      (exec D.N D.K (ofList ((List.range 8).map rhoStep)) w rBit).length = 1 ∧
      (exec D.N D.K (ofList ((List.range 8).map rhoStep)) w rP).length = D.N * D.K ∧
      decRM D.N D.K (exec D.N D.K (ofList ((List.range 8).map rhoStep)) w rP) =
        (setting D).E.X ^ (wSt * a.val) * decRM D.N D.K (w rP) ∧
      ∀ i, i ∉ [rBit, rAttr, rP] → exec D.N D.K (ofList ((List.range 8).map rhoStep)) w i = w i := by
  set x := symbolBits w8 a
  have hxl : x.length = 8 := length_symbolBits w8 a
  have hwt : ∀ j < 8, wtR j ≤ 2 * D.N := fun j hj =>
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))).trans hN
  let P : ℕ → St → Prop := fun j w' =>
    w' rAttr = x.drop j ++ L ∧ (w' rBit).length = 1 ∧ (w' rP).length = D.N * D.K ∧
    decRM D.N D.K (w' rP) = (setting D).E.X ^ bexp wtR x j * decRM D.N D.K (w rP) ∧
    ∀ i, i ∉ [rBit, rAttr, rP] → w' i = w i
  have key := exec_ofList_map_inv (N := D.N) (K := D.K) (List.range 8) rhoStep P w
    ⟨by simpa using hA, hB, hP, by simp [bexp], fun _ _ => rfl⟩
    (fun j hj w' hP' => by
      have hj8 : j < 8 := by simpa using hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := hP'
      have hcons : x.drop j ++ L = x[j] :: (x.drop (j + 1) ++ L) := by
        rw [List.drop_eq_getElem_cons (by omega)]; rfl
      rw [List.getElem_range]
      obtain ⟨r1, r2, r3, r4, r5⟩ := exec_rhoStep (D := D) j hj8 w' (by rw [h1, hcons]) h2
        (by rw [h5 _ (by decide), hC]) h3 (hwt j hj8)
        (by rw [h5 _ (by simp [rhoR_val hj8, Fin.ext_iff]; omega), hT j hj8])
      refine ⟨r1, r2, r3, ?_, fun i hi => by rw [r5 i hi, h5 i hi]⟩
      rw [r4, h4, ← mul_assoc, ← pow_add]
      congr 2
      simp only [bexp, hd, List.drop_eq_getElem_cons (show j < x.length by omega),
        List.headD_cons]
      cases x[j] <;> simp)
  simp only [List.length_range] at key
  obtain ⟨h1, h2, h3, h4, h5⟩ := key
  refine ⟨?_, h2, h3, ?_, h5⟩
  · rw [h1, List.drop_of_length_le (by omega), List.nil_append]
  · rw [h4, show wtR = fun i => wSt * 2 ^ (7 - i) from rfl, bexp_mul, bexp_symbol8]

/-! ### The post-map of the second gadget half -/

theorem wr_cbPost : ∀ j ∈ wr cbPost, j = xH ∨ j = xP := by
  intro j hj; simp [cbPost, wr] at hj; rcases hj with h | h <;> simp [h]

/-- **`xH := xAcc + 2^i P`, `xP := 2 xP`.** -/
theorem hpost_cb (p : Rg D) (w : St) : ∀ i, ∀ w' : St, (w' xAcc).length = D.N * D.K →
    (∀ j, j ∉ phW → w' j = w j) →
    (fun i (x : List Bool) => x.length = D.N * D.K ∧ decRM D.N D.K x = 2 ^ i * p) i (w' xP) →
    (exec D.N D.K cbPost w' xH).length = D.N * D.K ∧
      decRM D.N D.K (exec D.N D.K cbPost w' xH) =
        (fun i y => y + 2 ^ i * p) i (decRM D.N D.K (w' xAcc)) ∧
      (fun i (x : List Bool) => x.length = D.N * D.K ∧ decRM D.N D.K x = 2 ^ i * p) (i + 1)
        (exec D.N D.K cbPost w' xP) := by
  intro i w' hA _ ⟨hl, hv⟩
  have e : exec D.N D.K cbPost w' = exec D.N D.K (.add xP xP xP)
      (Function.update w' xH (addRMW D.N D.K (w' xAcc) (w' xP))) := by
    show exec D.N D.K (.add xP xP xP) (exec D.N D.K (.add xH xAcc xP) w') = _
    rw [exec_add_eq hA hl]
  rw [e, exec_add_eq (by simp [Function.update_apply, hl]) (by simp [Function.update_apply, hl])]
  refine ⟨by simp [Function.update_apply, length_addRMW _ _ hA], ?_, ?_⟩
  · simp [Function.update_apply, decRM_addRMW hA hl, hv]
  · refine ⟨by simp [Function.update_apply, length_addRMW _ _ hl], ?_⟩
    simp [Function.update_apply, decRM_addRMW hl hl, hv, pow_succ]
    ring

/-! ### One bottom row -/

/-- The registers `cbStep` writes. -/
def cbW : List (Fin 200) := rP :: rBit :: rAttr :: phW

/-- **The bottom row of `C^in_t`**, from the word of the symbol `a = x_t`. -/
theorem exec_cbStep (hN : wSt * 2 ^ 7 ≤ 2 * D.N) (w : St) (a : Symbol w8) (L : List Bool)
    (f : Wb D → Rg D) (g0 g1 : Fin D.K → Wb D → Bool) (e0 e1 : Fin D.K → Rg D)
    (rest restF b₀ : List Bool) (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hA : w rAttr = symbolBits w8 a ++ L)
    (h1 : (w r1).length = D.N * D.K) (h1v : decRM D.N D.K (w r1) = 1)
    (hV : w xV = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v)).flatten)
    (hZ : w xZ = ((List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g0 i)).flatten ++
      (((List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g1 i)).flatten ++ rest))
    (hF : w xF = ((List.finRange D.K).map fun i => encRM D.N D.K (e0 i)).flatten ++
      (((List.finRange D.K).map fun i => encRM D.N D.K (e1 i)).flatten ++ restF))
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hK : (w cK).length = D.K) (hT : ∀ j < 8, (w (rhoR j)).length = 2 * D.N - wtR j)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K)
    (hBit : (w rBit).length = 1) :
    exec D.N D.K cbStep w xOut = bufW (D.N * D.K) b₀ (ys₀ ++
        ((List.finRange D.K).map fun i => encRM D.N D.K (f ⬝ᵥ bv (g0 i) + e0 i)) ++
        ((List.finRange D.K).map fun i => encRM D.N D.K
          (f ⬝ᵥ bv (g1 i) + 2 ^ i.val * (setting D).E.X ^ (wSt * a.val) + e1 i))) ∧
      exec D.N D.K cbStep w rAttr = L ∧ exec D.N D.K cbStep w xZ = rest ∧
      exec D.N D.K cbStep w xF = restF ∧
      (exec D.N D.K cbStep w xv).length = D.N * D.K ∧
      (exec D.N D.K cbStep w xBit).length = 1 ∧ (exec D.N D.K cbStep w xf).length = D.N * D.K ∧
      (exec D.N D.K cbStep w rBit).length = 1 ∧
      ∀ j, j ∉ cbW → exec D.N D.K cbStep w j = w j := by
  have E0 : exec D.N D.K cbStep w = exec D.N D.K (ofList [.cp xCnt cK, hashPhase cpPost,
      .cp xP rP, .cp xCnt cK, hashPhase cbPost])
      (exec D.N D.K (ofList ((List.range 8).map rhoStep)) (Function.update w rP (w r1))) := by
    rw [cbStep, exec_ofList_append, exec_ofList_append]; rfl
  rw [E0]
  set w1 := Function.update w rP (w r1) with hw1
  have E1 : ∀ j, j ≠ rP → w1 j = w j := fun j hj => Function.update_of_ne hj _ _
  obtain ⟨s1, s2, s3, s4, s5⟩ := exec_rhoSteps hN w1 a L (by rw [E1 _ (by decide), hA])
    (by rw [E1 _ (by decide), hBit]) (by rw [E1 _ (by decide), hC1]) (by simp [w1, h1])
    (fun j hj => by
      rw [E1 _ (by simp [rhoR_val hj, Fin.ext_iff]; omega), hT j hj])
  set w2 := exec D.N D.K (ofList ((List.range 8).map rhoStep)) w1 with hw2
  have E2 : ∀ j, j ∉ cbW → w2 j = w j := fun j hj => by
    simp only [cbW, List.mem_cons, not_or] at hj
    rw [s5 j (by simp [hj.1, hj.2.1, hj.2.2.1]), E1 j hj.1]
  have hp : decRM D.N D.K (w2 rP) = (setting D).E.X ^ (wSt * a.val) := by
    rw [s4, hw1, Function.update_self, h1v, mul_one]
  simp only [exec_ofList_cons, exec_ofList_nil]
  -- the first half
  set w3 := Function.update w2 xCnt (w2 cK) with hw3
  have E3 : ∀ j, j ∉ cbW → w3 j = w j := fun j hj => by
    rw [hw3, Function.update_of_ne (fun h => hj (by rw [h]; decide)), E2 j hj]
  have E32 : ∀ j, j ≠ xCnt → w3 j = w2 j := fun j hj => Function.update_of_ne hj _ _
  have hw3' : exec D.N D.K (.cp xCnt cK) w2 = w3 := rfl
  rw [hw3']
  have E3' : ∀ j, j ∉ [rBit, rAttr, rP, xCnt] → w3 j = w j := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [E32 j hj.2.2.2, s5 j (by simp [hj.1, hj.2.1, hj.2.2.1]), E1 j hj.2.2.1]
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := exec_hashPhase_fin D.K cpPost (fun _ x => x)
    (fun _ _ => True) wr_cpPost w3 (hpost_cp w3) trivial f g0 e0
    (((List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g1 i)).flatten ++ rest)
    (((List.finRange D.K).map fun i => encRM D.N D.K (e1 i)).flatten ++ restF) b₀ ys₀ hys₀
    (by rw [hw3, Function.update_self, E2 _ (by decide), hK])
    (by rw [E3' _ (by decide), hV]) (by rw [E3' _ (by decide), hZ])
    (by rw [E3' _ (by decide), hF]) (by rw [E3' _ (by decide), hOut])
    (by rw [E3' _ (by decide), hCm]) (by rw [E3' _ (by decide), hC1])
    (by rw [E3' _ (by decide), hCNK]) (by rw [E3' _ (by decide), hZero])
    (by rw [E3' _ (by decide), hv]) (by rw [E3' _ (by decide), hb]) (by rw [E3' _ (by decide), hf])
  set w4 := exec D.N D.K (hashPhase cpPost) w3 with hw4
  -- the second half
  set w6 := Function.update (Function.update w4 xP (w4 rP)) xCnt
    (Function.update w4 xP (w4 rP) cK) with hw6
  have hw6' : exec D.N D.K (.cp xCnt cK) (exec D.N D.K (.cp xP rP) w4) = w6 := rfl
  rw [hw6']
  have E6 : ∀ j, j ∉ cbW → w6 j = w j := fun j hj => by
    rw [hw6, Function.update_of_ne (fun h => hj (by rw [h]; decide)),
      Function.update_of_ne (fun h => hj (by rw [h]; decide)), p7 j (fun h => hj
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))), E3 j hj]
  have E64 : ∀ j, j ≠ xCnt → j ≠ xP → w6 j = w4 j := fun j h1 h2 => by
    rw [hw6, Function.update_of_ne h1, Function.update_of_ne h2]
  have hrP : w4 rP = w2 rP := by rw [p7 _ (by decide), E32 _ (by decide)]
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := exec_hashPhase_fin D.K cbPost
    (fun i y => y + 2 ^ i * (setting D).E.X ^ (wSt * a.val))
    (fun i (x : List Bool) => x.length = D.N * D.K ∧
      decRM D.N D.K x = 2 ^ i * (setting D).E.X ^ (wSt * a.val)) wr_cbPost w6
    (hpost_cb _ w6)
    ⟨by rw [hw6, Function.update_of_ne (by decide), Function.update_self, hrP, s3],
      by rw [hw6, Function.update_of_ne (by decide), Function.update_self, hrP, hp, pow_zero,
        one_mul]⟩
    f g1 e1 rest restF b₀
    (ys₀ ++ (List.finRange D.K).map fun i => encRM D.N D.K (f ⬝ᵥ bv (g0 i) + e0 i))
    (words_app hys₀)
    (by rw [hw6, Function.update_self, Function.update_of_ne (by decide), p7 _ (by decide),
      E32 _ (by decide), E2 _ (by decide), hK])
    (by rw [E6 _ (by decide), hV]) (by rw [E64 _ (by decide) (by decide), p2])
    (by rw [E64 _ (by decide) (by decide), p3]) (by rw [E64 _ (by decide) (by decide), p1])
    (by rw [E6 _ (by decide), hCm]) (by rw [E6 _ (by decide), hC1])
    (by rw [E6 _ (by decide), hCNK]) (by rw [E6 _ (by decide), hZero])
    (by rw [E64 _ (by decide) (by decide), p4]) (by rw [E64 _ (by decide) (by decide), p5])
    (by rw [E64 _ (by decide) (by decide), p6])
  refine ⟨?_, ?_, q2, q3, q4, q5, q6, ?_, ?_⟩
  · rw [q1]
  · rw [q7 _ (by decide), E64 _ (by decide) (by decide), p7 _ (by decide), E32 _ (by decide), s1]
  · rw [q7 _ (by decide), E64 _ (by decide) (by decide), p7 _ (by decide), E32 _ (by decide), s2]
  · intro j hj
    rw [q7 j (fun h => hj (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ h)))), E6 j hj]

/-! ### All bottom rows -/

/-- The words of the bottom row of `C^in_t`. -/
noncomputable def cbWords (f : Wb D → Rg D) (g0 g1 : Fin D.K → Wb D → Bool) (e0 e1 : Fin D.K → Rg D)
    (a : Symbol w8) : List (List Bool) :=
  ((List.finRange D.K).map fun i => encRM D.N D.K (f ⬝ᵥ bv (g0 i) + e0 i)) ++
    ((List.finRange D.K).map fun i => encRM D.N D.K
      (f ⬝ᵥ bv (g1 i) + 2 ^ i.val * (setting D).E.X ^ (wSt * a.val) + e1 i))

theorem mem_cbWords {f : Wb D → Rg D} {g0 g1 : Fin D.K → Wb D → Bool} {e0 e1 : Fin D.K → Rg D}
    {a : Symbol w8} : ∀ y ∈ cbWords f g0 g1 e0 e1 a, y.length = D.N * D.K := by
  intro y hy
  rcases List.mem_append.mp hy with h | h <;> exact mem_words h

/-- **The bottom rows of all positions in `l`.** -/
theorem exec_cbSteps (hN : wSt * 2 ^ 7 ≤ 2 * D.N) {α : Type} (l : List α) (w : St)
    (x : α → Symbol w8) (f : Wb D → Rg D) (g0 g1 : α → Fin D.K → Wb D → Bool)
    (e0 e1 : α → Fin D.K → Rg D) (restF b₀ : List Bool)
    (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hA : w rAttr = (l.map fun t => symbolBits w8 (x t)).flatten)
    (h1 : (w r1).length = D.N * D.K) (h1v : decRM D.N D.K (w r1) = 1)
    (hV : w xV = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v)).flatten)
    (hZ : w xZ = (l.map fun t =>
      ((List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g0 t i)).flatten ++
      ((List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g1 t i)).flatten).flatten)
    (hF : w xF = (l.map fun t =>
      ((List.finRange D.K).map fun i => encRM D.N D.K (e0 t i)).flatten ++
      ((List.finRange D.K).map fun i => encRM D.N D.K (e1 t i)).flatten).flatten ++ restF)
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hK : (w cK).length = D.K) (hT : ∀ j < 8, (w (rhoR j)).length = 2 * D.N - wtR j)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K)
    (hBit : (w rBit).length = 1) :
    exec D.N D.K (ofList (l.map fun _ => cbStep)) w xOut = bufW (D.N * D.K) b₀ (ys₀ ++
        (l.map fun t => cbWords f (g0 t) (g1 t) (e0 t) (e1 t) (x t)).flatten) ∧
      exec D.N D.K (ofList (l.map fun _ => cbStep)) w xF = restF ∧
      (exec D.N D.K (ofList (l.map fun _ => cbStep)) w xv).length = D.N * D.K ∧
      (exec D.N D.K (ofList (l.map fun _ => cbStep)) w xBit).length = 1 ∧
      (exec D.N D.K (ofList (l.map fun _ => cbStep)) w xf).length = D.N * D.K ∧
      ∀ j, j ∉ cbW → exec D.N D.K (ofList (l.map fun _ => cbStep)) w j = w j := by
  let Zt : α → List Bool := fun t =>
      ((List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g0 t i)).flatten ++
      ((List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g1 t i)).flatten
  let Ft : α → List Bool := fun t =>
      ((List.finRange D.K).map fun i => encRM D.N D.K (e0 t i)).flatten ++
      ((List.finRange D.K).map fun i => encRM D.N D.K (e1 t i)).flatten
  let Wt : α → List (List Bool) := fun t => cbWords f (g0 t) (g1 t) (e0 t) (e1 t) (x t)
  let P : ℕ → St → Prop := fun i w' =>
    w' rAttr = ((l.drop i).map fun t => symbolBits w8 (x t)).flatten ∧
    w' xZ = ((l.drop i).map Zt).flatten ∧ w' xF = ((l.drop i).map Ft).flatten ++ restF ∧
    w' xOut = bufW (D.N * D.K) b₀ (ys₀ ++ ((l.take i).map Wt).flatten) ∧
    (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
    (w' rBit).length = 1 ∧ ∀ j, j ∉ cbW → w' j = w j
  have key := exec_ofList_map_inv (N := D.N) (K := D.K) l (fun _ => cbStep) P w
    ⟨by simpa using hA, by simpa using hZ, by simpa using hF, by simpa using hOut, hv, hb, hf,
      hBit, fun _ _ => rfl⟩
    (fun i hi w' hP => by
      obtain ⟨h1', h2, h3, h4, h5, h6, h7, h8, h9⟩ := hP
      have hd : ∀ {β : Type} (F : α → List β), ((l.drop i).map F).flatten =
          F l[i] ++ ((l.drop (i + 1)).map F).flatten := fun F => by
        rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons]
      obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := exec_cbStep hN w' (x l[i])
        ((l.drop (i + 1)).map fun t => symbolBits w8 (x t)).flatten f (g0 l[i]) (g1 l[i])
        (e0 l[i]) (e1 l[i]) ((l.drop (i + 1)).map Zt).flatten
        (((l.drop (i + 1)).map Ft).flatten ++ restF) b₀ (ys₀ ++ ((l.take i).map Wt).flatten)
        (fun y hy => by
          rcases List.mem_append.mp hy with h | h
          · exact hys₀ y h
          · obtain ⟨l', hl, hyl⟩ := List.mem_flatten.mp h
            obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
            exact mem_cbWords y hyl)
        (by rw [h1', hd]) (by rw [h9 _ (by decide), h1]) (by rw [h9 _ (by decide), h1v])
        (by rw [h9 _ (by decide), hV]) (by rw [h2, hd, List.append_assoc])
        (by rw [h3, hd, List.append_assoc, List.append_assoc]) h4
        (by rw [h9 _ (by decide), hK])
        (fun j hj => by rw [h9 _ (by simp [cbW, phW, rhoR_val hj, Fin.ext_iff]; omega), hT j hj])
        (by rw [h9 _ (by decide), hCm]) (by rw [h9 _ (by decide), hC1])
        (by rw [h9 _ (by decide), hCNK]) (by rw [h9 _ (by decide), hZero]) h5 h6 h7 h8
      refine ⟨r2, r3, r4, ?_, r5, r6, r7, r8, fun j hj => by rw [r9 j hj, h9 j hj]⟩
      rw [r1, take_succ_of_lt hi, List.map_append, List.flatten_append, List.map_singleton,
        List.flatten_singleton]
      simp only [List.append_assoc]
      rfl)
  obtain ⟨-, -, h3, h4, h5, h6, h7, -, h9⟩ := key
  refine ⟨?_, ?_, h5, h6, h7, h9⟩
  · rw [h4, List.take_length]
  · rw [h3, List.drop_length]; rfl

end AdvancedEncryption.ExpLUT.Prog.RedChal
