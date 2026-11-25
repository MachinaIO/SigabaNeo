import PE.Impl.ExpLUT.Prog.RedChalHWords

/-!
# The blocks `autC`, `cinC`, `cmC` of the challenge code (package G2, `chalP`)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedVM

variable {D : Dims}

/-! ### `c^aut` -/

/-- **The block of `c^aut`.** -/
theorem exec_autC (σ : RawSec D) (w : St) (restF b₀ : List Bool)
    (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hcnt : (w cAut).length = nE (Dig D.K × Col D.K))
    (hk : ∀ t < D.b, w (kR t) = List.replicate (κD D t) false)
    (hBb : w rBbar = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (bbarR D σ v)).flatten)
    (hra : w ra = zAutW σ)
    (hF : w xF = (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
      σ.2.2.2.2.2.1.1 ++ restF)
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    exec D.N D.K (autC D) w xOut =
        bufW (D.N * D.K) b₀ (ys₀ ++ ((Enum.list (α := Fin D.b)).map (autWords σ)).flatten) ∧
      exec D.N D.K (autC D) w xF = restF ∧
      (exec D.N D.K (autC D) w xv).length = D.N * D.K ∧
      (exec D.N D.K (autC D) w xBit).length = 1 ∧
      (exec D.N D.K (autC D) w xf).length = D.N * D.K ∧
      ∀ j, j ∉ xV :: xZ :: phW → exec D.N D.K (autC D) w j = w j := by
  rw [autC, exec_ofList_append]
  set u := Function.update (Function.update w xV (w rBbar)) xZ (Function.update w xV (w rBbar) ra)
    with hu
  have hu' : exec D.N D.K (ofList [.cp xV rBbar, .cp xZ ra]) w = u := rfl
  rw [hu']
  have E : ∀ j, j ≠ xV → j ≠ xZ → u j = w j := fun j h1 h2 => by
    rw [hu, Function.update_of_ne h2, Function.update_of_ne h1]
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := exec_autSteps σ u restF b₀ ys₀ hys₀
    (by rw [E _ (by decide) (by decide), hcnt])
    (fun t ht => by
      rw [E _ (fun h => by have := congrArg Fin.val h; simp [kR] at this; omega)
        (fun h => by have := congrArg Fin.val h; simp [kR] at this; omega), hk t ht])
    (by rw [hu, Function.update_of_ne (by decide), Function.update_self, hBb])
    (by rw [hu, Function.update_self, Function.update_of_ne (by decide), hra])
    (by rw [E _ (by decide) (by decide), hF]) (by rw [E _ (by decide) (by decide), hOut])
    (by rw [E _ (by decide) (by decide), hCm]) (by rw [E _ (by decide) (by decide), hC1])
    (by rw [E _ (by decide) (by decide), hCNK]) (by rw [E _ (by decide) (by decide), hZero])
    (by rw [E _ (by decide) (by decide), hv]) (by rw [E _ (by decide) (by decide), hb])
    (by rw [E _ (by decide) (by decide), hf])
  refine ⟨r1, r2, r3, r4, r5, fun j hj => ?_⟩
  simp only [List.mem_cons, not_or] at hj
  rw [r6 j hj.2.2, E j hj.1 hj.2.1]

/-! ### `c^in` and `c₀` -/

/-- The words of `c^in`. -/
noncomputable def cinWords (σ : RawSec D) : List (List Bool) :=
  (Enum.list (α := Pos × Dig (setting D).τ × Col (setting D).τ)).map fun p => encRM D.N D.K
    (id (bbarR D σ ⬝ᵥ bv (σ.2.2.2.2.2.2 (.inr (.inr (.inl p))))) +
      σ.2.2.2.2.2.1.2.2.1 p.1 p.2.1 p.2.2)

/-- The words of `c₀`. -/
noncomputable def c0Words (σ : RawSec D) : List (List Bool) :=
  (Enum.list (α := Col (setting D).τ)).map fun c => encRM D.N D.K
    (id (bbarR D σ ⬝ᵥ bv (σ.2.2.2.2.2.2 (.inr (.inl c)))) + σ.2.2.2.2.2.1.2.2.2 c)

/-- **The block of `c^in` and `c₀`.** -/
theorem exec_cinC (σ : RawSec D) (w : St) (b₀ : List Bool)
    (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hBb : w rBbar = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (bbarR D σ v)).flatten)
    (hRin : w rRin = zRinW σ) (hR0 : w rR0 = zR0W σ)
    (hcIn : (w cIn).length = nE (Pos × Dig D.K × Col D.K)) (hcCol : (w cCol).length = nE (Col D.K))
    (hF : w xF = (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
      σ.2.2.2.2.2.1.2.2.1 ++ (vecE D (Col D.K)).enc σ.2.2.2.2.2.1.2.2.2)
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    exec D.N D.K cinC w xOut =
        bufW (D.N * D.K) b₀ (ys₀ ++ cinWords σ ++ c0Words σ) ∧
      ∀ j, j ∉ xV :: xZ :: phW → exec D.N D.K cinC w j = w j := by
  simp only [cinC, exec_ofList_cons, exec_ofList_nil]
  set u := Function.update (Function.update (Function.update w xV (w rBbar)) xZ (w rRin)) xCnt
    (w cIn) with hu
  have hu' : exec D.N D.K (.cp xCnt cIn) (exec D.N D.K (.cp xZ rRin)
      (exec D.N D.K (.cp xV rBbar) w)) = u := by
    rw [hu]; simp [exec_cp_eq, Function.update_apply]
  rw [hu']
  have E : ∀ j, j ≠ xV → j ≠ xZ → j ≠ xCnt → u j = w j := fun j h1 h2 h3 => by
    rw [hu, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := exec_hashPhase_enum
    (α := Pos × Dig D.K × Col D.K) cpPost id wr_cpPost u (hpost_cp u)
    (bbarR D σ) (fun p => σ.2.2.2.2.2.2 (.inr (.inr (.inl p))))
    (fun p => σ.2.2.2.2.2.1.2.2.1 p.1 p.2.1 p.2.2) [] ((vecE D (Col D.K)).enc σ.2.2.2.2.2.1.2.2.2)
    b₀ ys₀ hys₀
    (by rw [hu, Function.update_self, hcIn])
    (by rw [hu, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hBb])
    (by rw [hu, Function.update_of_ne (by decide), Function.update_self, hRin, zRinW,
      List.append_nil]; rfl)
    (by rw [E _ (by decide) (by decide) (by decide), hF]
        exact congrArg (· ++ _) (fun3_enc_eq _))
    (by rw [E _ (by decide) (by decide) (by decide), hOut])
    (by rw [E _ (by decide) (by decide) (by decide), hCm])
    (by rw [E _ (by decide) (by decide) (by decide), hC1])
    (by rw [E _ (by decide) (by decide) (by decide), hCNK])
    (by rw [E _ (by decide) (by decide) (by decide), hZero])
    (by rw [E _ (by decide) (by decide) (by decide), hv])
    (by rw [E _ (by decide) (by decide) (by decide), hb])
    (by rw [E _ (by decide) (by decide) (by decide), hf])
  set u2 := exec D.N D.K (hashPhase cpPost) u with hu2
  set u3 := Function.update (Function.update u2 xZ (u2 rR0)) xCnt (u2 cCol) with hu3
  have hu3' : exec D.N D.K (.cp xCnt cCol) (exec D.N D.K (.cp xZ rR0) u2) = u3 := by
    rw [hu3]; simp [exec_cp_eq, Function.update_apply]
  rw [hu3']
  have E3 : ∀ j, j ∉ xV :: xZ :: phW → u3 j = w j := fun j hj => by
    simp only [List.mem_cons, not_or] at hj
    rw [hu3, Function.update_of_ne (fun h => hj.2.2 (by rw [h]; decide)),
      Function.update_of_ne hj.2.1, r7 j hj.2.2, E j hj.1 hj.2.1
        (fun h => hj.2.2 (by rw [h]; decide))]
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := exec_hashPhase_enum
    (α := Col D.K) cpPost id wr_cpPost u3 (hpost_cp u3)
    (bbarR D σ) (fun c => σ.2.2.2.2.2.2 (.inr (.inl c)))
    (fun c => σ.2.2.2.2.2.1.2.2.2 c) [] [] b₀ (ys₀ ++ cinWords σ) (words_app hys₀)
    (by rw [hu3, Function.update_self, r7 _ (by decide), E _ (by decide) (by decide) (by decide),
      hcCol])
    (by rw [hu3, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      r7 _ (by decide), hu, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self, hBb])
    (by rw [hu3, Function.update_of_ne (by decide), Function.update_self, r7 _ (by decide),
      E _ (by decide) (by decide) (by decide), hR0, zR0W, List.append_nil]; rfl)
    (by rw [hu3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), r3,
      List.append_nil]; exact vecE_enc_eq _)
    (by rw [hu3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), r1]; rfl)
    (by rw [E3 _ (by decide), hCm]) (by rw [E3 _ (by decide), hC1])
    (by rw [E3 _ (by decide), hCNK]) (by rw [E3 _ (by decide), hZero])
    (by rw [hu3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), r4])
    (by rw [hu3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), r5])
    (by rw [hu3, Function.update_of_ne (by decide), Function.update_of_ne (by decide), r6])
  refine ⟨by rw [q1]; rfl, fun j hj => ?_⟩
  have hj' : j ∉ phW := fun h => hj (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  rw [q7 j hj', E3 j hj]

/-! ### `c_m` -/

theorem decRM_half {x : List Bool} (hx : x.length = D.N * D.K) (h1 : decRM D.N D.K x = 1) :
    decRM D.N D.K (rotBW D.N D.K 1 x) = half D := by
  have hK := D.K_pos
  have := decRM_rotBW (N := D.N) (K := D.K) (i := D.K - 1) hx (Nat.sub_le _ _)
  rw [show D.K - (D.K - 1) = 1 by omega, h1] at this
  rw [this, half, Algebra.smul_def, mul_one]

/-- **The block of `c_m`.** -/
theorem exec_cmC (w : St) (vd d2 : Rg D) (μ : Bool) (b₀ : List Bool) (ys₀ : List (List Bool))
    (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hVd : w rVd = encRM D.N D.K vd) (hd2 : w rd2 = encRM D.N D.K d2)
    (h1 : (w r1).length = D.N * D.K) (h1v : decRM D.N D.K (w r1) = 1)
    (hC1 : (w xC1).length = 1) (hrb : w rb = [μ]) (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hCNK : (w xCNK).length = D.N * D.K) :
    exec D.N D.K cmC w xOut =
      bufW (D.N * D.K) b₀ (ys₀ ++ [encRM D.N D.K (vd + d2 + half D * msgR D μ)]) := by
  have hK := D.K_pos
  have hl := length_encRM D.N D.K
  simp only [cmC, exec_ofList_cons, exec_ofList_nil]
  rw [exec_add_eq (d := xS) (by rw [hVd, hl]) (by rw [hd2, hl])]
  set s := addRMW D.N D.K (w rVd) (w rd2) with hs
  have hsl : s.length = D.N * D.K := length_addRMW _ _ (by rw [hVd, hl]) _
  have hsv : decRM D.N D.K s = vd + d2 := by
    rw [hs, decRM_addRMW (by rw [hVd, hl]) (by rw [hd2, hl]), hVd, hd2, decRM_encRM hK,
      decRM_encRM hK]
  have erot : exec D.N D.K (.rotB rHalf r1 xC1) (Function.update w xS s) =
      Function.update (Function.update w xS s) rHalf (rotBW D.N D.K 1 (w r1)) := by
    simp only [exec, Function.update_apply]
    simp [hC1, opd_eq h1]
  rw [erot]
  set u := Function.update (Function.update w xS s) rHalf (rotBW D.N D.K 1 (w r1)) with hu
  have hhl : (u rHalf).length = D.N * D.K := by simp [hu, length_rotBW _ _ _ h1]
  have hhv : decRM D.N D.K (u rHalf) = half D := by simp [hu, decRM_half h1 h1v]
  have hus : u xS = s := by simp [hu, Function.update_apply]
  set t := if μ then addRMW D.N D.K s (u rHalf) else s with ht
  have htl : t.length = D.N * D.K := by
    rw [ht]; split_ifs
    · exact length_addRMW _ _ hsl _
    · exact hsl
  have htv : decRM D.N D.K t = vd + d2 + half D * msgR D μ := by
    rw [ht]; cases μ
    · simp [hsv, msgR]
    · simp [decRM_addRMW hsl hhl, hsv, hhv, msgR]
  have eif : exec D.N D.K (.ifb rb (.add xS xS rHalf) .nop) u = Function.update u xS t := by
    have hrbu : u rb = [μ] := by simp [hu, Function.update_apply, hrb]
    cases μ
    · simp only [exec, hrbu, hd, List.headD_cons, Bool.false_eq_true, ite_false]
      rw [show t = s from by simp [ht], ← hus, Function.update_eq_self]
    · simp only [exec, hrbu, hd, List.headD_cons, ite_true]
      rw [opd_eq (by rw [hus]; exact hsl), opd_eq hhl, hus]
      rfl
  rw [eif, exec_canon_eq hK (by simp [htl])]
  rw [exec_push (d := xOut) (s := xO) (c := xCNK) (by decide) (W := D.N * D.K) (b₀ := b₀)
    (ys := ys₀) hys₀ (by simp [Function.update_apply, hu, hOut])
    (by simp [Function.update_apply, length_encRM]) (by simp [Function.update_apply, hu, hCNK])]
  simp [htv]

/-! ### The bottom rows of `C^in` -/

theorem encAttribute_eq (x : Attribute w8) :
    encAttribute w8 x = ((Enum.list (α := Pos)).map fun t => symbolBits w8 (x t)).flatten := by
  show (List.ofFn x).flatMap (symbolBits w8) = _
  rw [List.ofFn_eq_map, List.flatMap_def, List.map_map]
  rfl

theorem zZW_eq (σ : RawSec D) : zZW σ = ((Enum.list (α := Pos)).map fun t =>
    ((List.finRange D.K).map fun i =>
      (Enum.list (α := Wb D)).map (σ.2.2.2.2.2.2 (.inl (t, (0, i))))).flatten ++
    ((List.finRange D.K).map fun i =>
      (Enum.list (α := Wb D)).map (σ.2.2.2.2.2.2 (.inl (t, (1, i))))).flatten).flatten := by
  rw [zZW, zrBlocks_prod]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [zrBlocks, ← List.flatten_append]
  congr 1
  exact enum_col_map (fun c : Col D.K => (Enum.list (α := Wb D)).map
    (σ.2.2.2.2.2.2 (.inl (t, c))))

theorem flCb_eq (σ : RawSec D) :
    (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc σ.2.2.2.2.2.1.2.1 =
      ((Enum.list (α := Pos)).map fun t =>
        ((List.finRange D.K).map fun i => encRM D.N D.K (σ.2.2.2.2.2.1.2.1 t (0, i))).flatten ++
        ((List.finRange D.K).map fun i =>
          encRM D.N D.K (σ.2.2.2.2.2.1.2.1 t (1, i))).flatten).flatten := by
  refine (fun_enc_eq _ _).trans ?_
  congr 1
  refine List.map_congr_left fun t _ => ?_
  refine (vecE_enc_eq _).trans ?_
  rw [← List.flatten_append]
  congr 1
  exact enum_col_map (fun c : Col D.K => encRM D.N D.K (σ.2.2.2.2.2.1.2.1 t c))

/-- **The block of the bottom rows of `C^in`.** -/
theorem exec_cbC (hN : wSt * 2 ^ 7 ≤ 2 * D.N) (σ : RawSec D) (w : St) (restF b₀ : List Bool)
    (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hNV : w rNV =
      ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (-σ.2.1.vB (.inl v))).flatten)
    (hZ : w rZ = zZW σ) (hA : w rAttr = encAttribute w8 σ.1)
    (hF : w xF = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc σ.2.2.2.2.2.1.2.1 ++ restF)
    (h1 : (w r1).length = D.N * D.K) (h1v : decRM D.N D.K (w r1) = 1)
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hK : (w cK).length = D.K) (hT : ∀ j < 8, (w (rhoR j)).length = 2 * D.N - wtR j)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K)
    (hBit : (w rBit).length = 1) :
    exec D.N D.K cbC w xOut = bufW (D.N * D.K) b₀ (ys₀ ++ ((Enum.list (α := Pos)).map fun t =>
        cbWords (fun v => -σ.2.1.vB (.inl v)) (fun i => σ.2.2.2.2.2.2 (.inl (t, (0, i))))
          (fun i => σ.2.2.2.2.2.2 (.inl (t, (1, i)))) (fun i => σ.2.2.2.2.2.1.2.1 t (0, i))
          (fun i => σ.2.2.2.2.2.1.2.1 t (1, i)) (σ.1 t)).flatten) ∧
      exec D.N D.K cbC w xF = restF ∧
      (exec D.N D.K cbC w xv).length = D.N * D.K ∧ (exec D.N D.K cbC w xBit).length = 1 ∧
      (exec D.N D.K cbC w xf).length = D.N * D.K ∧
      ∀ j, j ∉ xV :: xZ :: cbW → exec D.N D.K cbC w j = w j := by
  rw [cbC, exec_ofList_append]
  set u := Function.update (Function.update w xV (w rNV)) xZ (Function.update w xV (w rNV) rZ)
    with hu
  have hu' : exec D.N D.K (ofList [.cp xV rNV, .cp xZ rZ]) w = u := rfl
  rw [hu']
  have E : ∀ j, j ≠ xV → j ≠ xZ → u j = w j := fun j h1 h2 => by
    rw [hu, Function.update_of_ne h2, Function.update_of_ne h1]
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := exec_cbSteps hN (Enum.list (α := Pos)) u σ.1
    (fun v => -σ.2.1.vB (.inl v)) (fun t i => σ.2.2.2.2.2.2 (.inl (t, (0, i))))
    (fun t i => σ.2.2.2.2.2.2 (.inl (t, (1, i)))) (fun t i => σ.2.2.2.2.2.1.2.1 t (0, i))
    (fun t i => σ.2.2.2.2.2.1.2.1 t (1, i)) restF b₀ ys₀ hys₀
    (by rw [E _ (by decide) (by decide), hA, encAttribute_eq])
    (by rw [E _ (by decide) (by decide), h1]) (by rw [E _ (by decide) (by decide), h1v])
    (by rw [hu, Function.update_of_ne (by decide), Function.update_self, hNV])
    (by rw [hu, Function.update_self, Function.update_of_ne (by decide), hZ]; exact zZW_eq σ)
    (by rw [E _ (by decide) (by decide), hF]; exact congrArg (· ++ restF) (flCb_eq σ))
    (by rw [E _ (by decide) (by decide), hOut]) (by rw [E _ (by decide) (by decide), hK])
    (fun j hj => by
      rw [E _ (by simp [rhoR_val hj, Fin.ext_iff]; omega)
        (by simp [rhoR_val hj, Fin.ext_iff]; omega), hT j hj])
    (by rw [E _ (by decide) (by decide), hCm]) (by rw [E _ (by decide) (by decide), hC1])
    (by rw [E _ (by decide) (by decide), hCNK]) (by rw [E _ (by decide) (by decide), hZero])
    (by rw [E _ (by decide) (by decide), hv]) (by rw [E _ (by decide) (by decide), hb])
    (by rw [E _ (by decide) (by decide), hf]) (by rw [E _ (by decide) (by decide), hBit])
  refine ⟨r1, r2, r3, r4, r5, fun j hj => ?_⟩
  simp only [List.mem_cons, not_or] at hj
  rw [r6 j hj.2.2, E j hj.1 hj.2.1]

end AdvancedEncryption.ExpLUT.Prog.RedChal
