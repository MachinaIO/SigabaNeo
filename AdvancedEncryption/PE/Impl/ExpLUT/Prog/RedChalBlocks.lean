import PE.Impl.ExpLUT.Prog.RedChalRows
open SigabaNeo.Tape.RingVM.Hash
/-!
# The blocks `bC` and `hC` of the challenge code (package G2, `chalP`)

* **`exec_bC`**: `b = v_B + B⁽²⁾` (canonical words, along `Enum BCol`), the vectors `b̄` and `−v̄_B`,
  `v_d` into `rVd`, the helper rows left in `rV`;
* **`exec_hC`**: the helpers `h_k = v_{H,k} − G⁽²⁾ + H⁽²⁾_k`, along `Enum Jh` and `Enum Col`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### The first rows -/

theorem rows_gt : D.mb + D.K + 1 ≤ (circParamsD D).rows := by
  rw [rows_eq, mCirc]; omega

/-- **The first rows**: the columns of `B` and `d`. -/
theorem vsV_split (i : CInst D) :
    vsV i = (Enum.list (α := Wb D)).map (fun v => encRM D.N D.K (i.vB (.inl v))) ++
      ((Enum.list (α := Fin D.K)).map (fun g => encRM D.N D.K (i.vB (.inr g))) ++
        (encRM D.N D.K i.vd :: (vsV i).drop (D.mb + D.K + 1))) := by
  have hl : D.mb + D.K + 1 ≤ (vsV i).length := by rw [length_vsV]; exact rows_gt
  have h1 : (vsV i).take D.mb =
      (Enum.list (α := Wb D)).map (fun v => encRM D.N D.K (i.vB (.inl v))) := by
    refine List.ext_getElem (by simp [enum_fin]; omega) fun n h1 h2 => ?_
    have hn : n < D.mb := by simp [enum_fin] at h2; exact h2
    rw [List.getElem_take, List.getElem_map]
    simp only [enum_fin, List.getElem_finRange]
    exact vsV_col i ⟨n, hn⟩ (by omega)
  have h2 : ((vsV i).drop D.mb).take D.K =
      (Enum.list (α := Fin D.K)).map (fun g => encRM D.N D.K (i.vB (.inr g))) := by
    refine List.ext_getElem (by simp [enum_fin]; omega) fun n h1 h2 => ?_
    have hn : n < D.K := by simp [enum_fin] at h2; exact h2
    rw [List.getElem_take, List.getElem_drop]
    refine (vsV_gad i ⟨n, hn⟩ (by simp; omega)).trans ?_
    have : (Enum.list (α := Fin D.K))[n]'(by simpa [enum_fin] using hn) = ⟨n, hn⟩ := by
      show (List.finRange D.K)[n]'(by simpa using hn) = _
      simp
    refine Eq.trans ?_ (List.getElem_map _).symm
    exact congrArg (fun g : Fin D.K => encRM D.N D.K (i.vB (.inr g))) this.symm
  have h3 : (vsV i).drop (D.mb + D.K) = encRM D.N D.K i.vd :: (vsV i).drop (D.mb + D.K + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), vsV_d i (by omega)]
  rw [← h1, ← h2, ← h3, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

/-! ### `b` -/

theorem map_sum_split {α β γ : Type} (F : α ⊕ β → γ) (l₁ : List α) (l₂ : List β) :
    (l₁.map Sum.inl ++ l₂.map Sum.inr).map F = l₁.map (fun a => F (.inl a)) ++
      l₂.map (fun b => F (.inr b)) := by
  simp [List.map_append, List.map_map, Function.comp_def]

/-- The registers `bC` writes. -/
def bW : List (Fin 200) := [cnt, xv, rV, xf, rB2, xS, xO, tmpO, rBbar, tmpN, rNV, xOut, rVd]

/-- **The block of `b`.** -/
theorem exec_bC (σ : RawSec D) (w : St) (b₀ : List Bool) (ys₀ : List (List Bool))
    (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hV : w rV = instVW σ) (hB : w rB2 = b2W σ) (hO : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hBb : w rBbar = List.replicate (nE (Wb D) * (D.N * D.K)) false)
    (hNV : w rNV = List.replicate (nE (Wb D) * (D.N * D.K)) false)
    (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hNK : (w xCNK).length = D.N * D.K) (hv : (w xv).length = D.N * D.K)
    (hf : (w xf).length = D.N * D.K) (hCm : (w xCm).length = nE (Wb D))
    (hK : (w cK).length = D.K) (hVd : (w rVd).length = D.N * D.K) :
    exec D.N D.K bC w xOut = bufW (D.N * D.K) b₀ (ys₀ ++
        (Enum.list (α := BCol (Wb D) D.K)).map fun c =>
          encRM D.N D.K (σ.2.1.vB c + σ.2.2.1 c)) ∧
      exec D.N D.K bC w rBbar =
        ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (bbarR D σ v)).flatten ∧
      exec D.N D.K bC w rNV =
        ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (-σ.2.1.vB (.inl v))).flatten ∧
      exec D.N D.K bC w rV = ((vsV σ.2.1).drop (D.mb + D.K + 1)).flatten ∧
      exec D.N D.K bC w rVd = encRM D.N D.K σ.2.1.vd ∧
      (exec D.N D.K bC w xv).length = D.N * D.K ∧ (exec D.N D.K bC w xf).length = D.N * D.K ∧
      ∀ j, j ∉ bW → exec D.N D.K bC w j = w j := by
  have hKp := D.K_pos
  set i := σ.2.1
  set B2 := σ.2.2.1
  have hV' : w rV = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (i.vB (.inl v))).flatten ++
      (((Enum.list (α := Fin D.K)).map fun g => encRM D.N D.K (i.vB (.inr g))).flatten ++
        (encRM D.N D.K i.vd ++ ((vsV i).drop (D.mb + D.K + 1)).flatten)) := by
    rw [hV, instVW_eq]
    conv_lhs => rw [vsV_split i]
    simp only [List.flatten_append, List.flatten_cons, List.append_assoc]
  have hB' : w rB2 = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (B2 (.inl v))).flatten ++
      (((Enum.list (α := Fin D.K)).map fun g => encRM D.N D.K (B2 (.inr g))).flatten ++ []) := by
    rw [hB, b2W, vecE_enc_eq, enum_sum, List.map_append, List.flatten_append, List.map_map,
      List.map_map, List.append_nil]
    rfl
  simp only [bC, exec_ofList_cons, exec_ofList_nil]
  set w1 := Function.update w cnt (w xCm) with hw1
  have hw1' : exec D.N D.K (.cp cnt xCm) w = w1 := rfl
  rw [hw1']
  have E1 : ∀ j, j ≠ cnt → w1 j = w j := fun j hj => Function.update_of_ne hj _ _
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := exec_bLoop1 hKp (Enum.list (α := Wb D))
    (fun v => i.vB (.inl v)) (fun v => B2 (.inl v)) w1
    (((Enum.list (α := Fin D.K)).map fun g => encRM D.N D.K (i.vB (.inr g))).flatten ++
        (encRM D.N D.K i.vd ++ ((vsV i).drop (D.mb + D.K + 1)).flatten))
    (((Enum.list (α := Fin D.K)).map fun g => encRM D.N D.K (B2 (.inr g))).flatten ++ [])
    b₀ ys₀ hys₀
    (by rw [hw1, Function.update_self, hCm]) (by rw [E1 _ (by decide), hV'])
    (by rw [E1 _ (by decide), hB']) (by rw [E1 _ (by decide), hO])
    (by rw [E1 _ (by decide), hBb]) (by rw [E1 _ (by decide), hNV])
    (by rw [E1 _ (by decide), hZero]) (by rw [E1 _ (by decide), hNK])
    (by rw [E1 _ (by decide), hv]) (by rw [E1 _ (by decide), hf])
  set w2 := exec D.N D.K (.rep cnt bBody1) w1 with hw2
  set w3 := Function.update w2 cnt (w2 cK) with hw3
  have hw3' : exec D.N D.K (.cp cnt cK) w2 = w3 := rfl
  rw [hw3']
  have E3 : ∀ j, j ≠ cnt → w3 j = w2 j := fun j hj => Function.update_of_ne hj _ _
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := exec_bLoop2 hKp (Enum.list (α := Fin D.K))
    (fun g => i.vB (.inr g)) (fun g => B2 (.inr g)) w3
    (encRM D.N D.K i.vd ++ ((vsV i).drop (D.mb + D.K + 1)).flatten) [] b₀
    (ys₀ ++ (Enum.list (α := Wb D)).map fun v => encRM D.N D.K (i.vB (.inl v) + B2 (.inl v)))
    (words_app hys₀)
    (by rw [hw3, Function.update_self, p8 _ (by decide), E1 _ (by decide), hK, enum_fin,
      List.length_finRange])
    (by rw [E3 _ (by decide)]; exact p1) (by rw [E3 _ (by decide)]; exact p2)
    (by rw [E3 _ (by decide), p3])
    (by rw [E3 _ (by decide), p8 _ (by decide), E1 _ (by decide), hNK])
    (by rw [E3 _ (by decide), p6]) (by rw [E3 _ (by decide), p7])
  set w4 := exec D.N D.K (.rep cnt bBody2) w3 with hw4
  rw [exec_mv_pop (d := rVd) (s := rV) (c := xCNK) (v := encRM D.N D.K i.vd)
    (L := ((vsV i).drop (D.mb + D.K + 1)).flatten) (by decide)
    (by rw [q6 _ (by decide), E3 _ (by decide), p8 _ (by decide), E1 _ (by decide),
      q6 _ (by decide), E3 _ (by decide), p8 _ (by decide), E1 _ (by decide), hVd, hNK])
    (by rw [q6 _ (by decide), E3 _ (by decide), p8 _ (by decide), E1 _ (by decide), hNK,
      length_encRM]) q1]
  have F4 : ∀ j, j ∉ bW → w4 j = w j := fun j hj => by
    simp only [bW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [q6 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.2.2.2.1]), E3 j hj.1,
      p8 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.2.2.2.1]), E1 j hj.1]
  refine ⟨?_, ?_, ?_, by simp [Function.update_apply], by simp [Function.update_apply], ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), q3]
    show _ = bufW (D.N * D.K) b₀ (ys₀ ++ (((Enum.list (α := Wb D)).map Sum.inl ++
      (Enum.list (α := Fin D.K)).map Sum.inr).map fun c => encRM D.N D.K (i.vB c + B2 c)))
    rw [List.append_assoc]
    exact congrArg (fun l => bufW (D.N * D.K) b₀ (ys₀ ++ l)) (map_sum_split (fun c : BCol (Wb D) D.K => encRM D.N D.K (i.vB c + B2 c))
      (Enum.list (α := Wb D)) (Enum.list (α := Fin D.K))).symm
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), q6 _ (by decide),
      E3 _ (by decide), p4]
    rfl
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), q6 _ (by decide),
      E3 _ (by decide), p5]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), q4]
  · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), q5]
  · intro j hj
    have h1 : j ≠ rVd := fun h => hj (by rw [h]; decide)
    have h2 : j ≠ rV := fun h => hj (by rw [h]; decide)
    rw [Function.update_of_ne h1, Function.update_of_ne h2, F4 j hj]

/-! ### The helpers -/

/-- `H⁽²⁾` on the first gadget half, on indices. -/
noncomputable def F0 (σ : RawSec D) (j i : ℕ) : Rg D :=
  if h : j < D.b * 2 ∧ i < D.K then σ.2.2.2.1 (jhE D ⟨j, h.1⟩) (0, ⟨i, h.2⟩) else 0

/-- `H⁽²⁾` on the second gadget half, on indices. -/
noncomputable def F1 (σ : RawSec D) (j i : ℕ) : Rg D :=
  if h : j < D.b * 2 ∧ i < D.K then σ.2.2.2.1 (jhE D ⟨j, h.1⟩) (1, ⟨i, h.2⟩) else 0

/-- The registers `hC` writes. -/
def hW : List (Fin 200) := rS1 :: rS0 :: cntJ :: hOW

/-- **The block of the helpers** (words on indices). -/
theorem exec_hC (hb : 1 ≤ D.b) (σ : RawSec D) (w : St) (b₀ : List Bool) (ys₀ : List (List Bool))
    (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hV : w rV = ((vsV σ.2.1).drop (D.mb + D.K + 1)).flatten)
    (hH : w rH2 = ((List.range (D.b * 2)).map (hblk D.K (F0 σ) (F1 σ))).flatten)
    (hO : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hHalf : (w cHalf).length = D.K * (D.b * 2) * (D.N * D.K))
    (h2b : (w c2b).length = D.b * 2) (hK : (w cK).length = D.K)
    (hSk : (w cSkip).length = (D.b * 2 - 1) * (D.N * D.K))
    (h1 : (w r1).length = D.N * D.K) (h1v : decRM D.N D.K (w r1) = 1)
    (hNK : (w xCNK).length = D.N * D.K) (hv : (w xv).length = D.N * D.K)
    (hf : (w xf).length = D.N * D.K) :
    exec D.N D.K hC w xOut = bufW (D.N * D.K) b₀ (ys₀ ++ ((List.range (D.b * 2)).map
      (hout ((vsV σ.2.1).drop (D.mb + D.K + 1)) D.K (D.b * 2) (D.K * (D.b * 2)) 0
        (F0 σ) (F1 σ))).flatten) ∧
      (exec D.N D.K hC w xv).length = D.N * D.K ∧ (exec D.N D.K hC w xf).length = D.N * D.K ∧
      ∀ j, j ∉ hW → exec D.N D.K hC w j = w j := by
  have hKp := D.K_pos
  have hb1 : 1 ≤ D.b * 2 := by omega
  set vs := (vsV σ.2.1).drop (D.mb + D.K + 1) with hvs
  have hvsl : vs.length = D.K * (D.b * 2) + D.K * (D.b * 2) := by
    rw [hvs, List.length_drop, length_vsV, rows_eq, mCirc]; omega
  have hvsw : ∀ x ∈ vs, x.length = D.N * D.K := fun x hx => mem_vsV x (List.mem_of_mem_drop hx)
  simp only [hC, exec_ofList_cons, exec_ofList_nil]
  set w4 := Function.update (Function.update (Function.update (Function.update w rS1 (w rV)) rS0
    (w rV)) rS0 ((w rV).drop (w cHalf).length)) cntJ (w c2b) with hw4
  have hw4' : exec D.N D.K (.cp cntJ c2b) (exec D.N D.K (.drop rS0 cHalf)
      (exec D.N D.K (.cp rS0 rV) (exec D.N D.K (.cp rS1 rV) w))) = w4 := by
    rw [hw4, exec_cp_eq, exec_drop_eq (by decide), exec_cp_eq, exec_cp_eq]
    simp [Function.update_apply]
  rw [hw4']
  have E4 : ∀ j, j ∉ [rS1, rS0, cntJ] → w4 j = w j := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [hw4, Function.update_apply, hj.1, hj.2.1, hj.2.2]
  obtain ⟨p1, p2, p3, p4, p5⟩ := exec_hOuterLoop hKp D.K (D.b * 2) (D.K * (D.b * 2)) 0 vs hvsw hb1
    (fun j hj i hi => by
      rw [hvsl]
      have : i * (D.b * 2) + D.b * 2 ≤ D.K * (D.b * 2) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
      omega)
    (fun j hj i hi => by
      rw [hvsl]
      have : i * (D.b * 2) + D.b * 2 ≤ D.K * (D.b * 2) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
      omega)
    (F0 σ) (F1 σ) w4 [] b₀ ys₀ hys₀
    (by simp [hw4]; exact h2b) (by rw [E4 _ (by decide), hK])
    (by
      have : w4 rS0 = (w rV).drop (w cHalf).length := by simp [hw4, Function.update_apply]
      rw [this, hV, hHalf]
      exact drop_flatten_words hvsw _)
    (by simp [hw4, Function.update_apply, hV])
    (by rw [E4 _ (by decide), hSk]) (by rw [E4 _ (by decide), hH]; simp)
    (by rw [E4 _ (by decide), hO]) (by rw [E4 _ (by decide), h1])
    (by rw [E4 _ (by decide), h1v]) (by rw [E4 _ (by decide), hNK])
    (by rw [E4 _ (by decide), hv]) (by rw [E4 _ (by decide), hf])
  refine ⟨p2, p3, p4, fun j hj => ?_⟩
  simp only [hW, List.mem_cons, not_or] at hj
  rw [p5 j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]), E4 j (by simp [hj.1, hj.2.1, hj.2.2.1])]

end AdvancedEncryption.ExpLUT.Prog.RedChal
