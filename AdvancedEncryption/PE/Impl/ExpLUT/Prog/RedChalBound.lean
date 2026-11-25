import PE.Impl.ExpLUT.Prog.RedChalTime

/-!
# The register bounds of the challenge code (package G2, `chalP`)

Three classes of registers (`rk`): the templates of `σ_{g_t}`, `X^{w 2^j}` and the one-bit
template (within the operation area `Mo`), the loop counters (`Bc`), the rest (`Mb`).
`okB` checks a code against the classes; **`okB_spec`** gives `Closed`, `TmOK`, `RepLe`;
**`okB_chalC`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM AdvancedEncryption.ExpLUT.Prog.RedVM

/-- The loop counters. -/
def ctrRegs : List (Fin 200) := [cnt, cK, c2b, cntJ, cAut, cIn, cCol, xCm, xCc, xCnt]

/-- The class of a register. -/
def rk (r : Fin 200) : ℕ :=
  if 37 ≤ r.val ∧ r.val < 45 then 0
  else if 48 ≤ r.val ∧ r.val < 80 then 0
  else if r = xC1 then 0
  else if r ∈ ctrRegs then 1 else 2

/-- The bounds of the classes. -/
def Bf (Mo Bc Mb : ℕ) (r : Fin 200) : ℕ := if rk r = 0 then Mo else if rk r = 1 then Bc else Mb

theorem rk_le (r : Fin 200) : rk r ≤ 2 := by unfold rk; split_ifs <;> omega

theorem Bf_mono {Mo Bc Mb : ℕ} (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) {s d : Fin 200} (h : rk s ≤ rk d) :
    Bf Mo Bc Mb s ≤ Bf Mo Bc Mb d := by
  have := rk_le d
  unfold Bf; split_ifs <;> omega

theorem Mo_le_Bf {Mo Bc Mb : ℕ} (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) (r : Fin 200) : Mo ≤ Bf Mo Bc Mb r := by
  unfold Bf; split_ifs <;> omega

theorem Bf_le {Mo Bc Mb : ℕ} (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) (r : Fin 200) : Bf Mo Bc Mb r ≤ Mb := by
  unfold Bf; split_ifs <;> omega

/-- **The checker.** -/
def okB : Code → Bool
  | .rotB _ _ t => rk t == 0
  | .aut _ _ t => rk t == 0
  | .rhoJ _ _ t => rk t == 0
  | .cp d s => decide (rk s ≤ rk d)
  | .rep t b => decide (rk t ≤ 1) && okB b
  | .seq p q => okB p && okB q
  | .ifb _ p q => okB p && okB q
  | .mul .. => false
  | .digit .. => false
  | .neg .. => false
  | _ => true

theorem okB_spec {Mo N K Bc Mb : ℕ} (hNK : N * K ≤ Mo) (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) :
    ∀ c, okB c = true → Closed Mo N K (Bf Mo Bc Mb) c ∧ TmOK Mo (Bf Mo Bc Mb) c ∧
      RepLe (Bf Mo Bc Mb) Bc c := by
  have hd : ∀ d, N * K ≤ Bf Mo Bc Mb d := fun d => hNK.trans (Mo_le_Bf h1 h2 d)
  have ht : ∀ t, rk t = 0 → Bf Mo Bc Mb t ≤ Mo := fun t h => by simp [Bf, h]
  intro c hc
  induction c with
  | rep t b ih =>
    simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨c1, c2, c3⟩ := ih hc.2
    refine ⟨c1, c2, ?_, c3⟩
    have := rk_le t
    unfold Bf; split_ifs <;> omega
  | seq p q ihp ihq =>
    simp only [okB, Bool.and_eq_true] at hc
    obtain ⟨p1, p2, p3⟩ := ihp hc.1
    obtain ⟨q1, q2, q3⟩ := ihq hc.2
    exact ⟨⟨p1, q1⟩, ⟨p2, q2⟩, ⟨p3, q3⟩⟩
  | ifb t p q ihp ihq =>
    simp only [okB, Bool.and_eq_true] at hc
    obtain ⟨p1, p2, p3⟩ := ihp hc.1
    obtain ⟨q1, q2, q3⟩ := ihq hc.2
    exact ⟨⟨p1, q1⟩, ⟨p2, q2⟩, ⟨p3, q3⟩⟩
  | add d a b | sub d a b | canon d a => exact ⟨hd d, trivial, trivial⟩
  | mul | digit | neg => simp [okB] at hc
  | rotB d a t | aut d a t | rhoJ d a t =>
    simp only [okB, beq_iff_eq] at hc
    exact ⟨⟨hd d, ht t hc⟩, ht t hc, trivial⟩
  | cp d s =>
    simp only [okB, decide_eq_true_eq] at hc
    exact ⟨Bf_mono h1 h2 hc, trivial, trivial⟩
  | mv | drop | clr | tl | nop => exact ⟨trivial, trivial, trivial⟩

theorem okB_ofList : ∀ l : List Code, okB (ofList l) = l.all okB
  | [] => rfl
  | c :: l => by simp [ofList, okB, okB_ofList l]

theorem rk_kR (t : ℕ) : rk (kR t) = 0 := by
  unfold rk kR; simp only [Fin.val_mk]; split_ifs <;> omega

set_option maxRecDepth 20000 in
theorem okB_chalC (D : Dims) : okB (chalC D) = true := by
  have ha : ∀ t : ℕ, okB (autStep t) = true := fun t => by
    simp only [autStep, hashPhase, phaseBody, hashC, hashBody, autPost, okB, rk_kR, beq_self_eq_true,
      Bool.and_true, Bool.true_and]
    decide
  rw [chalC, okB_ofList]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [autC, cbC, okB_ofList, okB_ofList]
  simp only [List.all_append, List.all_map, Function.comp_def, ha]
  have hall : ∀ {α : Type} (l : List α), l.all (fun _ => true) = true := fun l => by simp
  simp only [hall, Bool.and_true]
  decide

/-! ### Counts -/

theorem vmCount_ofList : ∀ l : List Code, vmCount (ofList l) = (l.map vmCount).sum + 1
  | [] => rfl
  | c :: l => by simp [ofList, vmCount, vmCount_ofList l]; omega

theorem vmDepth_ofList_le (d : ℕ) : ∀ l : List Code, (∀ c ∈ l, vmDepth c ≤ d) →
    vmDepth (ofList l) ≤ d
  | [], _ => Nat.zero_le _
  | c :: l, h => by
    simp only [ofList, vmDepth]
    exact max_le (h c List.mem_cons_self)
      (vmDepth_ofList_le d l fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

theorem vmCount_chalC (D : Dims) : vmCount (chalC D) = 1205 + 16 * D.b := by
  have ha : ∀ t, vmCount (autStep t) = 16 := fun t => rfl
  rw [chalC, vmCount_ofList]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [autC, cbC, vmCount_ofList, vmCount_ofList]
  simp only [List.map_append, List.map_map, Function.comp_def, ha, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_const', List.sum_replicate,
    smul_eq_mul, enum_fin, List.length_finRange]
  have : vmCount parseC = 11 := rfl
  have : vmCount bC = 23 := rfl
  have : vmCount hC = 32 := rfl
  have : vmCount cbStep = 68 := rfl
  have : vmCount cinC = 36 := rfl
  have : vmCount cmC = 8 := rfl
  have : vmCount (Code.cp xV rBbar) = 1 := rfl
  have : vmCount (Code.cp xZ ra) = 1 := rfl
  have : vmCount (Code.cp xV rNV) = 1 := rfl
  have : vmCount (Code.cp xZ rZ) = 1 := rfl
  have h16 : (Enum.list (α := Pos)).length = 16 := rfl
  have hw : PE.BranchingProgram.w8.len = 16 := rfl
  simp only [*, List.map_replicate, List.sum_replicate, smul_eq_mul]
  omega

theorem vmDepth_chalC (D : Dims) : vmDepth (chalC D) ≤ 2 := by
  have ha : ∀ t, vmDepth (autStep t) = 2 := fun t => rfl
  refine vmDepth_ofList_le 2 _ fun c hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · refine vmDepth_ofList_le 2 _ fun c hc => ?_
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl) | ⟨t, _, rfl⟩
    · decide
    · decide
    · rw [ha]
  · refine vmDepth_ofList_le 2 _ fun c hc => ?_
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl) | ⟨t, _, rfl⟩
    · decide
    · decide
    · decide
  · decide
  · decide

/-! ### The bounds of the component -/

theorem κD_lt (D : Dims) (t : ℕ) : κD D t < 2 * D.N := by
  unfold κD; exact Nat.mod_lt _ (by have := D.N_pos; omega)

/-- **The template lengths within the classes.** -/
theorem tm_le_Bf (D : Dims) {Mo Bc Mb : ℕ} (hκ : 2 * D.N ≤ Mo) (h1 : 1 ≤ Mo)
    (hCtr : D.K ≤ Bc ∧ D.b * 2 ≤ Bc ∧ nE (Dig D.K × Col D.K) ≤ Bc ∧
      nE (Pos × Dig D.K × Col D.K) ≤ Bc ∧ nE (Col D.K) ≤ Bc ∧ nE (Wb D) ≤ Bc)
    (hBig : ∀ n, tmBase D n ≤ Mb) (r : Fin 200) : tm D r ≤ Bf Mo Bc Mb r := by
  unfold tm Bf rk
  by_cases ha : 48 ≤ r.val ∧ r.val < 80
  · rw [if_pos ha]
    have := κD_lt D (r.val - 48)
    simp only [show ¬(37 ≤ r.val ∧ r.val < 45) by omega, if_false, if_pos ha, if_true]
    omega
  rw [if_neg ha]
  by_cases hb : 37 ≤ r.val ∧ r.val < 45
  · rw [if_pos hb, if_pos hb]; simp only [if_true]; omega
  rw [if_neg hb, if_neg hb, if_neg ha]
  by_cases hc : r = xC1
  · subst hc; simp only [if_true]; show 1 ≤ Mo; exact h1
  rw [if_neg hc]
  by_cases hd : r ∈ ctrRegs
  · rw [if_pos hd]
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false, if_true]
    simp only [ctrRegs, List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hCtr
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.zero_le _
      | exact c1 | exact c2 | exact c3 | exact c4 | exact c5 | exact c6
  · rw [if_neg hd]
    simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, if_false]
    exact hBig _

/-- **The length and clock bounds of the challenge component.** -/
theorem bounds_chalP (D : Dims) {Mo Bc Mb La Lb : ℕ} (hNK : D.N * D.K ≤ Mo) (hK : D.K ≤ Mo)
    (hN : D.N ≤ Mo) (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) (hBc : 1 ≤ Bc) (hLa : La ≤ Mb) (hLb : Lb ≤ Mb)
    (htm : ∀ r, tm D r ≤ Bf Mo Bc Mb r) (hr1 : D.N * D.K ≤ Mb) :
    XProg.lenBoundT (chalP D) (io2 (R := 245) La Lb 0) ≤ io2 (R := 245) Mb 0 0 ∧
      XProg.timeBoundT (chalP D) (io2 (R := 245) La Lb 0) ≤
        210 * ((2 * Mb + 1) * (4 * Mb + 12)) +
          (1205 + 16 * D.b) * (Bc ^ 2 * (2 * Mb + 4 + IB Mb Mo) * 3) + 300 * (2 * Mb + 3) := by
  obtain ⟨hC, hT, hR⟩ := okB_spec hNK h1 h2 (chalC D) (okB_chalC D)
  have hBf : ∀ r, Bf Mo Bc Mb r ≤ Mb := Bf_le h1 h2
  have hra : Bf Mo Bc Mb ra = Mb := rfl
  have hrb : Bf Mo Bc Mb rb = Mb := rfl
  have hr1' : Bf Mo Bc Mb r1 = Mb := rfl
  have hro : Bf Mo Bc Mb xOut = Mb := rfl
  obtain ⟨hl, ht⟩ := RedIO.bounds_ringIO1 hNK hK hN (ra := ra) (rb := rb) (by decide) xOut r1
    (by decide) (by decide)
    (tm D) (chalC D) (Bf Mo Bc Mb) hC La Lb Mb (by rw [hra]; exact hLa) (by rw [hrb]; exact hLb)
    (fun r _ _ _ => htm r) (by rw [hr1']; show D.N * D.K - 1 + 1 ≤ Mb; omega)
    (h1.trans h2) hBf
  rw [hro] at hl
  refine ⟨hl, ht.trans ?_⟩
  have hsup : supB (encB Mo D.N D.K (Bf Mo Bc Mb)) ≤ Mb :=
    XProg.supB_le_of (RedIO.encB_le Mo D.N D.K _ Mb (h1.trans h2) hK hN hNK hBf)
  have hv := vmTime_le Mo D.N D.K (Bf Mo Bc Mb) (2 * Mb + 4) (IB Mb Mo) Bc (by omega) (by omega)
    hBc (chalC D) (leafLe_of hNK hK hN (h1.trans h2) hBf (chalC D) hT) hR
  rw [vmCount_chalC] at hv
  have hd := vmDepth_chalC D
  have hX : Bc ^ vmDepth (chalC D) * (2 * Mb + 4 + IB Mb Mo) * (vmDepth (chalC D) + 1) ≤
      Bc ^ 2 * (2 * Mb + 4 + IB Mb Mo) * 3 :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hBc hd)) (by omega)
  have := hv.trans (Nat.mul_le_mul_left _ hX)
  omega

end AdvancedEncryption.ExpLUT.Prog.RedChal
