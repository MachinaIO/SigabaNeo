import PE.Impl.ExpLUT.Prog.RedPubPTime

/-!
# The register bounds of the public-key code (package G2, `pubP`)

(Adapted from `RedChalBound`, with `digit` allowed.)

Three classes of registers (`rk`): the templates of `σ_{g_t}`, `X^{w 2^j}` and the one-bit
template (within the operation area `Mo`), the loop counters (`Bc`), the rest (`Mb`).
`pokB` checks a code against the classes; **`pokB_spec`** gives `Closed`, `PTmOK`, `PRepLe`;
**`pokB_chalC`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM AdvancedEncryption.ExpLUT.Prog.RedVM

/-- The loop counters. -/
def pctrRegs : List (Fin 200) := [cnt, cntJ, cntP, cntC, cntI, cJ, cPos, cCol, xCm, xCc, xCnt]

/-- The class of a register. -/
def prk (r : Fin 200) : ℕ :=
  if 72 ≤ r.val ∧ r.val < 112 then 0
  else if r = xC1 ∨ r = cK ∨ r = rI ∨ r = rRem then 0
  else if r ∈ pctrRegs then 1 else 2

/-- The bounds of the classes. -/
def pBf (Mo Bc Mb : ℕ) (r : Fin 200) : ℕ := if prk r = 0 then Mo else if prk r = 1 then Bc else Mb

theorem prk_le (r : Fin 200) : prk r ≤ 2 := by unfold prk; split_ifs <;> omega

theorem pBf_mono {Mo Bc Mb : ℕ} (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) {s d : Fin 200} (h : prk s ≤ prk d) :
    pBf Mo Bc Mb s ≤ pBf Mo Bc Mb d := by
  have := prk_le d
  unfold pBf; split_ifs <;> omega

theorem Mo_le_pBf {Mo Bc Mb : ℕ} (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) (r : Fin 200) : Mo ≤ pBf Mo Bc Mb r := by
  unfold pBf; split_ifs <;> omega

theorem pBf_le {Mo Bc Mb : ℕ} (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) (r : Fin 200) : pBf Mo Bc Mb r ≤ Mb := by
  unfold pBf; split_ifs <;> omega

/-- **The checker.** -/
def pokB : Code → Bool
  | .rotB _ _ t => prk t == 0
  | .aut _ _ t => prk t == 0
  | .rhoJ _ _ t => prk t == 0
  | .cp d s => decide (prk s ≤ prk d)
  | .rep t b => decide (prk t ≤ 1) && pokB b
  | .seq p q => pokB p && pokB q
  | .ifb _ p q => pokB p && pokB q
  | .digit _ _ t => prk t == 0
  | .mul .. => false
  | .neg .. => false
  | _ => true

theorem pokB_spec {Mo N K Bc Mb : ℕ} (hNK : N * K ≤ Mo) (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) :
    ∀ c, pokB c = true → Closed Mo N K (pBf Mo Bc Mb) c ∧ PTmOK Mo (pBf Mo Bc Mb) c ∧
      PRepLe (pBf Mo Bc Mb) Bc c := by
  have hd : ∀ d, N * K ≤ pBf Mo Bc Mb d := fun d => hNK.trans (Mo_le_pBf h1 h2 d)
  have ht : ∀ t, prk t = 0 → pBf Mo Bc Mb t ≤ Mo := fun t h => by simp [pBf, h]
  intro c hc
  induction c with
  | rep t b ih =>
    simp only [pokB, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨c1, c2, c3⟩ := ih hc.2
    refine ⟨c1, c2, ?_, c3⟩
    have := prk_le t
    unfold pBf; split_ifs <;> omega
  | seq p q ihp ihq =>
    simp only [pokB, Bool.and_eq_true] at hc
    obtain ⟨p1, p2, p3⟩ := ihp hc.1
    obtain ⟨q1, q2, q3⟩ := ihq hc.2
    exact ⟨⟨p1, q1⟩, ⟨p2, q2⟩, ⟨p3, q3⟩⟩
  | ifb t p q ihp ihq =>
    simp only [pokB, Bool.and_eq_true] at hc
    obtain ⟨p1, p2, p3⟩ := ihp hc.1
    obtain ⟨q1, q2, q3⟩ := ihq hc.2
    exact ⟨⟨p1, q1⟩, ⟨p2, q2⟩, ⟨p3, q3⟩⟩
  | add d a b | sub d a b | canon d a => exact ⟨hd d, trivial, trivial⟩
  | mul | neg => simp [pokB] at hc
  | rotB d a t | aut d a t | rhoJ d a t | digit d a t =>
    simp only [pokB, beq_iff_eq] at hc
    exact ⟨⟨hd d, ht t hc⟩, ht t hc, trivial⟩
  | cp d s =>
    simp only [pokB, decide_eq_true_eq] at hc
    exact ⟨pBf_mono h1 h2 hc, trivial, trivial⟩
  | mv | drop | clr | tl | nop => exact ⟨trivial, trivial, trivial⟩

theorem pokB_ofList : ∀ l : List Code, pokB (ofList l) = l.all pokB
  | [] => rfl
  | c :: l => by simp [ofList, pokB, pokB_ofList l]

theorem prk_kR (t : ℕ) : prk (kR t) = 0 := by
  unfold prk kR; simp only [Fin.val_mk]; split_ifs <;> omega

/-! ### Counts -/

theorem pvmCount_ofList : ∀ l : List Code, vmCount (ofList l) = (l.map vmCount).sum + 1
  | [] => rfl
  | c :: l => by simp [ofList, vmCount, pvmCount_ofList l]; omega

theorem pvmDepth_ofList_le (d : ℕ) : ∀ l : List Code, (∀ c ∈ l, pvmDepth c ≤ d) →
    pvmDepth (ofList l) ≤ d
  | [], _ => Nat.zero_le _
  | c :: l, h => by
    simp only [ofList, pvmDepth]
    exact max_le (h c List.mem_cons_self)
      (pvmDepth_ofList_le d l fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

/-! ### The code of the public key -/

theorem pokB_autT (t : ℕ) : pokB (autT t) = true := by
  have hp : prk (kR t) = 0 := prk_kR t
  simp (config := {decide := true}) only [autT, autPre, strC, aBodyK, aBodyV0, aBodyV1, digRow,
    cBody, dBody, autPost, rowSetC, rowC, halfC, gpost, hashPhase, phaseBody, hashC, hashBody,
    cpPost, pokB_ofList, pokB, hp, List.all_cons, List.all_nil, beq_self_eq_true, Bool.and_true,
    Bool.true_and, ↓reduceIte, if_true, if_false]

set_option maxRecDepth 20000 in
theorem pokB_pubC (D : Dims) : pokB (pubC D) = true := by
  rw [pubC, pokB_ofList]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [autC, pokB_ofList]
  simp only [List.all_append, List.all_map, Function.comp_def, pokB_autT]
  have hall : ∀ {α : Type} (l : List α), l.all (fun _ => true) = true := fun l => by simp
  simp only [hall, Bool.and_true]
  decide

theorem vmCount_autT (t : ℕ) : vmCount (autT t) = vmCount (autT 0) := rfl
theorem pvmDepth_autT (t : ℕ) : pvmDepth (autT t) = pvmDepth (autT 0) := rfl

theorem vmCount_pubC (D : Dims) : vmCount (pubC D) = 478 + 241 * D.b := by
  rw [pubC, pvmCount_ofList]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [autC, pvmCount_ofList]
  simp only [List.map_append, List.map_map, Function.comp_def, vmCount_autT, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.map_const', List.sum_replicate,
    smul_eq_mul, List.length_finRange]
  have : vmCount parseC = 19 := rfl
  have : vmCount outBC = 5 := rfl
  have : vmCount outHC = 22 := rfl
  have : vmCount prepC = 12 := rfl
  have : vmCount aPhC = 124 := rfl
  have : vmCount a0C = 83 := rfl
  have : vmCount ainC = 200 := rfl
  have : vmCount outDC = 3 := rfl
  have : vmCount (autT 0) = 241 := rfl
  have e1 : vmCount (Code.cp rSk rAHk) = 1 := rfl
  have e2 : vmCount (Code.drop rSk xCNK) = 1 := rfl
  have e3 : vmCount (Code.cp rSp rAHp) = 1 := rfl
  have e4 : vmCount (Code.drop rSp xCNK) = 1 := rfl
  have e5 : vmCount (Code.cp rVk rVHk) = 1 := rfl
  have e6 : vmCount (Code.drop rVk xCNK) = 1 := rfl
  have e7 : vmCount (Code.cp rVp rVHp) = 1 := rfl
  have e8 : vmCount (Code.drop rVp xCNK) = 1 := rfl
  simp only [*]
  ring

theorem pvmDepth_pubC (D : Dims) : pvmDepth (pubC D) ≤ 5 := by
  refine pvmDepth_ofList_le 5 _ fun c hc => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · refine pvmDepth_ofList_le 5 _ fun c hc => ?_
    simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨t, _, rfl⟩
    all_goals first | decide | (rw [pvmDepth_autT]; decide)
  · decide

theorem pκD_lt (D : Dims) (t : ℕ) : κD D t < 2 * D.N := by
  unfold κD; exact Nat.mod_lt _ (by have := D.N_pos; omega)

/-- **The template lengths within the classes.** -/
theorem tm_le_pBf (D : Dims) {Mo Bc Mb : ℕ} (hκ : 2 * D.N ≤ Mo) (h1 : 1 ≤ Mo) (hKo : D.K ≤ Mo)
    (hCtr : pnE (Jh D) ≤ Bc ∧ pnE Pos ≤ Bc ∧ pnE (Col D.K) ≤ Bc ∧ pnE (Wb D) ≤ Bc)
    (hBig : ∀ n, tmBase D n ≤ Mb) (r : Fin 200) : tm D r ≤ pBf Mo Bc Mb r := by
  unfold tm pBf prk
  by_cases ha : 72 ≤ r.val ∧ r.val < 80
  · rw [if_pos ha, if_pos (show 72 ≤ r.val ∧ r.val < 112 by omega)]
    simp only [if_true]; omega
  rw [if_neg ha]
  by_cases hb : 80 ≤ r.val ∧ r.val < 112
  · rw [if_pos hb, if_pos (show 72 ≤ r.val ∧ r.val < 112 by omega)]
    simp only [if_true]
    have := pκD_lt D (r.val - 80); omega
  rw [if_neg hb, if_neg (show ¬(72 ≤ r.val ∧ r.val < 112) by omega)]
  by_cases hc : r = xC1 ∨ r = cK ∨ r = rI ∨ r = rRem
  · rw [if_pos hc]; simp only [if_true]
    rcases hc with rfl | rfl | rfl | rfl
    · show 1 ≤ Mo; exact h1
    · exact hKo
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  rw [if_neg hc]
  by_cases hd : r ∈ pctrRegs
  · rw [if_pos hd]
    simp only [show (1 : ℕ) ≠ 0 by decide, if_false, if_true]
    simp only [pctrRegs, List.mem_cons, List.not_mem_nil, or_false] at hd
    obtain ⟨c1, c2, c3, c4⟩ := hCtr
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.zero_le _
      | exact c1 | exact c2 | exact c3 | exact c4
  · rw [if_neg hd]
    simp only [show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, if_false]
    exact hBig _

/-- **The length and clock bounds of the public-key component.** -/
theorem bounds_pubP (D : Dims) {Mo Bc Mb La Lb : ℕ} (hNK : D.N * D.K ≤ Mo) (hK : D.K ≤ Mo)
    (hN : D.N ≤ Mo) (h1 : Mo ≤ Bc) (h2 : Bc ≤ Mb) (hBc : 1 ≤ Bc) (hLa : La ≤ Mb) (hLb : Lb ≤ Mb)
    (htm : ∀ r, tm D r ≤ pBf Mo Bc Mb r) (hr1 : D.N * D.K ≤ Mb) :
    XProg.lenBoundT (pubP D) (io2 (R := 245) La Lb 0) ≤ io2 (R := 245) (tm D rOut ⊔ Mb) 0 0 ∧
      XProg.timeBoundT (pubP D) (io2 (R := 245) La Lb 0) ≤
        210 * ((2 * Mb + 1) * (4 * Mb + 12)) +
          (478 + 241 * D.b) * (Bc ^ 5 * (2 * Mb + 4 + pIB Mb Mo) * 6) + 300 * (2 * Mb + 3) := by
  obtain ⟨hC, hT, hR⟩ := pokB_spec hNK h1 h2 (pubC D) (pokB_pubC D)
  have hBf : ∀ r, pBf Mo Bc Mb r ≤ Mb := pBf_le h1 h2
  have hra : pBf Mo Bc Mb ra = Mb := rfl
  have hrb : pBf Mo Bc Mb rb = Mb := rfl
  have hr1' : pBf Mo Bc Mb r1 = Mb := rfl
  have hro : pBf Mo Bc Mb rOut = Mb := rfl
  obtain ⟨hl, ht⟩ := RedIO.bounds_ringIO1 hNK hK hN (ra := ra) (rb := rb) (by decide) rOut r1
    (by decide) (by decide)
    (tm D) (pubC D) (pBf Mo Bc Mb) hC La Lb Mb (by rw [hra]; exact hLa) (by rw [hrb]; exact hLb)
    (fun r _ _ _ => htm r) (by rw [hr1']; show D.N * D.K - 1 + 1 ≤ Mb; omega)
    (h1.trans h2) hBf
  rw [hro] at hl
  refine ⟨hl.trans (fun i => ?_), ht.trans ?_⟩
  · simp only [io2]; split_ifs <;> simp
  have hsup : supB (encB Mo D.N D.K (pBf Mo Bc Mb)) ≤ Mb :=
    XProg.supB_le_of (RedIO.encB_le Mo D.N D.K _ Mb (h1.trans h2) hK hN hNK hBf)
  have hv := pvmTime_le Mo D.N D.K (pBf Mo Bc Mb) (2 * Mb + 4) (pIB Mb Mo) Bc (by omega) (by omega)
    hBc (pubC D) (pleafLe_of hNK hK hN (h1.trans h2) hBf (pubC D) hT) hR
  rw [vmCount_pubC] at hv
  have hd := pvmDepth_pubC D
  have hX : Bc ^ pvmDepth (pubC D) * (2 * Mb + 4 + pIB Mb Mo) * (pvmDepth (pubC D) + 1) ≤
      Bc ^ 5 * (2 * Mb + 4 + pIB Mb Mo) * 6 :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hBc hd)) (by omega)
  have := hv.trans (Nat.mul_le_mul_left _ hX)
  omega

end AdvancedEncryption.ExpLUT.Prog.RedPubP
