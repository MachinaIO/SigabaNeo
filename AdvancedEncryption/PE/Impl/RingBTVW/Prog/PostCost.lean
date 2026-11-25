import PE.Impl.RingBTVW.Prog.CfX
import PE.Impl.RingBTVW.Prog.CostTools
import PE.Impl.RingBTVW.Prog.Blocks

/-!
# Uniform bounds of the read-back blocks

`ub_postCoreB`, `ub_postCoreC`: from tapes below `M` (with the templates below `M`), the
read-back blocks of `bfX` and `cfX` take at most `postBT …`, `postCT …` steps, and leave every tape
below `M + 2 (L + LT) + 4` (resp. `M + 2 (A + …) + (M + 1) M + …`). Their word programs `gadP` and
`addRWP` are bounded by `tbC · (M + 1)^tbD` (`tbC_gadP`, `tbD_gadP`, …, by the kernel).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

theorem tbD_gadP : Prog.tbD Prog.gadP = 4 := by decide +kernel
theorem tbC_gadP : Prog.tbC Prog.gadP = 375 := by decide +kernel
theorem tbD_addRWP : Prog.tbD Prog.addRWP = 3 := by decide +kernel
theorem tbC_addRWP : Prog.tbC Prog.addRWP = 210 := by decide +kernel

theorem ub_gadMap {k : ℕ} (u : Fin 21 → Fin k) (M : ℕ) :
    UB (prog (Prog.map u Prog.gadP)) M (375 * (M + 1) ^ 4) M :=
  (ub_progMap u _ Prog.noGrow_gadP M).mono ((Prog.timeBound_le _ Prog.noGrow_gadP M).trans
    (by rw [tbD_gadP, tbC_gadP])) le_rfl

theorem ub_addMap {k : ℕ} (u : Fin 28 → Fin k) (M : ℕ) :
    UB (prog (Prog.map u Prog.addRWP)) M (210 * (M + 1) ^ 3) M :=
  (ub_progMap u _ Prog.noGrow_addRWP M).mono ((Prog.timeBound_le _ Prog.noGrow_addRWP M).trans
    (by rw [tbD_addRWP, tbC_addRWP])) le_rfl

theorem ub_tailsX {k : ℕ} (i : Fin k) (n M : ℕ) :
    UB (prog (Prog.tailsP i n)) M ((n + 1) * (2 * (M + 1) + 3)) M := fun ℓ hℓ =>
  Prog.ubp_tailsP i n M ℓ hℓ

/-- A plain program from a uniform bound of the program. -/
theorem ub_of_ubp {k : ℕ} {p : Prog k} {M T M' : ℕ} (h : Prog.UBP p M T M') : UB (prog p) M T M' :=
  fun ℓ hℓ => by rw [timeBoundT_prog]; exact h ℓ hℓ

/-- A uniform bound of a plain program from that of the program as an `XProg`. -/
theorem ubp_of_ub {k : ℕ} {p : Prog k} {M T M' : ℕ} (h : UB (prog p) M T M') : Prog.UBP p M T M' :=
  fun ℓ hℓ => by have := h ℓ hℓ; rw [timeBoundT_prog] at this; exact this

/-- The time of the gadget branch of `postCoreB` from tapes below `M`. -/
def gadBT (M : ℕ) : ℕ := 375 * (M + 1) ^ 4 + 210 * (M + 1) ^ 3 + (2 * (M + 1) + 3)

theorem ubp_gadAddP (M : ℕ) : Prog.UBP gadAddP M (gadBT M) M :=
  ((ubp_of_ub (ub_gadMap uG M)).seq ((ubp_of_ub (ub_addMap uA M)).seq
    (ubp_of_ub (ub_copyS 1 28 M)))).mono (by simp only [gadBT]; omega) le_rfl

/-- The time of `postCoreB` from tapes below `M`. -/
def postBT (L LT oW Zr N K k M : ℕ) : ℕ :=
  let Ma := M + 1 + L
  let Mb := Ma + 1 + LT
  let Mb' := Mb + 1 + 1
  let Mc := Mb' + 1 + L
  let Md := Mc + 1 + LT
  getT 0 L M + getT oW LT Ma + getT (oW + LT) 1 Mb + (2 * (Mb' + 1) + 3) + prefT L Mb' +
    prefT LT Mc + (Zr + 1) * (2 * (Md + 1) + 3) + tmplT (postTmpl N K k) Md +
    (max (gadBT Md) (2 * (Md + 1) + 3) + 1) + (53 * (2 * (Md + 1) + 3) + (2 * (Md + 1) + 3))

theorem ub_postCoreB (L LT oW Zr N K k M : ℕ) (hM : ∀ x ∈ postTmpl N K k, x.2 ≤ M) :
    UB (postCoreB L LT oW Zr N K k) M (postBT L LT oW Zr N K k M)
      (M + 1 + L + 1 + LT + 1 + 1 + 1 + L + 1 + LT) := by
  rw [postCoreB]
  refine ((ub_getAt 0 L 0 2 4 5 6 M).seq <| (ub_getAt oW LT 0 3 4 5 6 _).seq <|
    (ub_getAt (oW + LT) 1 0 54 4 5 6 _).seq <|
    (ub_clear 0 _).seq <| (ub_prefP L 2 0 4 5 _).seq <| (ub_prefP LT 3 0 4 5 _).seq <|
    (ub_tailsX 1 Zr _).seq <|
    (ub_tmplP 53 (postTmpl N K k) (M + 1 + L + 1 + LT + 1 + 1 + 1 + L + 1 + LT)
      (fun x hx => (hM x hx).trans (by omega)) (by simp [postTmpl])).seq <|
    (ub_of_ubp (Prog.ubp_ifBit (ubp_gadAddP _) (Prog.ubp_prim0 (.clear 54) rfl _))).seq
      (ub_clearL _ _)).mono (le_of_eq ?_) (by simp)
  simp only [postBT, List.length_cons, List.length_nil, max_self]
  ring

/-- The time of the reading loop from tapes below `M` (`ub_skipLoopP`). -/
def skipT (M : ℕ) : ℕ :=
  (2 * (M + 1) + 3) + (M * (2 * (M + M * M) + 3 + 2 * ((M + M * M + 1) * (6 * (M + M * M +
    (M + M * M)) + 20)) + 1) + 2)

theorem ub_zerosX {k : ℕ} (r c t : Fin k) (M : ℕ) :
    UB (zerosP r c t) M (forT (fun X => 2 * (X + 1) + 3) 1 M) (M + M * 1) :=
  ub_forN (fun X => ub_prim (.snoc r false) X) M

/-- The bound after `postCoreC` from tapes below `M`. -/
def postCG (L A NK LW N K k nJ R M : ℕ) : ℕ :=
  let M4 := M + 1 + L + 1 + A + 1 + NK + 1 + 1 + 1 + LW
  let M5 := M4 + M4 * M4
  let M9 := M5 + 1 + L + 1 + A + 1 + nJ * R + 1 + NK
  M9 + M9 * 1 + 1 + k * (N * K)

/-- The time of the gadget branch of `postCoreC` from tapes below `M9`. -/
def gadCT (N K k M9 : ℕ) : ℕ :=
  let M10 := M9 + M9 * 1
  let M11 := M10 + 1 + k * (N * K)
  375 * (M9 + 1) ^ 4 + forT (fun X => 2 * (X + 1) + 3) 1 M9 + prefT (k * (N * K)) M10 +
    210 * (M11 + 1) ^ 3 + (2 * (M11 + 1) + 3)

theorem ub_gadAddC (N K k M : ℕ) :
    UB (gadAddC N K k) M (gadCT N K k M) (M + M * 1 + 1 + k * (N * K)) := by
  rw [gadAddC]
  exact ((ub_gadMap uGc _).seq <| (ub_zerosX 60 63 61 _).seq <|
    (ub_prefP (k * (N * K)) 7 60 4 5 _).seq <| (ub_addMap uAc _).seq (ub_copyS 1 28 _)).mono
    (le_of_eq (by simp only [gadCT]; ring)) le_rfl

/-- The time of `postCoreC` from tapes below `M`. -/
def postCT (L A NK oW LW Zr N K k Z R nJ M : ℕ) : ℕ :=
  let M1 := M + 1 + L
  let M2 := M1 + 1 + A
  let M3 := M2 + 1 + NK
  let M3' := M3 + 1 + 1
  let M4 := M3' + 1 + LW
  let M5 := M4 + M4 * M4
  let M6 := M5 + 1 + L
  let M7 := M6 + 1 + A
  let M8 := M7 + 1 + nJ * R
  let M9 := M8 + 1 + NK
  let M11 := M9 + M9 * 1 + 1 + k * (N * K)
  getT 0 L M + getT oW A M1 + getT (oW + A) NK M2 + getT (oW + A + NK) 1 M3 + getT oW LW M3' +
    tmplT (postTmplC N K k Z R nJ) M4 + skipT M4 + (2 * (M5 + 1) + 3) + prefT L M5 + prefT A M6 +
    prefT (nJ * R) M7 + prefT NK M8 + (Zr + 1) * (2 * (M9 + 1) + 3) +
    (max (gadCT N K k M9) (2 * (M9 + 1) + 3) + 1) +
    (63 * (2 * (M11 + 1) + 3) + (2 * (M11 + 1) + 3))

theorem ub_postCoreC (L A NK oW LW Zr N K k Z R nJ M : ℕ)
    (hM : ∀ x ∈ postTmplC N K k Z R nJ, x.2 ≤ M) :
    UB (postCoreC L A NK oW LW Zr N K k Z R nJ) M (postCT L A NK oW LW Zr N K k Z R nJ M)
      (postCG L A NK LW N K k nJ R M) := by
  rw [postCoreC]
  refine ((ub_getAt 0 L 0 2 4 5 6 M).seq <| (ub_getAt oW A 0 3 4 5 6 _).seq <|
    (ub_getAt (oW + A) NK 0 54 4 5 6 _).seq <| (ub_getAt (oW + A + NK) 1 0 64 4 5 6 _).seq <|
    (ub_getAt oW LW 0 55 4 5 6 _).seq <|
    (ub_tmplP 53 (postTmplC N K k Z R nJ) _ (fun x hx => (hM x hx).trans (by omega))
      (by simp [postTmplC])).seq <|
    (ub_skipLoopP (by decide) _).seq <| (ub_clear 0 _).seq <| (ub_prefP L 2 0 4 5 _).seq <|
    (ub_prefP A 3 0 4 5 _).seq <| (ub_prefP (nJ * R) 56 0 4 5 _).seq <|
    (ub_prefP NK 54 0 4 5 _).seq <| (ub_tailsX 1 Zr _).seq <|
    ((ub_ifBit (ub_gadAddC N K k _) ((ub_clear 64 _).mono le_rfl
      (show _ ≤ _ + _ * 1 + 1 + k * (N * K) by omega))).mono le_rfl
      (le_of_eq (max_self _))).seq
      (ub_clearL _ _)).mono (le_of_eq ?_) (le_of_eq ?_)
  · simp only [postCT, skipT, List.length_cons, List.length_nil]
    ring
  · simp only [postCG]

end AdvancedEncryption.RingBTVW.Prog
