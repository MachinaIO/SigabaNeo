import PE.Impl.DualUse.Prog.BfXCost

/-!
# The crafted data of `KeyGen` with the row loop charged its own counter

`ph_preCoreB` (`PE.Impl.DualUse.Prog.BfXCost`) bounds the row loop `wLoopP` of `preCoreB` by
`wTX X`, every count at the uniform bound `X` (about `X⁴` steps). Here (`ph_preCoreB_v`) the loop
is charged its `nT` rounds of moves of `Z + R` bits (`wTV`), about `nT (Z + R) X` steps.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-- The time of `wLoopP` with `n` rounds of moves of `ZR` bits, tapes below `X`. -/
def wTV (X n ZR : ℕ) : ℕ :=
  (n + 1) * (3 * ((ZR + 1) * (6 * (2 * X + 2 * ZR) + 20)) + 4 * (2 * X) + 2 * ZR + 12)

theorem wT_le_V {k : ℕ} {β : Fin k → ℕ} {X : ℕ} (h : ∀ i, β i ≤ X) (tn tz tr : Fin k)
    (hs : β tn * (β tz + β tr) + β tz + β tr ≤ X) :
    wT β tn tz tr ≤ wTV X (β tn) (β tz + β tr) := by
  have h1 := supB_le_of h
  have hS : wS β tn tz tr ≤ 2 * X := by unfold wS; omega
  unfold wT wTV wQ
  gcongr

/-- The time bound of `preCoreB` with the row loop charged its own counter. -/
def preTV (X nT ZR : ℕ) : ℕ :=
  3 * getT X X X + 9 * ((2 * X + 1) * (4 * X + 12)) + 5 * ((X + 1) * (6 * (X + X) + 20)) +
    wTV X nT ZR + (2 * (X + 1) + 3) + (17 * (2 * (X + 1) + 3) + (2 * (X + 1) + 3))

set_option maxHeartbeats 4000000 in
/-- **The per-tape bound of `preCoreB`**, the row loop charged its own counter (`preTV`). -/
theorem ph_preCoreB_v (L LT oB nTR Z R nT C0 RM0 PS0 PAD a : ℕ) (X : ℕ)
    (hX : a + 3 + L + LT + nTR + C0 + RM0 + nT * (Z + R) + PS0 + nA + Z + R + PAD + nA ≤ X)
    (hoB : oB ≤ X) (hRM : RM0 ≤ X) (hPS : PS0 ≤ X) (hnT : nT ≤ X) :
    Ph (preCoreB L LT oB nTR Z R nT C0 RM0 PS0 PAD) ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (preTV X nT (Z + R))
      (![a + 1 + L + C0 + RM0 + nT * (Z + R) + PS0 + nA, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  have hnA : nA = 128 := rfl
  set M1 := a + 1 + L with hM1
  set M2 := M1 + 1 + LT with hM2
  set M3 := M2 + 1 + nTR with hM3
  set Tm := max (max (max Z R) (max nT C0)) (max (max RM0 PS0) (max nA PAD)) with hTm
  have hTmX : Tm ≤ X := by simp only [hTm]; omega
  have s0 : supB ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ a := supB_vec_le (fun i => by fin_cases i <;> simp)
  have p1 := ph_getAt 0 L (src := 0) (dst := 1) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide) ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  have p1' : Ph (getAt 0 L 0 1 4 5 6) ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (getT 0 L (supB ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) ![a, M1, 0, 0, M1, M1, M1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := p1.mono le_rfl le_rfl
    (fun i => by fin_cases i <;> simp <;> omega)
  have s1 : supB ![a, M1, 0, 0, M1, M1, M1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ M1 := supB_vec_le (fun i => by fin_cases i <;> simp <;> omega)
  have p2 := (ph_getAt L LT (src := 0) (dst := 3) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide) ![a, M1, 0, 0, M1, M1, M1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).mono le_rfl le_rfl
    (show _ ≤ ![a, M1, 0, M2, M2, M2, M2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by fin_cases i <;> simp <;> omega)
  have s2 : supB ![a, M1, 0, M2, M2, M2, M2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ M2 := supB_vec_le (fun i => by fin_cases i <;> simp <;> omega)
  have p3 := (ph_getAt oB nTR (src := 0) (dst := 2) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide) ![a, M1, 0, M2, M2, M2, M2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).mono le_rfl le_rfl
    (show _ ≤ ![a, M1, M3, M2, M3, M3, M3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by fin_cases i <;> simp <;> omega)
  have s3 : supB ![a, M1, M3, M2, M3, M3, M3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ M3 := supB_vec_le (fun i => by fin_cases i <;> simp <;> omega)
  have p4 := (ph_tmplP (17 : Fin 18) (preTmpl Z R nT C0 RM0 PS0 PAD) ![a, M1, M3, M2, M3, M3, M3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by simp [preTmpl])).mono
    le_rfl le_rfl (show _ ≤ ![a, M1, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, 0, Tm] from fun i => by
      fin_cases i <;> simp [preTmpl, tmplB, natB, hTm] <;> omega)
  have p5 := (ph_zerosP (r := (1 : Fin 18)) (c := 16) (t := 10) (by decide) (by decide) ![a, M1, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, 0, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, C0, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p6 := (ph_zerosP (r := (1 : Fin 18)) (c := 16) (t := 11) (by decide) (by decide) ![a, M1 + C0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, C0, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, RM0, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p7 := (ph_zerosP (r := (3 : Fin 18)) (c := 16) (t := 14) (by decide) (by decide) ![a, M1 + C0 + RM0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, RM0, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0, M3, M2 + PAD, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, PAD, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p8 := (ph_wLoopP (out := (1 : Fin 18)) (f := 2) (x := 3) (c := 15) (c' := 16) (tn := 9) (tz := 7)
    (tr := 8) (by decide) ![a, M1 + C0 + RM0, M3, M2 + PAD, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, PAD, Tm]).mono le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0 + nT * (Z + R), M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, max PAD (max Z R), Tm] from fun i => by
      fin_cases i <;> simp [wB] <;> omega)
  have p9 := (ph_zerosP (r := (1 : Fin 18)) (c := 16) (t := 12) (by decide) (by decide) ![a, M1 + C0 + RM0 + nT * (Z + R), M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, max PAD (max Z R), Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, PS0, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p10 := (ph_zerosP (r := (1 : Fin 18)) (c := 16) (t := 13) (by decide) (by decide) ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, PS0, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, nA, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p11 := (ph_prim (Prim.copy (0 : Fin 18) 1) ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, nA, Tm]).mono le_rfl le_rfl
    (show _ ≤ ![M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, nA, Tm] from fun i => by fin_cases i <;> simp [Prim.lenT] <;> omega)
  have p12 := (ph_clearL [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] ![M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, nA, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by fin_cases i <;> simp)
  refine (p1'.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq (p8.seq (p9.seq (p10.seq
    (p11.seq p12))))))))))).mono le_rfl ?_ le_rfl
  have hle : ∀ (v : Fin 18 → ℕ), (∀ i, v i ≤ X) → supB v ≤ X := fun v h => supB_le_of h
  have t1 := getT_mono (o := 0) (L := L) (M := supB _) (o' := X) (L' := X) (M' := X) (by omega) (by omega)
    (s0.trans (by omega))
  have t2 := getT_mono (o := L) (L := LT) (M := supB _) (o' := X) (L' := X) (M' := X) (by omega) (by omega)
    (s1.trans (by omega))
  have t3 := getT_mono (o := oB) (L := nTR) (M := supB _) (o' := X) (L' := X) (M' := X) hoB (by omega)
    (s2.trans (by omega))
  have t4 := tmplTT_le (17 : Fin 18) X (preTmpl Z R nT C0 RM0 PS0 PAD) ![a, M1, M3, M2, M3, M3, M3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    (fun i => by fin_cases i <;> simp <;> omega) (by simp [preTmpl]; omega)
  have t5 := mvT_le_const (X := X) (β := ![a, M1, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, 0, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 10
  have t6 := mvT_le_const (X := X) (β := ![a, M1 + C0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, C0, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 11
  have t7 := mvT_le_const (X := X) (β := ![a, M1 + C0 + RM0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, RM0, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 14
  have t8 : wT (![a, M1 + C0 + RM0, M3, M2 + PAD, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, PAD, Tm] : Fin 18 → ℕ) 9 7 8 ≤ wTV X nT (Z + R) := wT_le_V (X := X) (β := ![a, M1 + C0 + RM0, M3, M2 + PAD, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, 0, PAD, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 9 7 8 (by simp; omega)
  have t9 := mvT_le_const (X := X) (β := ![a, M1 + C0 + RM0 + nT * (Z + R), M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, max PAD (max Z R), Tm]) (fun i => by fin_cases i <;> simp <;> omega) 12
  have t10 := mvT_le_const (X := X) (β := ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, PS0, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 13
  have t11 := hle ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, nA, Tm] (fun i => by fin_cases i <;> simp <;> omega)
  have t12 := hle ![M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M1 + C0 + RM0 + nT * (Z + R) + PS0 + nA, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, nA, PAD, nT, nA, Tm] (fun i => by fin_cases i <;> simp <;> omega)
  simp only [preTV, preTmpl, List.length_cons, List.length_nil] at t4 ⊢
  omega

end AdvancedEncryption.DualUse.Prog
