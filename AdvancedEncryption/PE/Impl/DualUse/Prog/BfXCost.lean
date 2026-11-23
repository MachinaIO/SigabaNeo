import PE.Impl.DualUse.Prog.BfX
import PE.Impl.DualUse.Prog.CostTools
import PE.Impl.DualUse.Prog.WfB2Time

/-!
# Per-tape bounds of the crafted-data blocks

`ph_preCoreB`: from a word of at most `a` bits on tape `0` (the other tapes blank), `preCoreB`
leaves at most `preL a …` bits on tape `0` and the other tapes blank, in at most `preT …` steps.
The bound of tape `0` is tight (`a + L + LT + nTR + C0 + RM0 + nT (Z + R) + PS0 + 13`): the
`W_f` block is certified only on simulation data of at most `2^240` bits.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

theorem mvT_le_const {k : ℕ} {β : Fin k → ℕ} {X : ℕ} (h : ∀ i, β i ≤ X) (t : Fin k) :
    mvT β t ≤ (X + 1) * (6 * (X + X) + 20) := by
  unfold mvT
  have := supB_le_of h
  have := h t
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The closed time bound of `wLoopP` from bounds below `X`. -/
def wTX (X : ℕ) : ℕ :=
  (X + 1) * (3 * ((X + X + 1) * (6 * ((X + X * (X + X) + X + X) + 2 * (X + X)) + 20)) +
    4 * (X + X * (X + X) + X + X) + 2 * (X + X) + 12)

theorem wT_le_X {k : ℕ} {β : Fin k → ℕ} {X : ℕ} (h : ∀ i, β i ≤ X) (tn tz tr : Fin k) :
    wT β tn tz tr ≤ wTX X := by
  have h1 := supB_le_of h
  have hn := h tn; have hz := h tz; have hr := h tr
  unfold wT wQ wS wTX
  gcongr

theorem getT_mono {o L M o' L' M' : ℕ} (ho : o ≤ o') (hL : L ≤ L') (hM : M ≤ M') :
    getT o L M ≤ getT o' L' M' := by
  unfold getT prefT
  gcongr

/-- The time bound of `preCoreB` from bounds below `X`. -/
def preTX (X : ℕ) : ℕ :=
  3 * getT X X X + 9 * ((2 * X + 1) * (4 * X + 12)) + 5 * ((X + 1) * (6 * (X + X) + 20)) + wTX X +
    (2 * (X + 1) + 3) + (17 * (2 * (X + 1) + 3) + (2 * (X + 1) + 3))

theorem supB_vec_le {n : ℕ} {v : Fin n → ℕ} {X : ℕ} (h : ∀ i, v i ≤ X) : supB v ≤ X := supB_le_of h

set_option maxHeartbeats 4000000 in
/-- **The per-tape bound of `preCoreB`.** -/
theorem ph_preCoreB (L LT oB nTR Z R nT C0 RM0 PS0 PAD a : ℕ) (X : ℕ)
    (hX : a + 3 + L + LT + nTR + C0 + RM0 + nT * (Z + R) + PS0 + 10 + Z + R + PAD + 10 ≤ X)
    (hoB : oB ≤ X) (hRM : RM0 ≤ X) (hPS : PS0 ≤ X) (hnT : nT ≤ X) :
    Ph (preCoreB L LT oB nTR Z R nT C0 RM0 PS0 PAD) ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (preTX X)
      (![a + 1 + L + C0 + RM0 + nT * (Z + R) + PS0 + 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) := by
  set M1 := a + 1 + L with hM1
  set M2 := M1 + 1 + LT with hM2
  set M3 := M2 + 1 + nTR with hM3
  set Tm := max (max (max Z R) (max nT C0)) (max (max RM0 PS0) (max 10 PAD)) with hTm
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
    le_rfl le_rfl (show _ ≤ ![a, M1, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, 0, Tm] from fun i => by
      fin_cases i <;> simp [preTmpl, tmplB, natB, hTm] <;> omega)
  have p5 := (ph_zerosP (r := (1 : Fin 18)) (c := 16) (t := 10) (by decide) (by decide) ![a, M1, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, 0, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, C0, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p6 := (ph_zerosP (r := (1 : Fin 18)) (c := 16) (t := 11) (by decide) (by decide) ![a, M1 + C0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, C0, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, RM0, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p7 := (ph_zerosP (r := (3 : Fin 18)) (c := 16) (t := 14) (by decide) (by decide) ![a, M1 + C0 + RM0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, RM0, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0, M3, M2 + PAD, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, PAD, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p8 := (ph_wLoopP (out := (1 : Fin 18)) (f := 2) (x := 3) (c := 15) (c' := 16) (tn := 9) (tz := 7)
    (tr := 8) (by decide) ![a, M1 + C0 + RM0, M3, M2 + PAD, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, PAD, Tm]).mono le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0 + nT * (Z + R), M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, max PAD (max Z R), Tm] from fun i => by
      fin_cases i <;> simp [wB] <;> omega)
  have p9 := (ph_zerosP (r := (1 : Fin 18)) (c := 16) (t := 12) (by decide) (by decide) ![a, M1 + C0 + RM0 + nT * (Z + R), M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, max PAD (max Z R), Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, PS0, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p10 := (ph_zerosP (r := (1 : Fin 18)) (c := 16) (t := 13) (by decide) (by decide) ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, PS0, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, 10, Tm] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p11 := (ph_prim (Prim.copy (0 : Fin 18) 1) ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, 10, Tm]).mono le_rfl le_rfl
    (show _ ≤ ![M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, 10, Tm] from fun i => by fin_cases i <;> simp [Prim.lenT] <;> omega)
  have p12 := (ph_clearL [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] ![M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, 10, Tm]).mono
    le_rfl le_rfl (show _ ≤ ![M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by fin_cases i <;> simp)
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
  have t5 := mvT_le_const (X := X) (β := ![a, M1, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, 0, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 10
  have t6 := mvT_le_const (X := X) (β := ![a, M1 + C0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, C0, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 11
  have t7 := mvT_le_const (X := X) (β := ![a, M1 + C0 + RM0, M3, M2, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, RM0, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 14
  have t8 := wT_le_X (X := X) (β := ![a, M1 + C0 + RM0, M3, M2 + PAD, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, 0, PAD, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 9 7 8
  have t9 := mvT_le_const (X := X) (β := ![a, M1 + C0 + RM0 + nT * (Z + R), M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, max PAD (max Z R), Tm]) (fun i => by fin_cases i <;> simp <;> omega) 12
  have t10 := mvT_le_const (X := X) (β := ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, PS0, Tm]) (fun i => by fin_cases i <;> simp <;> omega) 13
  have t11 := hle ![a, M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, 10, Tm] (fun i => by fin_cases i <;> simp <;> omega)
  have t12 := hle ![M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M1 + C0 + RM0 + nT * (Z + R) + PS0 + 10, M3, max (M2 + PAD) Z, M3, M3, M3, Z, R, nT, C0, RM0, PS0, 10, PAD, nT, 10, Tm] (fun i => by fin_cases i <;> simp <;> omega)
  simp only [preTX, preTmpl, List.length_cons, List.length_nil] at t4 ⊢
  omega

end AdvancedEncryption.DualUse.Prog
