import PE.Impl.DualUse.Prog.DecTightLib
import PE.Impl.DualUse.Prog.DecGenCost
import PE.Impl.DualUse.Prog.CfX

/-!
# The crafted data of `Dec`, per tape

`ph_preCoreC` bounds every step of `preCoreC` by one bound `X` on offsets, lengths, templates and
tapes (`preTCX X`, degree `4` in `X` through the row loops). Here the same per-step bounds are
summed with three sizes: `X` the longest tape (the sweeps), `Y` the offsets and lengths read, `T`
the templates; the row loops are charged their counters (`10`, `nJ`) and moved sizes
(**`ph_preCoreC'`**).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

theorem mvT_le_T {k : ℕ} {β : Fin k → ℕ} {X T : ℕ} (h : ∀ i, β i ≤ X) (t : Fin k) (ht : β t ≤ T) :
    mvT β t ≤ (T + 1) * (6 * (X + T) + 20) := by
  unfold mvT
  have := supB_le_of h
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The time of a row loop with the counter below `n`, the moved words below `z`. -/
def wTv (X n z : ℕ) : ℕ :=
  (n + 1) * (3 * ((z + 1) * (6 * ((X + n * z + z) + 2 * z) + 20)) + 4 * (X + n * z + z) + 2 * z + 12)

theorem wT_le_v {k : ℕ} {β : Fin k → ℕ} {X n z : ℕ} (h : ∀ i, β i ≤ X) (tn tz tr : Fin k)
    (hn : β tn ≤ n) (hz : β tz + β tr ≤ z) : wT β tn tz tr ≤ wTv X n z := by
  have h1 := supB_le_of h
  have hm := Nat.mul_le_mul hn hz
  have hS : wS β tn tz tr ≤ X + n * z + z := by unfold wS; omega
  have hQ : wQ β tn tz tr ≤ (z + 1) * (6 * ((X + n * z + z) + 2 * z) + 20) := by
    unfold wQ; exact Nat.mul_le_mul (by omega) (by omega)
  unfold wT wTv
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The time of `preCoreC` per tape. -/
def preTCv (X Y T z1 n2 z2 : ℕ) : ℕ :=
  6 * getT Y Y X + 10 * ((2 * T + 1) * (4 * X + 12)) + 6 * ((T + 1) * (6 * (X + T) + 20)) +
    wTv X nA z1 + wTv X n2 z2 + (2 * (X + 1) + 3) + (20 * (2 * (X + 1) + 3) + (2 * (X + 1) + 3))

set_option maxHeartbeats 8000000 in
/-- **The per-tape bound of `preCoreC`.** -/
theorem ph_preCoreC' (L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD a : ℕ) (X Y T : ℕ)
    (hX : 2 * (a + 6 + L + A + NK + 2 * LΨ + C0 + nA * (Z2 + R2) + PAD + Z + R + Z2 + R2 + LΨ + nA +
      C0 + PAD + nJ + nA) + Lcj + nJ * (Z + R) + LΨ + nA ≤ X)
    (hoK : oK ≤ Y) (hoP : oP ≤ Y) (hoJ : oJ ≤ Y) (hL : L ≤ Y) (hA : A ≤ Y) (hNK : NK ≤ Y)
    (hLΨ : LΨ ≤ Y) (hLcj : Lcj ≤ Y) (hTX : T ≤ X) (tZ : Z ≤ T) (tR : R ≤ T) (tnJ : nJ ≤ T)
    (tC0 : C0 ≤ T) (tZ2 : Z2 ≤ T) (tR2 : R2 ≤ T) (tPAD : PAD ≤ T) (tLΨ : LΨ ≤ T) (t10 : nA ≤ T) :
    Ph (preCoreC L A oK NK oP LΨ oJ Lcj Z R nJ C0 Z2 R2 PAD) ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (preTCv X Y T (Z2 + R2) nJ (Z + R)) ![a + 1 + L + C0 + nA * (Z2 + R2) + nJ * (Z + R) + LΨ + nA, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  simp only [show nA = 128 from rfl] at *
  set M1 := a + 1 + L with hM1
  set M2 := M1 + 1 + A with hM2
  set M3 := M2 + 1 + NK with hM3
  set M4 := M3 + 1 + LΨ with hM4
  set M5 := M4 + 1 + LΨ with hM5
  set Tm := max (max (max Z R) (max nJ C0)) (max (max Z2 R2) (max (max 128 PAD) LΨ)) with hTm
  have p1 := (ph_getAt 0 L (src := 0) (dst := 1) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide)
    ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).mono le_rfl le_rfl (show _ ≤ ![a, M1, 0, 0, M1, M1, M1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by
      have : supB ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ a := supB_le_of (fun i => by fin_cases i <;> simp)
      fin_cases i <;> simp <;> omega)
  have s1 : supB ![a, M1, 0, 0, M1, M1, M1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ M1 := supB_le_of (fun i => by fin_cases i <;> simp <;> omega)
  have p2 := (ph_getAt L A (src := 0) (dst := 3) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide)
    ![a, M1, 0, 0, M1, M1, M1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).mono le_rfl le_rfl (show _ ≤ ![a, M1, 0, M2, M2, M2, M2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by fin_cases i <;> simp <;> omega)
  have s2 : supB ![a, M1, 0, M2, M2, M2, M2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ M2 := supB_le_of (fun i => by fin_cases i <;> simp <;> omega)
  have p3 := (ph_getAt oK NK (src := 0) (dst := 3) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide)
    ![a, M1, 0, M2, M2, M2, M2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).mono le_rfl le_rfl (show _ ≤ ![a, M1, 0, M3, M3, M3, M3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by fin_cases i <;> simp <;> omega)
  have s3 : supB ![a, M1, 0, M3, M3, M3, M3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ M3 := supB_le_of (fun i => by fin_cases i <;> simp <;> omega)
  have p4 := (ph_getAt oP LΨ (src := 0) (dst := 2) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide)
    ![a, M1, 0, M3, M3, M3, M3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).mono le_rfl le_rfl (show _ ≤ ![a, M1, M4, M3, M4, M4, M4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by fin_cases i <;> simp <;> omega)
  have s4 : supB ![a, M1, M4, M3, M4, M4, M4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ≤ M4 := supB_le_of (fun i => by fin_cases i <;> simp <;> omega)
  have p5 := (ph_getAt oP LΨ (src := 0) (dst := 18) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide)
    ![a, M1, M4, M3, M4, M4, M4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).mono le_rfl le_rfl (show _ ≤ ![a, M1, M4, M3, M5, M5, M5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, M5, 0, 0] from fun i => by fin_cases i <;> simp <;> omega)
  have s5 : supB ![a, M1, M4, M3, M5, M5, M5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, M5, 0, 0] ≤ M5 := supB_le_of (fun i => by fin_cases i <;> simp <;> omega)
  have p6 := (ph_tmplP (17 : Fin 21) (preTmplC Z R nJ C0 Z2 R2 PAD LΨ) ![a, M1, M4, M3, M5, M5, M5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, M5, 0, 0] (by simp [preTmplC])).mono
    le_rfl le_rfl (show _ ≤ ![a, M1, M4, M3, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, 0, Tm, M5, 0, LΨ] from fun i => by
      fin_cases i <;> simp [preTmplC, tmplB, natB, hTm, nA] <;> omega)
  have p7 := (ph_zerosP (r := (1 : Fin 21)) (c := 16) (t := 10) (by decide) (by decide) ![a, M1, M4, M3, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, 0, Tm, M5, 0, LΨ]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0, M4, M3, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, C0, Tm, M5, 0, LΨ] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p8 := (ph_zerosP (r := (3 : Fin 21)) (c := 16) (t := 14) (by decide) (by decide) ![a, M1 + C0, M4, M3, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, C0, Tm, M5, 0, LΨ]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0, M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, PAD, Tm, M5, 0, LΨ] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p9 := (ph_zerosP (r := (19 : Fin 21)) (c := 16) (t := 11) (by decide) (by decide) ![a, M1 + C0, M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, PAD, Tm, M5, 0, LΨ]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0, M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, Z2, Tm, M5, Z2, LΨ] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p10 := (ph_wLoopP (out := (1 : Fin 21)) (f := 2) (x := 19) (c := 15) (c' := 16) (tn := 13)
    (tz := 11) (tr := 12) (by decide) ![a, M1 + C0, M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, Z2, Tm, M5, Z2, LΨ]).mono le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + 128 * (Z2 + R2), M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 128, max Z2 R2, Tm, M5, Z2, LΨ] from fun i => by
      fin_cases i <;> simp [wB] <;> omega)
  have s10 : supB ![a, M1 + C0 + 128 * (Z2 + R2), M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 128, max Z2 R2, Tm, M5, Z2, LΨ] ≤ M5 + C0 + 128 * (Z2 + R2) + PAD + Z + R + Z2 + R2 + LΨ + 128 + nJ + 128 :=
    supB_le_of (fun i => by fin_cases i <;> simp <;> omega)
  set XG := supB ![a, M1 + C0 + 128 * (Z2 + R2), M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 128, max Z2 R2, Tm, M5, Z2, LΨ] + 1 + Lcj with hXG
  have hXGX : XG ≤ X := by omega
  have p11 := (ph_getAt oJ Lcj (src := 0) (dst := 2) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide)
    ![a, M1 + C0 + 128 * (Z2 + R2), M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 128, max Z2 R2, Tm, M5, Z2, LΨ]).mono le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + 128 * (Z2 + R2), XG, M3 + PAD, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, 128, max Z2 R2, Tm, M5, Z2, LΨ] from fun i => by fin_cases i <;> simp <;> omega)
  have p12 := (ph_wLoopP (out := (1 : Fin 21)) (f := 2) (x := 3) (c := 15) (c' := 16) (tn := 9)
    (tz := 7) (tr := 8) (by decide) ![a, M1 + C0 + 128 * (Z2 + R2), XG, M3 + PAD, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, 128, max Z2 R2, Tm, M5, Z2, LΨ]).mono le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R), XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, max (max Z2 R2) (max Z R), Tm, M5, Z2, LΨ] from fun i => by
      fin_cases i <;> simp [wB] <;> omega)
  have p13 := (ph_moveP (r := (1 : Fin 21)) (S := 18) (c := 16) (t := 20) (by decide) (by decide)
    (by decide) (by decide) ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R), XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, max (max Z2 R2) (max Z R), Tm, M5, Z2, LΨ]).mono le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, LΨ, Tm, M5, Z2, LΨ] from fun i => by
      fin_cases i <;> simp [mvB] <;> omega)
  have p14 := (ph_zerosP (r := (1 : Fin 21)) (c := 16) (t := 13) (by decide) (by decide) ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, LΨ, Tm, M5, Z2, LΨ]).mono
    le_rfl le_rfl (show _ ≤ ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, 128, Tm, M5, Z2, LΨ] from fun i => by fin_cases i <;> simp [mvB] <;> omega)
  have p15 := (ph_prim (Prim.copy (0 : Fin 21) 1) ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, 128, Tm, M5, Z2, LΨ]).mono le_rfl le_rfl
    (show _ ≤ ![M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, 128, Tm, M5, Z2, LΨ] from fun i => by fin_cases i <;> simp [Prim.lenT] <;> omega)
  have p16 := (ph_clearL [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
    ![M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, 128, Tm, M5, Z2, LΨ]).mono le_rfl le_rfl (show _ ≤ ![a + 1 + L + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] from fun i => by fin_cases i <;> simp <;> omega)
  refine (p1.seq (p2.seq (p3.seq (p4.seq (p5.seq (p6.seq (p7.seq (p8.seq (p9.seq (p10.seq (p11.seq
    (p12.seq (p13.seq (p14.seq (p15.seq p16))))))))))))))).mono le_rfl ?_ le_rfl
  have g1 := getT_mono' (o := 0) (L := L) (M := supB ![a, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (o' := Y) (L' := Y) (M' := X) (by omega)
    (by omega) ((supB_le_of (M := a) (fun i => by fin_cases i <;> simp)).trans (by omega))
  have g2 := getT_mono' (o := L) (L := A) (M := supB ![a, M1, 0, 0, M1, M1, M1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (o' := Y) (L' := Y) (M' := X) (by omega)
    (by omega) (s1.trans (by omega))
  have g3 := getT_mono' (o := oK) (L := NK) (M := supB ![a, M1, 0, M2, M2, M2, M2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (o' := Y) (L' := Y) (M' := X) hoK
    (by omega) (s2.trans (by omega))
  have g4 := getT_mono' (o := oP) (L := LΨ) (M := supB ![a, M1, 0, M3, M3, M3, M3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (o' := Y) (L' := Y) (M' := X) hoP
    (by omega) (s3.trans (by omega))
  have g5 := getT_mono' (o := oP) (L := LΨ) (M := supB ![a, M1, M4, M3, M4, M4, M4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (o' := Y) (L' := Y) (M' := X) hoP
    (by omega) (s4.trans (by omega))
  have g11 := getT_mono' (o := oJ) (L := Lcj) (M := supB ![a, M1 + C0 + 128 * (Z2 + R2), M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 128, max Z2 R2, Tm, M5, Z2, LΨ]) (o' := Y) (L' := Y) (M' := X) hoJ
    (by omega) (s10.trans (by omega))
  have t6 := tmplTT_le2 (17 : Fin 21) X T hTX (preTmplC Z R nJ C0 Z2 R2 PAD LΨ) ![a, M1, M4, M3, M5, M5, M5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, M5, 0, 0]
    (fun i => by fin_cases i <;> simp <;> omega) (by simp [preTmplC, nA]; omega)
  have t7 := mvT_le_T (X := X) (T := T) (β := ![a, M1, M4, M3, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, 0, Tm, M5, 0, LΨ]) (fun i => by fin_cases i <;> simp <;> omega) 10 (by simp <;> omega)
  have t8 := mvT_le_T (X := X) (T := T) (β := ![a, M1 + C0, M4, M3, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, C0, Tm, M5, 0, LΨ]) (fun i => by fin_cases i <;> simp <;> omega) 14 (by simp <;> omega)
  have t9 := mvT_le_T (X := X) (T := T) (β := ![a, M1 + C0, M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, PAD, Tm, M5, 0, LΨ]) (fun i => by fin_cases i <;> simp <;> omega) 11 (by simp <;> omega)
  have t10 := wT_le_v (X := X) (n := 128) (z := Z2 + R2) (β := ![a, M1 + C0, M4, M3 + PAD, M5, M5, M5, Z, R, nJ, C0, Z2, R2, 128, PAD, 0, Z2, Tm, M5, Z2, LΨ]) (fun i => by fin_cases i <;> simp <;> omega) 13 11 12 (by simp) (by simp)
  have t12 := wT_le_v (X := X) (n := nJ) (z := Z + R) (β := ![a, M1 + C0 + 128 * (Z2 + R2), XG, M3 + PAD, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, 128, max Z2 R2, Tm, M5, Z2, LΨ]) (fun i => by fin_cases i <;> simp <;> omega) 9 7 8 (by simp) (by simp)
  have t13 := mvT_le_T (X := X) (T := T) (β := ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R), XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, max (max Z2 R2) (max Z R), Tm, M5, Z2, LΨ]) (fun i => by fin_cases i <;> simp <;> omega) 20 (by simp <;> omega)
  have t14 := mvT_le_T (X := X) (T := T) (β := ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, LΨ, Tm, M5, Z2, LΨ]) (fun i => by fin_cases i <;> simp <;> omega) 13 (by simp <;> omega)
  have t15 := supB_le_of (show ∀ i, ![a, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, 128, Tm, M5, Z2, LΨ] i ≤ X from fun i => by fin_cases i <;> simp <;> omega)
  have t16 := supB_le_of (show ∀ i, ![M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, M1 + C0 + 128 * (Z2 + R2) + nJ * (Z + R) + LΨ + 128, XG, max (M3 + PAD) Z, XG, XG, XG, Z, R, nJ, C0, Z2, R2, 128, PAD, nJ, 128, Tm, M5, Z2, LΨ] i ≤ X from fun i => by fin_cases i <;> simp <;> omega)
  simp only [preTCv, preTmplC, List.length_cons, List.length_nil, show nA = 128 from rfl] at t6 ⊢
  omega


end AdvancedEncryption.DualUse.Prog
