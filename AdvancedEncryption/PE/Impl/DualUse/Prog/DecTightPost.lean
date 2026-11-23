import PE.Impl.DualUse.Prog.DecTightLib
import PE.Impl.DualUse.Prog.PostCost
import PE.Impl.DualUse.Prog.WfB2Time
import PE.Impl.DualUse.Prog.BfXCost

/-!
# The read-back block of `c_f̂`, per tape

`ub_postCoreC` bounds `postCoreC` from one bound `M` on every tape (the `W_f` block's uniform
`2^250`): its reading loop is charged `M` rounds of `M` bits, its word programs
`tbC · (M + 1)^tbD`. Here, from the per-tape output of the `W_f` block (tape `0` at most `D`,
tape `1` at most `Wv`, the others blank):

* the templates are exact, so the reading loop takes `nJ` rounds of at most `Z` bits;
* `gadP`, `addRWP` are charged their certified sweeps (`SpecT`), each `2 · top + 3`;
* afterwards tape `0` holds at most `L + A + nJ R + NK` bits, tape `1` at most `2k N K`, the
  others are blank (**`ph_postCoreC'`**).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT

/-- Before the templates: tape `0`, tape `1`, the blank `28`, `60`, every other tape below `U`. -/
def pcU (U a0 a1 : ℕ) : Fin 64 → ℕ := fun t =>
  if t.val = 0 then a0 else if t.val = 1 then a1 else if t.val = 28 then 0 else if t.val = 60 then 0 else U

/-- With the templates. -/
def pcV (K N k Z R nJ U a0 a1 a28 a60 : ℕ) : Fin 64 → ℕ := fun t =>
  if t.val = 0 then a0 else if t.val = 1 then a1 else if t.val = 28 then a28 else if t.val = 60 then a60
  else if t.val = 8 then K else if t.val = 9 then N else if t.val = 10 then N * K else if t.val = 11 then k
  else if t.val = 12 then 2 * k * (N * K) else if t.val = 29 then 1 * (2 * k) * N else if t.val = 57 then Z
  else if t.val = 58 then R else if t.val = 59 then nJ else if t.val = 61 then k * (N * K) else U

theorem ite_le' {c : Prop} [Decidable c] {a b U : ℕ} (ha : a ≤ U) (hb : b ≤ U) :
    (if c then a else b) ≤ U := by
  split <;> assumption

theorem pcV_le {K N k Z R nJ U a0 a1 a28 a60 : ℕ} (h0 : a0 ≤ U) (h1 : a1 ≤ U) (h2 : a28 ≤ U)
    (h3 : a60 ≤ U) (t1 : K ≤ U) (t2 : N ≤ U) (t3 : N * K ≤ U) (t4 : k ≤ U)
    (t5 : 2 * k * (N * K) ≤ U) (t6 : 1 * (2 * k) * N ≤ U) (t7 : Z ≤ U) (t8 : R ≤ U) (t9 : nJ ≤ U)
    (t10 : k * (N * K) ≤ U) (t : Fin 64) : pcV K N k Z R nJ U a0 a1 a28 a60 t ≤ U := by
  simp only [pcV]
  repeat (first | exact h0 | exact h1 | exact h2 | exact h3 | exact t1 | exact t2 | exact t3 | exact t4 | exact t5 | exact t6 | exact t7 | exact t8 | exact t9 | exact t10 | exact le_rfl | apply ite_le')

theorem tmplTT_le2 {n : ℕ} (c : Fin n) (M T : ℕ) (hTM : T ≤ M) :
    ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ), (∀ i, β i ≤ M) → (∀ x ∈ l, x.2 ≤ T) →
      tmplTT c l β ≤ (l.length + 1) * ((2 * T + 1) * (4 * M + 12))
  | [], β, hβ, _ => by
    simp only [tmplTT, List.length_nil, Nat.zero_add, Nat.one_mul]
    have := supB_le_of hβ
    nlinarith
  | x :: l, β, hβ, hl => by
    simp only [tmplTT, List.length_cons]
    have hx := hl x (by simp)
    have ih := tmplTT_le2 c M T hTM l (natB x.1 c x.2 β) (natB_leT x.1 c x.2 hβ (hx.trans hTM))
      (fun y hy => hl y (by simp [hy]))
    have hs : max (supB β) x.2 ≤ M := max_le (supB_le_of hβ) (hx.trans hTM)
    have : (2 * x.2 + 1) * (4 * max (supB β) x.2 + 12) ≤ (2 * T + 1) * (4 * M + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith

theorem supB_pcU {U a0 a1 S : ℕ} (h0 : a0 ≤ S) (h1 : a1 ≤ S) (hU : U ≤ S) : supB (pcU U a0 a1) ≤ S :=
  supB_le_of fun t => by simp only [pcU]; split_ifs <;> omega

/-- A read into `dst` (scratch `4 5 6`) keeps the shape. -/
theorem ph_getU (o L : ℕ) (dst : Fin 64) (hd : dst.val ≠ 0 ∧ dst.val ≠ 1 ∧ dst.val ≠ 28 ∧ dst.val ≠ 60)
    {U a0 a1 S : ℕ} (h0 : a0 ≤ S) (h1 : a1 ≤ S) (hU : U ≤ S) :
    Ph (getAt o L 0 dst 4 5 6) (pcU U a0 a1) (getT o L S) (pcU (S + 1 + L) a0 a1) := by
  refine (ph_getAt o L (src := 0) (dst := dst) (tmp := 4) (a := 5) (b := 6) (by decide) (by decide)
    (pcU U a0 a1)).mono le_rfl (getT_mono le_rfl le_rfl (supB_pcU h0 h1 hU)) ?_
  have hs := supB_pcU h0 h1 hU
  obtain ⟨d0, d1, d28, d60⟩ := hd
  intro t
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  by_cases ht : t = 4 ∨ t = dst ∨ t = 5 ∨ t = 6
  · rw [if_pos ht]
    rcases ht with rfl | rfl | rfl | rfl <;> simp [pcU, d0, d1, d28, d60] <;> omega
  · rw [if_neg ht]
    simp only [pcU]; split_ifs <;> omega

theorem prefT_mono {P M M' : ℕ} (h : M ≤ M') : prefT P M ≤ prefT P M' := by
  unfold prefT; gcongr

theorem check_gadP_top :
    check 8 SigabaNeo.Tape.Prog.gadP (σGad ++ List.replicate 15 pTop) σGad' wGad = true := by
  decide +kernel

theorem sGad : Sound SigabaNeo.Tape.Prog.gadP (σGad ++ List.replicate 15 pTop)
    (σGad' ++ List.replicate 21 pTop) wGad :=
  SigabaNeo.Tape.Sym.sound_of_check check_gadP_top

/-- The bounds after `postCoreC`: tape `0`, tape `1`, the others blank. -/
def pcF (F0 F1 : ℕ) : Fin 64 → ℕ := fun t => if t.val = 0 then F0 else if t.val = 1 then F1 else 0

section V
variable {K N k Z R nJ : ℕ}

theorem tm_test (K N k Z R nJ M4 D Wv : ℕ) (hD : D ≤ M4) (hW : Wv ≤ M4) (t1 : K ≤ M4) (t2 : N ≤ M4) (t3 : N * K ≤ M4) (t4 : k ≤ M4) (t5 : 2 * k * (N * K) ≤ M4)
    (t6 : 1 * (2 * k) * N ≤ M4) (t7 : Z ≤ M4) (t8 : R ≤ M4) (t9 : nJ ≤ M4) (t10 : k * (N * K) ≤ M4) :
    tmplB (53 : Fin 64) (postTmplC N K k Z R nJ) (pcU M4 D Wv) ≤ pcV K N k Z R nJ M4 D Wv 0 0 := fun t => by
  have hmx : 2 * k * max (N * K) N ≤ M4 := by
    rw [← Nat.mul_max_mul_left]; exact max_le (by omega) (by simp only [one_mul] at t6; omega)
  fin_cases t <;> simp [tmplB, postTmplC, natB, pcU, pcV, max_le_iff] <;> omega


theorem v_skip {M4 D Wv : ℕ} (hD : D ≤ M4) (hW : Wv ≤ M4) (t7 : Z ≤ M4) (t8 : R ≤ M4) (t9 : nJ ≤ M4) :
    skB (pcV K N k Z R nJ M4 D Wv 0 0) 56 62 63 M4 nJ Z nJ ≤ pcV K N k Z R nJ (M4 + nJ * Z) D Wv 0 0 :=
  fun t => by fin_cases t <;> simp [skB, pcV, max_le_iff] <;> omega

theorem v_clr0 {U a0 a1 a28 a60 : ℕ} :
    (Prim.clear (0 : Fin 64)).lenT (pcV K N k Z R nJ U a0 a1 a28 a60) ≤ pcV K N k Z R nJ U 0 a1 a28 a60 :=
  fun t => by fin_cases t <;> simp [Prim.lenT, pcV]

theorem v_pref0 {U a0 a1 a28 a60 P S U' : ℕ} (hs : supB (pcV K N k Z R nJ U a0 a1 a28 a60) ≤ S)
    (hU : U ≤ U') (hS : S + 1 + P ≤ U') :
    (fun t : Fin 64 => if t = 0 then pcV K N k Z R nJ U a0 a1 a28 a60 0 + P
      else if t = 4 ∨ t = 5 then supB (pcV K N k Z R nJ U a0 a1 a28 a60) + 1 + P
      else pcV K N k Z R nJ U a0 a1 a28 a60 t) ≤ pcV K N k Z R nJ U' (a0 + P) a1 a28 a60 :=
  fun t => by fin_cases t <;> simp [pcV] <;> omega

theorem v_pref60 {U a0 a1 a28 a60 P S U' : ℕ} (hs : supB (pcV K N k Z R nJ U a0 a1 a28 a60) ≤ S)
    (hU : U ≤ U') (hS : S + 1 + P ≤ U') :
    (fun t : Fin 64 => if t = 60 then pcV K N k Z R nJ U a0 a1 a28 a60 60 + P
      else if t = 4 ∨ t = 5 then supB (pcV K N k Z R nJ U a0 a1 a28 a60) + 1 + P
      else pcV K N k Z R nJ U a0 a1 a28 a60 t) ≤ pcV K N k Z R nJ U' a0 a1 a28 (a60 + P) :=
  fun t => by fin_cases t <;> simp [pcV] <;> omega

theorem v_tails {U a0 a1 a28 a60 Zr : ℕ} :
    Function.update (pcV K N k Z R nJ U a0 a1 a28 a60) 1 (pcV K N k Z R nJ U a0 a1 a28 a60 1 - Zr) ≤
      pcV K N k Z R nJ U a0 (a1 - Zr) a28 a60 :=
  fun t => by fin_cases t <;> simp [pcV, Function.update_apply]

theorem v_zeros {U a0 a1 a28 a60 : ℕ} (h : k * (N * K) ≤ U) :
    mvB (pcV K N k Z R nJ U a0 a1 a28 a60) 60 63 61 ≤ pcV K N k Z R nJ U a0 a1 a28 (a60 + k * (N * K)) :=
  fun t => by fin_cases t <;> simp [mvB, pcV, Function.update_apply] <;> omega

theorem v_copy {U a0 a1 a28 a60 : ℕ} :
    (Prim.copy (1 : Fin 64) 28).lenT (pcV K N k Z R nJ U a0 a1 a28 a60) ≤ pcV K N k Z R nJ U a0 a28 a28 a60 :=
  fun t => by fin_cases t <;> simp [Prim.lenT, pcV, Function.update_apply]


theorem v_clearL {U a0 a1 a28 a60 : ℕ} :
    (fun t : Fin 64 => if t ∈ ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
    23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
    47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63] : List (Fin 64)) then 0
      else pcV K N k Z R nJ U a0 a1 a28 a60 t) ≤ pcF a0 a1 :=
  fun t => by fin_cases t <;> simp [pcV, pcF]


open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT in
theorem v_gad_in {U a0 a1 a28 a60 : ℕ} (j : Fin 21) :
    pcV K N k Z R nJ U a0 a1 a28 a60 (uGc j) ≤ bnd (vars U N K 0 0 0 k) (σGad ++ List.replicate 15 pTop) j := by
  fin_cases j <;> simp [uGc, pcV, bnd, aGet, σGad, pTop, pK, pN, pNK, pk, p2kNK, mo, pEval, mEval, vars, top] <;> ring_nf <;> omega

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT in
theorem v_gad_out {U a0 a1 a28 a60 : ℕ} (h : 2 * k * (N * K) ≤ U) (j : Fin 21) :
    bnd (vars U N K 0 0 0 k) (σGad' ++ List.replicate 21 pTop) j ≤ pcV K N k Z R nJ U a0 a1 a28 a60 (uGc j) := by
  fin_cases j <;> simp [uGc, pcV, bnd, aGet, σGad', pTop, pK, pN, pNK, pk, p2kNK, mo, pEval, mEval, vars, top] <;> ring_nf at * <;> omega

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT in
theorem v_add_in {U a0 a1 a28 a60 : ℕ} (h28 : a28 ≤ U) (h1 : a1 ≤ (1 * (2 * k) * N) * K) (h60 : a60 ≤ (1 * (2 * k) * N) * K)
    (j : Fin 28) :
    pcV K N k Z R nJ U a0 a1 a28 a60 (uAc j) ≤ bnd (vars U (1 * (2 * k) * N) K 0 0 0 0) (σRing ++ List.replicate 23 pTop) j := by
  fin_cases j <;> simp [uAc, pcV, bnd, aGet, σRing, pTop, pK, pN, pNK, mo, pEval, mEval, vars, top] <;> ring_nf at * <;> omega

open SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT in
theorem v_add_out {U a0 : ℕ} (j : Fin 28) :
    bnd (vars U (1 * (2 * k) * N) K 0 0 0 0) (σRing' ++ List.replicate 28 pTop) j ≤
      pcV K N k Z R nJ U a0 ((1 * (2 * k) * N) * K) ((1 * (2 * k) * N) * K) ((1 * (2 * k) * N) * K) (uAc j) := by
  fin_cases j <;> simp [uAc, pcV, bnd, aGet, σRing', pTop, pK, pN, pNK, mo, pEval, mEval, vars, top] <;> ring_nf at * <;> omega
theorem v_rest {U a0 a1 a60 B : ℕ} (h1 : a1 ≤ B) (h60 : a60 ≤ B) (t : Fin 64) :
    pcV K N k Z R nJ U a0 a1 0 a60 t ≤ pcV K N k Z R nJ U a0 B B B t := by
  fin_cases t <;> simp [pcV] <;> omega

end V

/-- **The time of `postCoreC`, per tape** (`D` the input bound, `T` the templates' bound). -/
def postCT' (L A NK oW LW Zr N K k Z R nJ D T : ℕ) : ℕ :=
  let U1 := D + 1 + L
  let U2 := U1 + 1 + A
  let U3 := U2 + 1 + NK
  let M4 := U3 + 1 + LW
  let M5 := M4 + nJ * Z
  let U6 := M5 + 1 + L
  let U7 := U6 + 1 + A
  let U8 := U7 + 1 + nJ * R
  let U9 := U8 + 1 + NK
  let U10 := U9 + 1 + k * (N * K)
  getT 0 L D +
    (getT oW A U1 +
    (getT (oW + A) NK U2 +
    (getT oW LW U3 +
    (11 * ((2 * T + 1) * (4 * M4 + 12)) +
    (skT M4 (M4 + M4 + nJ * Z) nJ Z +
    ((2 * (M5 + 1) + 3) +
    (prefT L M5 +
    (prefT A U6 +
    (prefT (nJ * R) U7 +
    (prefT NK U8 +
    ((Zr + 1) * (2 * (U9 + 1) + 3) +
    ((2 * U9 + 3) * (15 * (N * K) * k + 9 * N * k + 11 * K * k + 34 * k + 11 * K + 24) +
    ((k * (N * K) + 1) * (6 * (U9 + k * (N * K)) + 20) +
    (prefT (k * (N * K)) U9 +
    ((2 * U10 + 3) * (29 * ((1 * (2 * k) * N) * K) + 28 * (1 * (2 * k) * N) + 7) +
    ((2 * (U10 + 1) + 3) +
    ((62 * (2 * (U10 + 1) + 3) + (2 * (U10 + 1) + 3)))))))))))))))))))

set_option maxHeartbeats 4000000 in
/-- **`postCoreC` per tape.** -/
theorem ph_postCoreC' (L A NK oW LW Zr N K k Z R nJ D T Wv : ℕ)
    (hTD : T ≤ D) (hWD : Wv ≤ D) (hW : Wv ≤ Zr + (1 * (2 * k) * N) * K) (hRZ : R ≤ Z)
    (t1 : K ≤ T) (t2 : N ≤ T) (t3 : N * K ≤ T) (t4 : k ≤ T) (t5 : 2 * k * (N * K) ≤ T)
    (t6 : 1 * (2 * k) * N ≤ T) (t7 : Z ≤ T) (t8 : nJ ≤ T) (t9 : k * (N * K) ≤ T) :
    Ph (postCoreC L A NK oW LW Zr N K k Z R nJ) (pcU 0 D Wv)
      (postCT' L A NK oW LW Zr N K k Z R nJ D T)
      (pcF (L + A + nJ * R + NK) ((1 * (2 * k) * N) * K)) := by
  have t7' : R ≤ T := hRZ.trans t7
  have hW' : Wv - Zr ≤ (1 * (2 * k) * N) * K := by omega
  have hNK2 : k * (N * K) + k * (N * K) = (1 * (2 * k) * N) * K := by ring
  -- the bounds of the stages
  have hle : ∀ {U a0 a1 a28 a60 : ℕ}, T ≤ U → a0 ≤ U → a1 ≤ U → a28 ≤ U → a60 ≤ U →
      ∀ t, pcV K N k Z R nJ U a0 a1 a28 a60 t ≤ U := fun hT h0 h1 h2 h3 t =>
    pcV_le h0 h1 h2 h3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) t
  have hsup : ∀ {U a0 a1 a28 a60 : ℕ}, T ≤ U → a0 ≤ U → a1 ≤ U → a28 ≤ U → a60 ≤ U →
      supB (pcV K N k Z R nJ U a0 a1 a28 a60) ≤ U := fun hT h0 h1 h2 h3 =>
    supB_le_of (hle hT h0 h1 h2 h3)
  -- the reads
  have p1 := ph_getU 0 L 2 (by decide) (S := D) (U := 0) (a0 := D) (a1 := Wv) le_rfl hWD (by omega)
  have p2 := ph_getU oW A 3 (by decide) (S := D + 1 + L) (a0 := D) (a1 := Wv) (by omega)
    (by omega) le_rfl
  have p3 := ph_getU (oW + A) NK 54 (by decide) (S := D + 1 + L + 1 + A) (a0 := D) (a1 := Wv)
    (by omega) (by omega) le_rfl
  have p4 := ph_getU oW LW 55 (by decide) (S := D + 1 + L + 1 + A + 1 + NK) (a0 := D) (a1 := Wv)
    (by omega) (by omega) le_rfl
  set M4 := D + 1 + L + 1 + A + 1 + NK + 1 + LW with hM4
  -- the templates
  have p5 := (ph_tmplP (53 : Fin 64) (postTmplC N K k Z R nJ) (pcU M4 D Wv)
    (by simp [postTmplC])).mono le_rfl
    (tmplTT_le2 (53 : Fin 64) M4 T (by omega) _ _ (fun i => by fin_cases i <;> simp [pcU] <;> omega)
      (by simp only [postTmplC, List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption))
    (tm_test K N k Z R nJ M4 D Wv (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  -- the reading loop
  have p6 := (ph_skipLoopP' (out := (56 : Fin 64)) (src := 55) (c := 62) (c' := 63) (tn := 59)
    (tz := 57) (tr := 58) (by decide) (M := M4) (O := M4) (n := nJ) (R := Z)
    (pcV K N k Z R nJ M4 D Wv 0 0) (fun t _ => hle (by omega) (by omega) (by omega) (by omega)
      (by omega) t)
    (by simp [pcV]) (by simp [pcV]) (by simp [pcV]) (by simp [pcV]; omega) (by omega)
    (by omega)).mono le_rfl
    (show _ ≤ skT M4 (M4 + M4 + nJ * Z) nJ Z by
      have := hsup (U := M4) (a0 := D) (a1 := Wv) (a28 := 0) (a60 := 0) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      unfold skT; omega)
    (v_skip (by omega) (by omega) (by omega) (by omega) (by omega))
  set M5 := M4 + nJ * Z with hM5
  -- the clearing of tape 0 and the prefixes
  have p7 := (ph_prim (Prim.clear (0 : Fin 64)) (pcV K N k Z R nJ M5 D Wv 0 0)).mono le_rfl
    (show _ ≤ 2 * (M5 + 1) + 3 by
      have := hsup (U := M5) (a0 := D) (a1 := Wv) (a28 := 0) (a60 := 0) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      omega) v_clr0
  have p8 := (ph_prefP' L (src := (2 : Fin 64)) (dst := 0) (a := 4) (b := 5) (by decide) (by decide)
    (pcV K N k Z R nJ M5 0 Wv 0 0)).mono le_rfl
    (prefT_mono (hsup (by omega) (by omega) (by omega) (by omega) (by omega)))
    (v_pref0 (U' := M5 + 1 + L) (hsup (by omega) (by omega) (by omega) (by omega) (by omega))
      (by omega) le_rfl)
  have p9 := (ph_prefP' A (src := (3 : Fin 64)) (dst := 0) (a := 4) (b := 5) (by decide) (by decide)
    (pcV K N k Z R nJ (M5 + 1 + L) (0 + L) Wv 0 0)).mono le_rfl
    (prefT_mono (hsup (by omega) (by omega) (by omega) (by omega) (by omega)))
    (v_pref0 (U' := M5 + 1 + L + 1 + A) (hsup (by omega) (by omega) (by omega) (by omega) (by omega))
      (by omega) le_rfl)
  have p10 := (ph_prefP' (nJ * R) (src := (56 : Fin 64)) (dst := 0) (a := 4) (b := 5) (by decide)
    (by decide) (pcV K N k Z R nJ (M5 + 1 + L + 1 + A) (0 + L + A) Wv 0 0)).mono le_rfl
    (prefT_mono (hsup (by omega) (by omega) (by omega) (by omega) (by omega)))
    (v_pref0 (U' := M5 + 1 + L + 1 + A + 1 + nJ * R)
      (hsup (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega) le_rfl)
  have p11 := (ph_prefP' NK (src := (54 : Fin 64)) (dst := 0) (a := 4) (b := 5) (by decide)
    (by decide) (pcV K N k Z R nJ (M5 + 1 + L + 1 + A + 1 + nJ * R) (0 + L + A + nJ * R) Wv 0 0)).mono
    le_rfl (prefT_mono (hsup (by omega) (by omega) (by omega) (by omega) (by omega)))
    (v_pref0 (U' := M5 + 1 + L + 1 + A + 1 + nJ * R + 1 + NK)
      (hsup (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega) le_rfl)
  set U9 := M5 + 1 + L + 1 + A + 1 + nJ * R + 1 + NK with hU9
  set F0 := 0 + L + A + nJ * R + NK with hF0
  -- the tails of tape 1
  have p12 := (ph_tailsX (1 : Fin 64) Zr (pcV K N k Z R nJ U9 F0 Wv 0 0)).mono le_rfl
    (show _ ≤ (Zr + 1) * (2 * (U9 + 1) + 3) from Nat.mul_le_mul_left _ (by
      have := hsup (U := U9) (a0 := F0) (a1 := Wv) (a28 := 0) (a60 := 0) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      omega)) v_tails
  -- the gadget row
  have p13 := ph_mapSound uGc_inj sGad (vars U9 N K 0 0 0 k) (pcV K N k Z R nJ U9 F0 (Wv - Zr) 0 0)
    (pcV K N k Z R nJ U9 F0 (Wv - Zr) 0 0) v_gad_in
    (fun t => hle (U := U9) (by omega) (by omega) (by omega) (by omega) (by omega) t)
    (v_gad_out (by omega)) (fun t _ => le_rfl)
  have hsg : (2 * top (vars U9 N K 0 0 0 k) + 3) * pEval (vars U9 N K 0 0 0 k) wGad =
      (2 * U9 + 3) * (15 * (N * K) * k + 9 * N * k + 11 * K * k + 34 * k + 11 * K + 24) := by
    simp [top, wGad, pEval, mEval, vars]; ring
  rw [hsg] at p13
  -- the zeros and the second row
  have p14 := (ph_zerosP (r := (60 : Fin 64)) (c := 63) (t := 61) (by decide) (by decide)
    (pcV K N k Z R nJ U9 F0 (Wv - Zr) 0 0)).mono le_rfl
    (show _ ≤ (k * (N * K) + 1) * (6 * (U9 + k * (N * K)) + 20) by
      have hs := hsup (U := U9) (a0 := F0) (a1 := Wv - Zr) (a28 := 0) (a60 := 0) (by omega)
        (by omega) (by omega) (by omega) (by omega)
      have e : pcV K N k Z R nJ U9 F0 (Wv - Zr) 0 0 61 = k * (N * K) := by simp [pcV]
      unfold mvT; rw [e]
      exact Nat.mul_le_mul le_rfl (by omega))
    (v_zeros (by omega))
  have p15 := (ph_prefP' (k * (N * K)) (src := (7 : Fin 64)) (dst := 60) (a := 4) (b := 5)
    (by decide) (by decide) (pcV K N k Z R nJ U9 F0 (Wv - Zr) 0 (0 + k * (N * K)))).mono le_rfl
    (prefT_mono (hsup (by omega) (by omega) (by omega) (by omega) (by omega)))
    (v_pref60 (U' := U9 + 1 + k * (N * K)) (hsup (by omega) (by omega) (by omega) (by omega)
      (by omega)) (by omega) le_rfl)
  set U10 := U9 + 1 + k * (N * K) with hU10
  -- the sum
  have p16 := ph_mapSound uAc_inj SigabaNeo.Tape.Prog.StepT.sAdd (vars U10 (1 * (2 * k) * N) K 0 0 0 0)
    (pcV K N k Z R nJ U10 F0 (Wv - Zr) 0 (0 + k * (N * K) + k * (N * K)))
    (pcV K N k Z R nJ U10 F0 ((1 * (2 * k) * N) * K) ((1 * (2 * k) * N) * K) ((1 * (2 * k) * N) * K))
    (v_add_in (by omega) hW' (by omega))
    (fun t => hle (U := U10) (by omega) (by omega) (by omega) (by omega) (by omega) t)
    v_add_out
    (fun t ht => by
      clear ht
      exact v_rest (by omega) (by omega) t)
  have hsa : (2 * top (vars U10 (1 * (2 * k) * N) K 0 0 0 0) + 3) *
      pEval (vars U10 (1 * (2 * k) * N) K 0 0 0 0) wAdd =
      (2 * U10 + 3) * (29 * ((1 * (2 * k) * N) * K) + 28 * (1 * (2 * k) * N) + 7) := by
    simp [top, wAdd, pEval, mEval, vars]; ring
  rw [hsa] at p16
  have p17 := (ph_prim (Prim.copy (1 : Fin 64) 28) (pcV K N k Z R nJ U10 F0 ((1 * (2 * k) * N) * K)
    ((1 * (2 * k) * N) * K) ((1 * (2 * k) * N) * K))).mono le_rfl
    (show _ ≤ 2 * (U10 + 1) + 3 by
      have := hsup (U := U10) (a0 := F0) (a1 := (1 * (2 * k) * N) * K)
        (a28 := (1 * (2 * k) * N) * K) (a60 := (1 * (2 * k) * N) * K) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      omega) v_copy
  have p18 := (ph_clearL [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
    23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46,
    47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
    (pcV K N k Z R nJ U10 F0 ((1 * (2 * k) * N) * K) ((1 * (2 * k) * N) * K)
      ((1 * (2 * k) * N) * K))).mono le_rfl
    (show _ ≤ 62 * (2 * (U10 + 1) + 3) + (2 * (U10 + 1) + 3) by
      have := hsup (U := U10) (a0 := F0) (a1 := (1 * (2 * k) * N) * K)
        (a28 := (1 * (2 * k) * N) * K) (a60 := (1 * (2 * k) * N) * K) (by omega) (by omega)
        (by omega) (by omega) (by omega)
      simp only [List.length_cons, List.length_nil]; omega) v_clearL
  rw [postCoreC]
  refine (p1.seq <| p2.seq <| p3.seq <| p4.seq <| p5.seq <| p6.seq <| p7.seq <| p8.seq <| p9.seq <|
    p10.seq <| p11.seq <| p12.seq <| p13.seq <| p14.seq <| p15.seq <| p16.seq <| p17.seq p18).mono
    le_rfl (le_of_eq ?_) (le_of_eq ?_)
  · simp only [postCT', hM4, hM5, hU9, hU10, postTmplC, List.length_cons, List.length_nil]
  · simp only [hF0, Nat.zero_add]

end AdvancedEncryption.DualUse.Prog
