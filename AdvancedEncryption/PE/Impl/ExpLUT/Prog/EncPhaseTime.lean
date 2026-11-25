import PE.Impl.ExpLUT.Prog.EncDescConf
/-! # Uniform time bounds for non-lengthening encryption phases -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog

/-- A syntax-derived polynomial bounds the actual per-tape clock. -/
theorem time_noGrow_le {k : ℕ} (p : SigabaNeo.Tape.Prog k) (hp : p.NoGrow)
    {M : ℕ} {ℓ : Fin k → ℕ} (hℓ : ∀ i, ℓ i ≤ M) :
    timeBoundT p ℓ ≤ p.tbC * (M + 1) ^ p.tbD :=
  (timeBoundT_mono p hℓ).trans ((timeBoundT_const_le p M).trans (timeBound_le p hp M))

/-- Charge a counted loop by its own template length, while bounding its body uniformly. -/
theorem time_forN_noGrow {k : ℕ} (p : SigabaNeo.Tape.Prog k) (hp : p.NoGrow)
    (c t : Fin k) {M n : ℕ} {ℓ : Fin k → ℕ}
    (hℓ : ∀ i, ℓ i ≤ M) (hn : ℓ t ≤ n) :
    timeBoundT (forN c t p) ℓ ≤ (2 * M + 3) +
      (n * (2 * M + 3 + p.tbC * (M + 1) ^ p.tbD + 1) + 2) := by
  let a := lenBoundT (cp c t) ℓ
  have ha : ∀ i, a i ≤ M := Sym.lenBoundT_le_const _ (by rfl) hℓ
  have hac : a c = ℓ t := by simp [a, lenBoundT, Prim.lenT]
  have hi : loopStepT c p (fun _ => M) ≤ fun _ => M := by
    exact Sym.lenBoundT_le_const p hp (fun i => (tailB_le c (fun _ => M) i))
  have hl := timeBoundT_loop_le_of_inv c p ha hi
  have hr := roundTimeT_le p c (fun _ => M)
  have hb := time_noGrow_le p hp (fun _ => le_refl M)
  have hs : supB (fun _ : Fin k => M) ≤ M := Sym.supB_le_const (fun _ => le_refl M)
  have hr' : roundTimeT (timeBoundT p) c (fun _ => M) ≤
      2 * M + 3 + p.tbC * (M + 1) ^ p.tbD := by omega
  rw [hac] at hl
  have hl' := hl.trans (Nat.add_le_add_right
    (Nat.mul_le_mul hn (Nat.add_le_add_right hr' 1)) 2)
  have hc : timeBoundT (cp c t) ℓ ≤ 2 * M + 3 := by
    have hs := Sym.supB_le_const hℓ
    simp only [timeBoundT, Prim.pad]
    omega
  exact Nat.add_le_add hc hl'

set_option maxRecDepth 100000 in
theorem degrees_mrow : (mrowP.tbC, mrowP.tbD) = (4356, 6) := by decide +kernel
set_option maxRecDepth 100000 in
theorem degrees_helper : (hBlkP.tbC, hBlkP.tbD) = (9791, 6) := by decide +kernel
set_option maxRecDepth 100000 in
theorem degrees_aut : (autBlkP.tbC, autBlkP.tbD) = (12766, 8) := by decide +kernel

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_mrow_uniform {ℓ : Fin 66 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) :
    timeBoundT mrowP ℓ ≤ 2 ^ 608 := by
  have h := time_noGrow_le mrowP noGrow_mrowP hℓ
  have hc : mrowP.tbC = 4356 := congrArg Prod.fst degrees_mrow
  have hd : mrowP.tbD = 6 := congrArg Prod.snd degrees_mrow
  rw [hc, hd] at h
  exact h.trans (by norm_num)

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_helper_uniform {ℓ : Fin 69 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) :
    timeBoundT hBlkP ℓ ≤ 2 ^ 609 := by
  have h := time_noGrow_le hBlkP noGrow_hBlkP hℓ
  have hc : hBlkP.tbC = 9791 := congrArg Prod.fst degrees_helper
  have hd : hBlkP.tbD = 6 := congrArg Prod.snd degrees_helper
  rw [hc, hd] at h
  exact h.trans (by norm_num)

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_aut_uniform {ℓ : Fin 85 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) :
    timeBoundT autBlkP ℓ ≤ 2 ^ 807 := by
  have h := time_noGrow_le autBlkP noGrow_autBlkP hℓ
  have hc : autBlkP.tbC = 12766 := congrArg Prod.fst degrees_aut
  have hd : autBlkP.tbD = 8 := congrArg Prod.snd degrees_aut
  rw [hc, hd] at h
  exact h.trans (by norm_num)

set_option maxRecDepth 100000 in
theorem degrees_cinBody : (cinBody.tbC, cinBody.tbD) = (9925, 8) := by decide +kernel

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
/-- The attribute digit phase has only sixteen outer iterations. -/
theorem time_cin_uniform {ℓ : Fin 104 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99)
    (hn : ℓ 35 ≤ 16) : timeBoundT cinP ℓ ≤ 2 ^ 811 := by
  have h := time_forN_noGrow cinBody (by rfl) 39 35 hℓ hn
  have hc : cinBody.tbC = 9925 := congrArg Prod.fst degrees_cinBody
  have hd : cinBody.tbD = 8 := congrArg Prod.snd degrees_cinBody
  rw [hc, hd] at h
  exact h.trans (by norm_num)

set_option maxRecDepth 100000 in
theorem degrees_cinbotBody : ((map tCb1 cbP).tbC, (map tCb1 cbP).tbD) = (4998, 6) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_cinbot_uniform {ℓ : Fin 104 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99)
    (hn : ℓ 35 ≤ 16) : timeBoundT cinbotP ℓ ≤ 2 ^ 613 := by
  have h := time_forN_noGrow (map tCb1 cbP) (by rfl) 39 35 hℓ hn
  have hc : (map tCb1 cbP).tbC = 4998 := congrArg Prod.fst degrees_cinbotBody
  have hd : (map tCb1 cbP).tbD = 6 := congrArg Prod.snd degrees_cinbotBody
  rw [hc, hd] at h
  exact h.trans (by norm_num)

set_option maxRecDepth 100000 in
theorem degrees_tailEnd : ((SigabaNeo.Tape.Prog.seq c0P cmP).tbC,
    (SigabaNeo.Tape.Prog.seq c0P cmP).tbD) = (8976, 6) := by decide +kernel

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_tailEnd_uniform {ℓ : Fin 104 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) :
    timeBoundT (.seq c0P cmP) ℓ ≤ 2 ^ 609 := by
  have h := time_noGrow_le (.seq c0P cmP) (by rfl) hℓ
  have hc : (SigabaNeo.Tape.Prog.seq c0P cmP).tbC = 8976 := congrArg Prod.fst degrees_tailEnd
  have hd : (SigabaNeo.Tape.Prog.seq c0P cmP).tbD = 6 := congrArg Prod.snd degrees_tailEnd
  rw [hc, hd] at h
  exact h.trans (by norm_num)

set_option maxRecDepth 100000 in
theorem cinbot_preserves_count : cinbotP.Preserves 35 :=
  preserves_of_preservesB (by decide +kernel)

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
/-- The complete final phase, with the sixteen-iteration template charged explicitly. -/
theorem time_tail_uniform {ℓ : Fin 104 → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99)
    (hn : ℓ 35 ≤ 16) : timeBoundT tailP ℓ ≤ 2 ^ 812 := by
  have h1 := time_cinbot_uniform hℓ hn
  have hl1 := Sym.lenBoundT_le_const cinbotP (by rfl) hℓ
  have hn1 : lenBoundT cinbotP ℓ 35 ≤ 16 := by
    rw [lenBoundT_of_preserves _ _ cinbot_preserves_count]; exact hn
  have h2 := time_cin_uniform hl1 hn1
  have hl2 := Sym.lenBoundT_le_const cinP (by rfl) hl1
  have h3 := time_tailEnd_uniform hl2
  exact (Nat.add_le_add h1 (Nat.add_le_add h2 h3)).trans (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.EncW
