import PE.Impl.ExpLUT.Prog.RedKeyTAcc

/-!
# Module 9: coins and the candidate decoder at a large tape cap (tight)

* `rktSampleP`: F3's `cert_sampleP` for an arbitrary layout `layout M N K b` (`n ≤ b rCoin`);
* `rktDecC` … `rktDecQC`: F3's decoder certificates with the final subtraction charged with the
  ring word `rC2` as counter (F3: the tape cap);
* **`rktCandidateC`**: the candidate decoder from any `RingInputs M N K a`, generic in `M`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyT

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.XProg
open AdvancedEncryption.DualUse.Prog
open SigabaNeo.Lattices.Algo (length_encRM)
open AdvancedEncryption.ExpLUT.Prog
open AdvancedEncryption.ExpLUT.Prog.KeyTime

/-! ### Coins -/

theorem rktSampleP (M N K n : ℕ) (b : Fin 64 → ℕ) (h : RingInputs M N K (layout M N K b))
    (hn : n ≤ b rCoin) (hM : 1 ≤ M) :
    Cert (KeyCore.sampleP n) (layout M N K b) (layout M N K b)
      ((2 * (M + 1) + 3) + (bCoins n).T 0 M) := by
  let a0 := Function.update (layout M N K b) (tR rCoin) 0
  have hp := Cert.ofVB (XProg.VB.prim (.clear (tR rCoin)) h.top)
  have hi : ∀ t, a0 t ≤ M := update_top _ M h.top (tR rCoin) 0 (Nat.zero_le _)
  have hnM : n ≤ M := hn.trans (by simpa using h.top (tR rCoin))
  have hs : VB (.frame KeyCore.coinFrame (coinsF n)) a0 ((bCoins n).T 0 M)
      (layout M N K b) := by
    apply vb_smp KeyCore.coinFrame (atbb_coinsF n) (x := 0) (S := M)
    · simp [a0, KeyCore.coinFrame]
    · intro j _; exact hi _
    · change max 1 n ≤ M
      exact max_le hM hnM
    · change 0 + n * 1 ≤ layout M N K b (tR rCoin)
      simpa using hn
    · intro j hj
      fin_cases j <;> simp_all [KeyCore.coinFrame, layout, bCoins, Bnd.count, bCoin]
    · intro t
      by_cases ht : t = tR rCoin
      · subst t; simp [a0]
      · simp [a0, Function.update_of_ne ht]
  rw [KeyCore.sampleP]
  exact (hp.seq (Cert.ofVB hs)).mono le_rfl le_rfl le_rfl

set_option exponentiation.threshold 1000 in
theorem rktCoinTime (n : ℕ) (hn : n ≤ 2 ^ 106) :
    (2 * (2 ^ 150 + 1) + 3) + (bCoins n).T 0 (2 ^ 150) ≤ 2 ^ 264 := by
  change (2 * (2 ^ 150 + 1) + 3) + XProg.countT n 1 0 tCoin 0 (2 ^ 150) ≤ _
  unfold XProg.countT tCoin
  calc
    _ ≤ (2 * (2 ^ 150 + 1) + 3) +
        ((2 * 2 ^ 106 + 1) * (4 * (0 + 2 ^ 150) + 12) +
          (2 * (0 + 2 ^ 150) + 3) +
          (2 ^ 106 * (2 * (0 + 2 ^ 106 * 1 + (2 ^ 150 + 2 ^ 106 * 0)) + 3 +
            (6 * (0 + 2 ^ 106 * 1 + (2 ^ 150 + 2 ^ 106 * 0)) + 16) + 1) + 2) +
          (2 * (0 + 2 ^ 106 * 1 + (2 ^ 150 + 2 ^ 106 * 0)) + 3)) := by gcongr
    _ ≤ 2 ^ 264 := by norm_num

/-! ### The decoder (tight final subtraction) -/

def decT (M N K R : ℕ) : ℕ :=
  2 * (2 * M + 5) + R * (2 * M + decodeBodyTime M + 4) + 2 + operationBound M N K (N * K)

theorem rktDecC (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hk : b rTBk + b rTKmB ≤ K) (hn : b rTN ≤ R) (hs : R * K ≤ M) (hc2 : b rC2 ≤ N * K) :
    Cert (MVM.compile decC) (layout M N K b)
      (layout M N K (decodeResult M N K R b)) (decT M N K R) := by
  let c := Function.update b rDx M
  let c0 := Function.update c rDw 0
  have hic : RingInputs M N K (layout M N K c) := h.update_layout rDx M le_rfl
  have hi0 : RingInputs M N K (layout M N K c0) := hic.update_layout rDw 0 (Nat.zero_le _)
  have hib := decodeBase_inputs M N K b h
  have p0 := layout_clear_update M N K c hic.top rDw
  have p1 := layout_copy_update M N K c0 hi0.top AdvancedEncryption.ExpLUT.Prog.rDn rTN
  have he : Function.update c0 AdvancedEncryption.ExpLUT.Prog.rDn (c0 rTN) =
      Function.update (decodeBase M b) rDw 0 := by
    funext r
    by_cases h0 : r = rDw <;> by_cases h1 : r = AdvancedEncryption.ExpLUT.Prog.rDn <;>
      simp_all [c0, c, decodeBase, Function.update_apply]
  rw [he] at p1
  have p2 := compile_decLoop M N K R (decodeBase M b) hib
    (by simpa [decodeBase] using h.top (tR rTBk))
    (by simpa [decodeBase] using hk) (by simpa [decodeBase] using hn) hs
  have hil := hib.update_layout rDw (R * K) hs
  have p3 := rktOpU M N K (N * K) _ hil .sub rDo rDw rC2
    (by simpa [decodeBase] using hc2)
  rw [decC]
  apply (p0.seq (p1.seq (p2.seq p3))).mono _ le_rfl (by unfold decT; omega)
  apply layout_mono
  intro r
  by_cases hr : r = rDx
  · subst r; simpa [c] using h.top (tR rDx)
  · simp [c, Function.update_of_ne hr]

def decQBT (M N K R : ℕ) : ℕ := decT M N K R + appendAllowance M

theorem rktDecQBody (M N K R : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hk : b rTBk + b rTKmB ≤ K) (hn : b rTN ≤ R) (hr : R * K ≤ M)
    (hx : M ≤ b rDx) (hd : b rTN ≤ b AdvancedEncryption.ExpLUT.Prog.rDn)
    (hw : R * K ≤ b rDw) (ho : N * K ≤ b rDo) (hs : b rDq + N * K ≤ M) (hc2 : b rC2 ≤ N * K) :
    Cert (MVM.compile decQBody) (layout M N K b)
      (layout M N K (Function.update b rDq (b rDq + N * K))) (decQBT M N K R) := by
  let c := decodeResult M N K R b
  have hi := decodeResult_inputs M N K R b h hr
  have p0 := rktDecC M N K R b h hk hn hr hc2
  have p1 := layout_append_uniform M N K c hi.top rDq rDo
    (by simpa [c, decodeResult, decodeBase] using hs)
  have hle : c ≤ b := decodeResult_le M N K R b hx hd hw ho
  rw [decQBody]
  apply (p0.seq p1).mono le_rfl _ le_rfl
  apply layout_mono
  intro r
  by_cases he : r = rDq
  · subst r; simp [c, decodeResult, decodeBase]
  · simp only [Function.update_of_ne he]; exact hle r

def decQT (M N K R Q : ℕ) : ℕ := (2 * M + 5) + Q * (2 * M + decQBT M N K R + 4) + 2

theorem rktDecQC (M N K R Q : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b))
    (hk : b rTBk + b rTKmB ≤ K) (hn : b rTN ≤ R) (hr : R * K ≤ M)
    (hq : b rDqn ≤ Q) (hs : Q * (N * K) ≤ M) (hc2 : b rC2 ≤ N * K) :
    Cert (MVM.compile decQC) (layout M N K b)
      (layout M N K (Function.update (decodeQueueBase M b) rDq (Q * (N * K))))
      (decQT M N K R Q) := by
  let c := decodeQueueBase M b
  have hic := decodeQueueBase_inputs M N K b h
  let γ := fun j ↦ layout M N K (Function.update c rDq (j * (N * K)))
  have hi (j : ℕ) (hj : j ≤ Q) : RingInputs M N K (γ j) :=
    hic.update_layout rDq _ ((Nat.mul_le_mul_right (N * K) hj).trans hs)
  have p1 : Cert (MVM.compile (.rep rDqn decQBody)) (layout M N K (Function.update c rDq 0)) (γ Q)
      (Q * (2 * M + decQBT M N K R + 4) + 2) := by
    apply rep_family rDqn decQBody γ Q (decQBT M N K R) _
      (by simp [γ]) (by simpa [γ, c, decodeQueueBase] using hq)
    · intro j hj
      have hsize : (j + 1) * (N * K) ≤ M :=
        (Nat.mul_le_mul_right (N * K) (by omega : j + 1 ≤ Q)).trans hs
      have hb := rktDecQBody M N K R (Function.update c rDq (j * (N * K)))
        (hi j (by omega)) (by simpa [c, decodeQueueBase] using hk)
        (by simpa [c, decodeQueueBase] using hn) hr (by simp [c, decodeQueueBase])
        (by simpa [c, decodeQueueBase] using h.top (tR rTN))
        (by simpa [c, decodeQueueBase] using hr)
        (by simpa [c, decodeQueueBase] using h.ring)
        (by simpa only [Function.update_self, Nat.add_mul, Nat.one_mul] using hsize)
        (by simpa [c, decodeQueueBase] using hc2)
      simp only [Function.update_self, cap_reset] at hb
      rw [show j * (N * K) + N * K = (j + 1) * (N * K) by ring] at hb
      exact hb.mono (tailB_le (tR rDqn) _) le_rfl le_rfl
    · intro j hj; exact SigabaNeo.Tape.Prog.supB_le_of (hi j (by omega)).top
    · intro j hj
      apply layout_mono
      intro r
      by_cases he : r = rDq
      · subst r; simp only [Function.update_self]; exact Nat.mul_le_mul_right (N * K) hj
      · simp [Function.update_of_ne he]
  have p0 := layout_clear_update M N K c hic.top rDq
  rw [decQC]
  exact (p0.seq p1).mono (layout_mono _ _ _ (le_decodeQueueBase M N K b h)) le_rfl
    (by unfold decQT; omega)

/-! ### The candidate decoder -/

/-- The output envelope of the candidate decoder. -/
noncomputable def candOut (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ) : Fin 64 → ℕ :=
  Function.update (Function.update (decodeQueueBase M
    (fun r ↦ candidateInitResult D B M a (tR r))) rDq (nPI D * (D.N * D.K))) 9
    (nPI D * (D.N * D.K))

noncomputable def candT (D : Dims) (B M : ℕ) : ℕ :=
  (5 + templateTimeWeight (candidateInitOps D B)) * (2 * M + 5) +
    (decQT M D.N D.K D.N (nPI D) + (2 * M + 5))

/-- **The candidate decoder** (tight), from any `RingInputs` envelope. -/
theorem rktCandidateC (D : Dims) (B M : ℕ) (a : Fin 105 → ℕ)
    (h : RingInputs M D.N D.K a) (hM : 1 ≤ M)
    (hw : ((candidateInitOps D B).map (fun op ↦ op.2.weightBound)).sum ≤ M)
    (hBK : B ≤ D.K) (hNK : D.N * D.K ≤ M) (hq : nPI D * (D.N * D.K) ≤ M) :
    Cert (MVM.compile (candidateC D B)) a (layout M D.N D.K (candOut D B M a)) (candT D B M) := by
  let ai := candidateInitResult D B M a
  let b := fun r ↦ ai (tR r)
  have hi := candidateInitResult_inputs D B M D.N D.K a h hM hw
  obtain ⟨hB, hKB, hN, hQ⟩ := candidateInitResult_lengths D B M a
  have hb : RingInputs M D.N D.K (layout M D.N D.K b) :=
    layout_inputs _ _ _ b (fun r ↦ hi.top (tR r)) hi.ring hi.dimension hi.width
  have hin := le_layout M D.N D.K b ai hi.top hi.templateK hi.templateN hi.zeros.le hi.ones
    (fun _ ↦ le_rfl)
  have hk : b rTBk + b rTKmB ≤ D.K := by
    change ai (tR rTBk) + ai (tR rTKmB) ≤ _
    dsimp only [ai]
    rw [hB, hKB]
    omega
  have hn : b rTN ≤ D.N := by change ai (tR rTN) ≤ _; dsimp only [ai]; rw [hN]
  have hqq : b rDqn ≤ nPI D := by change ai (tR rDqn) ≤ _; dsimp only [ai]; rw [hQ]
  have hc2 : b rC2 ≤ D.N * D.K := by
    change ai (tR rC2) ≤ _
    simp [ai, candidateInitResult, templateBounds, candidateInitOps, TemplateWord.value,
      natResult_register, length_encRM]
  have hqb := (decodeQueueBase_inputs M D.N D.K b hb).update_layout rDq _ hq
  have p0 := compile_candidateInitC D B M a hM h.top hw
  have p1 := (rktDecQC M D.N D.K D.N (nPI D) b hb hk hn (le_of_eq_of_le (by ring) hNK) hqq hq
    hc2).mono hin le_rfl le_rfl
  have p2 := layout_copy_update M D.N D.K _ hqb.top 9 rDq
  simp only [Function.update_self] at p2
  rw [candidateC]
  exact (p0.seq (p1.seq p2)).mono le_rfl le_rfl (by unfold candT; exact le_rfl)

end AdvancedEncryption.ExpLUT.Prog.RedKeyT
