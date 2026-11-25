import PE.Impl.ExpLUT.Prog.KeyTimeCandidate
import PE.Impl.RingBTVW.Prog.TightApp

/-! Runtime of the actual framed fair-coin sampler and candidate generation. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog SigabaNeo.Tape.XProg
open AdvancedEncryption.RingBTVW.Prog

set_option exponentiation.threshold 1000 in
theorem keyCoinTime (n : ℕ) (hn : n ≤ 2 ^ 106) :
    (2 * (2 ^ 120 + 1) + 3) + (bCoins n).T 0 (2 ^ 120) ≤ 2 ^ 234 := by
  change (2 * (2 ^ 120 + 1) + 3) + countT n 1 0 tCoin 0 (2 ^ 120) ≤ _
  unfold countT tCoin
  calc
    _ ≤ (2 * (2 ^ 120 + 1) + 3) +
        ((2 * 2 ^ 106 + 1) * (4 * (0 + 2 ^ 120) + 12) +
          (2 * (0 + 2 ^ 120) + 3) +
          (2 ^ 106 * (2 * (0 + 2 ^ 106 * 1 + (2 ^ 120 + 2 ^ 106 * 0)) + 3 +
            (6 * (0 + 2 ^ 106 * 1 + (2 ^ 120 + 2 ^ 106 * 0)) + 16) + 1) + 2) +
          (2 * (0 + 2 ^ 106 * 1 + (2 ^ 120 + 2 ^ 106 * 0)) + 3)) := by gcongr
    _ ≤ 2 ^ 234 := by norm_num

/-- All scratch lengths may already be large; the sampler clears its output before generating bits. -/
theorem cert_sampleP (n : ℕ) (hn : n ≤ 2 ^ 106) :
    Cert (KeyCore.sampleP n) preparedBounds preparedBounds (2 ^ 234) := by
  let a0 := Function.update preparedBounds (tR rCoin) 0
  have hp := Cert.ofVB (XProg.VB.prim (.clear (tR rCoin)) preparedBounds_inputs.top)
  have hi : ∀ t, a0 t ≤ 2 ^ 120 :=
    update_top preparedBounds (2 ^ 120) preparedBounds_inputs.top (tR rCoin) 0 (Nat.zero_le _)
  have hs : VB (.frame KeyCore.coinFrame (coinsF n)) a0 ((bCoins n).T 0 (2 ^ 120))
      preparedBounds := by
    apply vb_smp KeyCore.coinFrame (atbb_coinsF n) (x := 0) (S := 2 ^ 120)
    · simp [a0, KeyCore.coinFrame]
    · intro j _; exact hi _
    · change max 1 n ≤ 2 ^ 120
      exact max_le (by norm_num) (hn.trans (by norm_num))
    · change 0 + n * 1 ≤ preparedBounds (tR rCoin)
      simpa [preparedBounds] using hn.trans (by norm_num : 2 ^ 106 ≤ 2 ^ 120)
    · intro j hj
      fin_cases j <;> simp_all [KeyCore.coinFrame, preparedBounds, layout, bCoins, Bnd.count, bCoin]
    · intro t
      by_cases ht : t = tR rCoin
      · subst t; simp [a0]
      · simp [a0, Function.update_of_ne ht]
  rw [KeyCore.sampleP]
  exact (hp.seq (Cert.ofVB hs)).mono le_rfl le_rfl (keyCoinTime n hn)

set_option exponentiation.threshold 1000 in
/-- The actual fair-bit sampler followed by the initialized candidate decoder. -/
theorem cert_sampleCandidate_Dc :
    Cert (.seq (KeyCore.sampleP (nPI Dc * Dc.N * Params.Bk))
      (MVM.compile (candidateC Dc Params.Bk))) preparedBounds preparedBounds (2 ^ 416) :=
  ((cert_sampleP _ KeyCore.keyCoinCount_Dc.le).seq
    (compile_candidateC_Dc preparedBounds preparedBounds_inputs)).mono le_rfl le_rfl (by norm_num)

set_option exponentiation.threshold 1000 in
/-- Preparation, fresh random coins and the complete real candidate decoder. -/
theorem cert_prepareSampleCandidate_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (.seq (MVM.compile (keyPrepareC Dc))
      (.seq (KeyCore.sampleP (nPI Dc * Dc.N * Params.Bk))
        (MVM.compile (candidateC Dc Params.Bk)))) a preparedBounds (2 ^ 463) :=
  ((compile_keyPrepareC_Dc a h).seq cert_sampleCandidate_Dc).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
