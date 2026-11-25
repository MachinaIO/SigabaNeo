import PE.Impl.ExpLUT.Prog.KeyTimeLoadScratch

/-! Runtime and length certificates for the actual binary-doubling unary initializer. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

/-- The initializer may retain static loop bounds on its two scratch tapes. -/
def natResult (r : Fin 64) (n M : ℕ) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  Function.update (Function.update (Function.update a 39 M) 40 M) (tR r) n

@[simp] theorem natResult_dest (r : Fin 64) (n M : ℕ) (a : Fin 105 → ℕ) :
    natResult r n M a (tR r) = n := by simp [natResult]

theorem natResult_other (r u : Fin 64) (h : u ≠ r) (n M : ℕ)
    (a : Fin 105 → ℕ) : natResult r n M a (tR u) = a (tR u) := by
  have h39 : tR u ≠ (39 : Fin 105) := by
    intro he; have := congrArg Fin.val he; simp [tR] at this; omega
  have h40 : tR u ≠ (40 : Fin 105) := by
    intro he; have := congrArg Fin.val he; simp [tR] at this; omega
  simp [natResult, Function.update_of_ne (fun he ↦ h (tR_inj he)), h39, h40]

theorem natResult_top (r : Fin 64) (n M : ℕ) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) (hn : n ≤ M) : ∀ t, natResult r n M a t ≤ M := by
  intro t
  simp only [natResult, Function.update_apply]
  split_ifs <;> first | assumption | exact le_rfl | exact ha t

theorem append_natResult (r s : Fin 64) (n M : ℕ) (a : Fin 105 → ℕ)
    (hs : natResult r n M a (tR s) ≤ M) :
    appendResult r s (natResult r n M a) ≤
      natResult r (n + natResult r n M a (tR s)) M a := by
  intro t
  by_cases hr : t = tR r
  · subst t; simp [appendResult]
  · simp only [appendResult, natResult, Function.update_apply]
    split_ifs <;> simp_all [natResult]

/-- Time is linear in the unary output length, with an explicit global tape bound. -/
theorem compile_natC (r u : Fin 64) (hru : r ≠ u) (n M : ℕ)
    (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ M) (hu : a (tR u) = 1) (hn : n ≤ M) :
    Cert (MVM.compile (natC r u n)) a (natResult r n M a)
      ((32 * n + 4) * (2 * M + 5)) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero =>
      rw [natC]
      have h := compile_clr_cert r a M ha
      apply h.mono le_rfl
      · intro t
        simp only [natResult, Function.update_apply]
        split_ifs <;> first | exact le_rfl | exact ha t
      · omega
    | succ n =>
      let q := (n + 1) / 2
      have hq : q < n + 1 := by dsimp [q]; omega
      have hqM : q ≤ M := by omega
      have hrec := ih q hq hqM
      have htop := natResult_top r q M a ha hqM
      have hdbl : q + q ≤ M := by dsimp [q]; omega
      have happ := compile_append r r (natResult r q M a) M htop (by simpa using hdbl)
      have hdouble : Cert (MVM.compile (.app r r)) (natResult r q M a)
          (natResult r (q + q) M a) ((4 * q + 6) * (2 * M + 5)) := by
        simpa only [natResult_dest] using
          happ.mono le_rfl (append_natResult r r q M a (by simpa using hqM)) le_rfl
      have hpair := hrec.seq hdouble
      have htop2 := natResult_top r (q + q) M a ha hdbl
      have hsource : natResult r (q + q) M a (tR u) = 1 :=
        (natResult_other r u (Ne.symm hru) _ _ _).trans hu
      rw [natC]
      by_cases he : (n + 1) % 2 = 0
      · rw [ite_eq_left he]
        have heq : q + q = n + 1 := by dsimp [q]; omega
        have h := hpair.seq (compile_nop _ M htop2)
        apply h.mono le_rfl
        · rw [heq]
        · have hqpos : 1 ≤ q := by omega
          nlinarith
      · rw [ite_eq_right he]
        have heq : q + q + 1 = n + 1 := by dsimp [q]; omega
        have hlast := compile_append r u (natResult r (q + q) M a) M htop2
          (by rw [natResult_dest, hsource, heq]; exact hn)
        have hout := append_natResult r u (q + q) M a (by rw [hsource]; omega)
        rw [hsource, heq] at hout
        have h := hpair.seq (hlast.mono le_rfl hout le_rfl)
        apply h.mono le_rfl le_rfl
        rw [hsource]
        nlinarith

end AdvancedEncryption.ExpLUT.Prog.KeyTime
