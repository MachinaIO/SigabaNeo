import PE.Impl.ExpLUT.Prog.KeyTimeEnter

/-! The invalid-predicate branch: load the public key, emit a zero key, pack and erase. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem keyInputResult_bit (D : Dims) (M : ℕ) (a : Fin 105 → ℕ) :
    keyInputResult D M a (tR rB1) = 1 := by
  unfold keyInputResult
  rw [fieldResult_other 0 16 rB1 _ _ _ (by decide) (by decide) (by decide),
    fieldResult_other 0 17 rB1 _ _ _ (by decide) (by decide) (by decide)]
  exact (initBits_sources a).2

def invalidBounds : Fin 64 → ℕ := Function.update (fun _ ↦ 2 ^ 120) rB1 1

theorem invalidBounds_inputs :
    RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K invalidBounds) := by
  apply layout_inputs
  · intro r; simp only [invalidBounds, Function.update_apply]; split_ifs <;> norm_num
  all_goals norm_num [Dc, Dims.N, Params.en, Params.Kc]

theorem keyInputResult_le_invalid (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    keyInputResult Dc (2 ^ 120) a ≤ layout (2 ^ 120) Dc.N Dc.K invalidBounds := by
  have hi := keyInputResult_inputs Dc (2 ^ 120) (2 ^ 24) (2 ^ 16) a h (by norm_num)
    keyCodec_bounds_Dc.1 keyCodec_bounds_Dc.2.1
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  rw [hn, hk]
  apply le_layout _ _ _ _ _ hi.top hi.templateK hi.templateN hi.zeros.le hi.ones
  intro r
  by_cases hr : r = rB1
  · subst r; simp only [invalidBounds, Function.update_self, keyInputResult_bit]; rfl
  · simpa only [invalidBounds, Function.update_of_ne hr] using hi.top (tR r)

theorem compile_invalidKeyC_of_parts (D : Dims) (a b c : Fin 105 → ℕ) (T0 T1 T2 T3 : ℕ)
    (p0 : Cert (MVM.compile (keyInputC D)) a b T0)
    (p1 : Cert (MVM.compile (.cp 14 17)) b b T1)
    (p2 : Cert (MVM.compile (natC 19 rB1 (codecSize (keyEnc D)))) b b T2)
    (p3 : Cert (MVM.compile packKeyC) b c T3) :
    Cert (MVM.compile (invalidKeyC D)) a c (T0 + (T1 + (T2 + T3))) :=
  p0.seq (p1.seq (p2.seq p3))

theorem compile_invalidKeyC_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (MVM.compile (invalidKeyC Dc)) a
      (layout (2 ^ 121) Dc.N Dc.K (packedResult invalidBounds)) (2 ^ 252) := by
  have hi := invalidBounds_inputs
  have p0 := (compile_keyInputC_Dc a h.top).mono le_rfl (keyInputResult_le_invalid a h) le_rfl
  have p1 := layout_copy (2 ^ 120) Dc.N Dc.K invalidBounds hi.top 14 17 (by simp [invalidBounds])
  have p2 := compile_rejectWord (codecSize (keyEnc Dc)) invalidBounds hi
    (by simp [invalidBounds]) (by simp [invalidBounds]) keyCodec_bounds_Dc.2.2
  have hm : 2 ^ 120 ≤ (2 ^ 121 : ℕ) := by norm_num
  have hj := layout_lift_inputs _ _ _ _ invalidBounds hm hi
  have hs : invalidBounds 14 + invalidBounds 19 ≤ 2 ^ 121 := by norm_num [invalidBounds]
  have p3 := (compile_packKeyC (2 ^ 121) Dc.N Dc.K invalidBounds hj hs).mono
    (layout_lift _ _ _ _ invalidBounds hm) le_rfl le_rfl
  exact (compile_invalidKeyC_of_parts Dc _ _ _ _ _ _ _ p0 p1 p2 p3).mono
    le_rfl le_rfl (by norm_num [appendAllowance])

theorem cert_invalidOutput_Dc (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (.seq (MVM.compile (invalidKeyC Dc)) (.prog MVM.IO.post)) a
      (outputBounds (2 ^ 121)) (2 ^ 253) := by
  have hm : 2 ^ 120 ≤ (2 ^ 121 : ℕ) := by norm_num
  have hi := layout_lift_inputs _ _ _ _ invalidBounds hm invalidBounds_inputs
  have hs : invalidBounds 14 + invalidBounds 19 ≤ 2 ^ 121 := by norm_num [invalidBounds]
  have hp := hi.update_layout 0 _ hs
  have p0 := compile_invalidKeyC_Dc a h
  have p1 := cert_vmPost (2 ^ 121) (layout (2 ^ 121) Dc.N Dc.K (packedResult invalidBounds)) hp.top
  have he : layout (2 ^ 121) Dc.N Dc.K (packedResult invalidBounds) 41 = 2 ^ 121 := by
    change packedResult invalidBounds 0 = _
    norm_num [packedResult, invalidBounds]
  rw [he] at p1
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

theorem cert_invalidP_Dc (a : Fin 105 → ℕ) (ht : ∀ t, a t ≤ 2 ^ 120) :
    Cert (KeyCore.invalidP Dc) a (outputBounds (2 ^ 121)) (2 ^ 254) := by
  have p0 := cert_enterP_Dc a ht
  have p1 := cert_invalidOutput_Dc preparedBounds preparedBounds_inputs
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

theorem outputBounds_mono {m n : ℕ} (h : m ≤ n) : outputBounds m ≤ outputBounds n := by
  intro t
  by_cases ht : t = 0 <;> simp only [outputBounds, ht, ↓reduceIte]
  · exact h
  · exact le_rfl

theorem cert_validP_uniform (r : ℕ) (a : Fin 105 → ℕ) (ht : ∀ t, a t ≤ 2 ^ 120) :
    Cert (KeyCore.validP Dc Params.Bk r) a (outputBounds (2 ^ 121)) (2 ^ 504) := by
  have hi := candidateTryResult_inputs preparedBounds preparedBounds_inputs
  have h14 : candidateTryResult preparedBounds 14 ≤ 2 ^ 120 := by simpa using hi.top (tR 14)
  have h19 : candidateTryResult preparedBounds 19 ≤ 2 ^ 120 := by simpa using hi.top (tR 19)
  exact (cert_validP_Dc r a ht).mono le_rfl (outputBounds_mono (by omega)) le_rfl

end AdvancedEncryption.ExpLUT.Prog.KeyTime
