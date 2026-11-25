import PE.Impl.ExpLUT.Prog.KeyTimeNat

/-! Actual constant-word initialization, including literal bits and unary templates. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

@[simp] theorem natResult_nested (r : Fin 64) (m n M : ℕ) (a : Fin 105 → ℕ) :
    natResult r n M (natResult r m M a) = natResult r n M a := by
  funext t
  simp only [natResult, Function.update_apply]
  split_ifs <;> rfl

@[simp] theorem natResult_updated (r : Fin 64) (n m M : ℕ) (a : Fin 105 → ℕ) :
    natResult r n M (Function.update a (tR r) m) = natResult r n M a := by
  funext t
  simp only [natResult, Function.update_apply]
  split_ifs <;> rfl

theorem appendResult_le_natResult (r s : Fin 64) (M : ℕ) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) :
    appendResult r s a ≤ natResult r (a (tR r) + a (tR s)) M a := by
  intro t
  simp only [appendResult, natResult, Function.update_apply]
  split_ifs <;> first | exact le_rfl | exact Nat.zero_le _ | exact ha _

/-- Appending a literal uses one single-bit append per list entry. -/
theorem compile_emitBitsC (r : Fin 64) (h5 : r ≠ 5) (hf : r ≠ rB1)
    (bs : List Bool) (M : ℕ) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) (ht : a (tR 5) = 1) (hz : a (tR rB1) = 1)
    (hlen : a (tR r) + bs.length ≤ M) :
    Cert (MVM.compile (emitBitsC r bs)) a
      (natResult r (a (tR r) + bs.length) M a)
      ((10 * bs.length + 1) * (2 * M + 5)) := by
  induction bs generalizing a with
  | nil =>
    have h := compile_nop a M ha
    apply h.mono le_rfl
    · intro t
      simp only [List.length_nil, Nat.add_zero, natResult, Function.update_apply]
      split_ifs <;> simp_all
    · simp; omega
  | cons b bs ih =>
    let s : Fin 64 := if b then 5 else rB1
    have hs : a (tR s) = 1 := by cases b <;> assumption
    have happ := compile_append r s a M ha (by rw [hs]; simp only [List.length_cons] at hlen; omega)
    have hfirst := happ.mono le_rfl (appendResult_le_natResult r s M a ha) le_rfl
    rw [hs] at hfirst
    have hn : a (tR r) + 1 ≤ M := by simp only [List.length_cons] at hlen; omega
    have hnext := ih (natResult r (a (tR r) + 1) M a)
      (natResult_top r _ M a ha hn)
      (by rw [natResult_other r 5 (Ne.symm h5)]; exact ht)
      (by rw [natResult_other r rB1 (Ne.symm hf)]; exact hz)
      (by simp only [natResult_dest, List.length_cons] at *; omega)
    have h := hfirst.seq hnext
    simp only [natResult_dest, natResult_nested] at h
    have heq : a (tR r) + 1 + bs.length = a (tR r) + (b :: bs).length := by simp; omega
    rw [heq] at h
    apply h.mono le_rfl le_rfl
    simp only [List.length_cons]
    nlinarith

/-- Both forms of fixed template construction have a length-linear time bound. -/
theorem compile_template (r : Fin 64) (h5 : r ≠ 5) (hf : r ≠ rB1)
    (w : TemplateWord) (M : ℕ) (a : Fin 105 → ℕ)
    (ha : ∀ t, a t ≤ M) (ht : a (tR 5) = 1) (hz : a (tR rB1) = 1)
    (hlen : w.value.length ≤ M) :
    Cert (MVM.compile (w.code r)) a (natResult r w.value.length M a)
      ((32 * w.value.length + 6) * (2 * M + 5)) := by
  cases w with
  | zeros n =>
    simp only [TemplateWord.value, List.length_replicate] at hlen ⊢
    exact (compile_natC r rB1 hf n M a ha hz hlen).mono le_rfl le_rfl (by nlinarith)
  | bits bs =>
    let c := Function.update a (tR r) 0
    have hc : ∀ t, c t ≤ M := by
      intro t; simp only [c, Function.update_apply]; split_ifs <;> first | omega | exact ha t
    have ht' : c (tR 5) = 1 := by
      simp [c, Function.update_of_ne (fun he ↦ h5 (tR_inj he).symm), ht]
    have hz' : c (tR rB1) = 1 := by
      simp [c, Function.update_of_ne (fun he ↦ hf (tR_inj he).symm), hz]
    have hem := compile_emitBitsC r h5 hf bs M c hc ht' hz'
      (by simpa [c, TemplateWord.value] using hlen)
    have h := (compile_clr_cert r a M ha).seq hem
    simp [c] at h
    exact h.mono le_rfl le_rfl (by dsimp [TemplateWord.value]; nlinarith)

/-- Sequential bound transformation for all initialized template registers. -/
def templateBounds (M : ℕ) : List (Fin 64 × TemplateWord) →
    (Fin 105 → ℕ) → (Fin 105 → ℕ)
  | [], a => a
  | (r, w) :: ops, a => templateBounds M ops (natResult r w.value.length M a)

def templateTimeWeight : List (Fin 64 × TemplateWord) → ℕ
  | [] => 1
  | (_, w) :: ops => 32 * w.value.length + 6 + templateTimeWeight ops

/-- Compose the actual template instruction list without expanding any literal word. -/
theorem compile_templateOps (ops : List (Fin 64 × TemplateWord)) (M : ℕ)
    (a : Fin 105 → ℕ) (ha : ∀ t, a t ≤ M)
    (ht : a (tR 5) = 1) (hz : a (tR rB1) = 1)
    (hops : ∀ op ∈ ops, op.1 ≠ 5 ∧ op.1 ≠ rB1 ∧ op.2.value.length ≤ M) :
    Cert (MVM.compile (templateOpsC ops)) a (templateBounds M ops a)
      (templateTimeWeight ops * (2 * M + 5)) := by
  induction ops generalizing a with
  | nil =>
    exact (compile_nop a M ha).mono le_rfl le_rfl (by
      simp only [templateTimeWeight]; omega)
  | cons op ops ih =>
    rcases op with ⟨r, w⟩
    have hr := hops (r, w) (by simp)
    have hhead := compile_template r hr.1 hr.2.1 w M a ha ht hz hr.2.2
    have htail := ih (natResult r w.value.length M a)
      (natResult_top r _ M a ha hr.2.2)
      ((natResult_other r 5 (Ne.symm hr.1) _ _ _).trans ht)
      ((natResult_other r rB1 (Ne.symm hr.2.1) _ _ _).trans hz)
      (fun op hop ↦ hops op (by simp [hop]))
    have h := hhead.seq htail
    convert h using 1 <;> first | rfl | (simp only [templateTimeWeight]; ring)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
