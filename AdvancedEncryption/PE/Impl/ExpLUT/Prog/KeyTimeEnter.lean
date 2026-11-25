import PE.Impl.ExpLUT.Prog.KeyTimeLiteral

/-! Restoring the physical VM templates after arbitrary bounded parser workspace. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

def blankVM (N K : ℕ) : Store 105 := MVM.enc N K (fun _ ↦ [])

theorem blankVM_top (M N K : ℕ) (hn : N ≤ M) (hk : K ≤ M) (hr : N * K ≤ M) :
    ∀ t, (blankVM N K t).length ≤ M := by
  intro t
  unfold blankVM MVM.enc MVM.encX
  split_ifs <;> simp_all

def preResult (N K : ℕ) (a : Fin 105 → ℕ) (t : Fin 105) : ℕ :=
  if t = 41 then a 0 else if t = 42 then a 1 else (blankVM N K t).length

theorem preResult_inputs (M N K : ℕ) (a : Fin 105 → ℕ) (ht : ∀ t, a t ≤ M)
    (hn : N ≤ M) (hk : K ≤ M) (hr : N * K ≤ M) : RingInputs M N K (preResult N K a) := by
  refine ⟨?_, hr, hn, hk, ?_, ?_, ?_, ?_⟩
  · intro t; unfold preResult; split_ifs
    · exact ht 0
    · exact ht 1
    · exact blankVM_top M N K hn hk hr t
  all_goals simp [preResult, blankVM, MVM.enc, MVM.encX]

theorem cert_vmPre (M N K : ℕ) (a : Fin 105 → ℕ) (ht : ∀ t, a t ≤ M)
    (hn : N ≤ M) (hk : K ≤ M) (hr : N * K ≤ M) :
    Cert (.prog (MVM.IO.pre N K (fun _ ↦ 0))) a (preResult N K a)
      ((105 * (M + 1) + 3) * (2 * M + 5)) := by
  let c := Function.update a 41 (a 0)
  let d := Function.update c 42 (a 1)
  have hc := update_top a M ht 41 (a 0) (ht 0)
  have hd := update_top c M hc 42 (a 1) (ht 1)
  have p0 := Cert.ofVB (XProg.VB.prim (.copy (41 : Fin 105) 0) ht)
  have p1 := Cert.ofVB (XProg.VB.prim (.copy (42 : Fin 105) 1) hc)
  have he1 : (Prim.copy (42 : Fin 105) 1).lenT c = d := by simp [Prim.lenT, c, d]
  rw [he1] at p1
  have hf := blankVM_top M N K hn hk hr
  have p2 := cert_setList (blankVM N K) MVM.IO.preTapes M d hd (fun t _ ↦ hf t)
  have he2 : literalBounds (blankVM N K) MVM.IO.preTapes d = preResult N K a := by
    funext t
    by_cases h41 : t = 41 <;> by_cases h42 : t = 42 <;>
      simp [literalBounds, MVM.IO.preTapes, preResult, d, c, h41, h42]
  rw [he2] at p2
  have hl : MVM.IO.preTapes.length ≤ 105 :=
    (List.length_filter_le _ _).trans (by simp)
  have hw := literalWeight_le (blankVM N K) MVM.IO.preTapes M (fun t _ ↦ hf t)
  have hb : literalWeight (blankVM N K) MVM.IO.preTapes ≤ 105 * (M + 1) + 1 :=
    hw.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (M + 1) hl) 1)
  have all := p0.progSeq (p1.progSeq p2)
  simpa only [MVM.IO.pre, List.replicate_zero, blankVM] using
    all.mono le_rfl le_rfl (show _ ≤ (105 * (M + 1) + 3) * (2 * M + 5) by nlinarith)

theorem cert_enterP_Dc (a : Fin 105 → ℕ) (ht : ∀ t, a t ≤ 2 ^ 120) :
    Cert (KeyCore.enterP Dc) a preparedBounds (2 ^ 250) := by
  have hn : Dc.N = 2 ^ 24 := by norm_num [Dc, Dims.N, Params.en]
  have hk : Dc.K = 2 ^ 16 := by norm_num [Dc, Params.Kc]
  have hnM : Dc.N ≤ 2 ^ 120 := by rw [hn]; norm_num
  have hkM : Dc.K ≤ 2 ^ 120 := by rw [hk]; norm_num
  have hrM : Dc.N * Dc.K ≤ 2 ^ 120 := by rw [hn, hk]; norm_num
  have hi := preResult_inputs (2 ^ 120) Dc.N Dc.K a ht hnM hkM hrM
  have hle : preResult Dc.N Dc.K a ≤ preparedBounds := by
    have hh := le_layout (2 ^ 120) Dc.N Dc.K (fun _ ↦ 2 ^ 120) _ hi.top
      hi.templateK hi.templateN hi.zeros.le hi.ones (fun r ↦ hi.top (tR r))
    simpa only [hn, hk, preparedBounds] using hh
  have p0 := (cert_vmPre (2 ^ 120) Dc.N Dc.K a ht hnM hkM hrM).mono le_rfl hle le_rfl
  have p1 := layout_copy (2 ^ 120) (2 ^ 24) (2 ^ 16) (fun _ ↦ 2 ^ 120)
    preparedBounds_inputs.top rCs 1 le_rfl
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

theorem cert_validP_Dc (r : ℕ) (a : Fin 105 → ℕ) (ht : ∀ t, a t ≤ 2 ^ 120) :
    Cert (KeyCore.validP Dc Params.Bk r) a
      (outputBounds (candidateTryResult preparedBounds 14 + candidateTryResult preparedBounds 19))
      (2 ^ 504) := by
  have p0 := cert_enterP_Dc a ht
  have p1 := cert_outputProgram_Dc r preparedBounds preparedBounds_inputs
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
