import PE.Impl.ExpLUT.Prog.KeyTimeCore
/-! Packing the secret-key word and erasing the VM workspace. -/
set_option exponentiation.threshold 1000
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem Cert.progSeq {k : ℕ} {p q : SigabaNeo.Tape.Prog k} {a b c : Fin k → ℕ} {T U : ℕ}
    (hp : Cert (.prog p) a b T) (hq : Cert (.prog q) b c U) :
    Cert (.prog (.seq p q)) a c (T + U) := ⟨(hp.seq hq).len, (hp.seq hq).time⟩

def clearedBounds (ts : List (Fin 105)) (a : Fin 105 → ℕ) (t : Fin 105) :=
  if t ∈ ts then 0 else a t

theorem cert_clearList (ts : List (Fin 105)) (M : ℕ) (a : Fin 105 → ℕ)
    (ht : ∀ t, a t ≤ M) :
    Cert (.prog (MVM.IO.setList (fun _ ↦ []) ts)) a (clearedBounds ts a)
      ((ts.length + 1) * (2 * M + 5)) := by
  induction ts generalizing a with
  | nil =>
    have hp := Cert.ofVB (XProg.VB.prim (.copy (0 : Fin 105) 0) ht)
    apply hp.mono le_rfl
    · intro t; by_cases he : t = 0 <;> simp [Prim.lenT, clearedBounds, Function.update_apply, he]
    · simp only [List.length_nil]; omega
  | cons t ts ih =>
    have hp := Cert.ofVB (XProg.VB.prim (.clear t) ht)
    have hn := update_top a M ht t 0 (Nat.zero_le _)
    have hq := ih (Function.update a t 0) hn
    have he : clearedBounds ts (Function.update a t 0) = clearedBounds (t :: ts) a := by
      funext j; simp only [clearedBounds, List.mem_cons, Function.update_apply]
      split_ifs <;> simp_all
    rw [he] at hq
    exact (hp.progSeq hq).mono le_rfl le_rfl
      (by simp only [List.length_cons]; nlinarith)

def outputBounds (n : ℕ) (t : Fin 105) : ℕ := if t = 0 then n else 0

theorem cert_vmPost (M : ℕ) (a : Fin 105 → ℕ) (ht : ∀ t, a t ≤ M) :
    Cert (.prog MVM.IO.post) a (outputBounds (a 41)) (107 * (2 * M + 5)) := by
  have hp := Cert.ofVB (XProg.VB.prim (.copy (0 : Fin 105) 41) ht)
  have hn := update_top a M ht 0 (a 41) (ht 41)
  have hq := cert_clearList MVM.IO.postTapes M (Function.update a 0 (a 41)) hn
  have he : clearedBounds MVM.IO.postTapes (Function.update a 0 (a 41)) = outputBounds (a 41) := by
    funext t
    by_cases he : t = 0 <;> simp [clearedBounds, MVM.IO.postTapes, outputBounds, he]
  rw [he] at hq
  have hl : MVM.IO.postTapes.length ≤ 105 :=
    (List.length_filter_le _ _).trans (by simp)
  exact (hp.progSeq hq).mono le_rfl le_rfl (by nlinarith)

theorem layout_lift (M L N K : ℕ) (b : Fin 64 → ℕ) (hm : M ≤ L) :
    layout M N K b ≤ layout L N K b := by
  intro t; unfold layout; split_ifs <;> first | exact le_rfl | exact hm

theorem layout_lift_inputs (M L N K : ℕ) (b : Fin 64 → ℕ) (hm : M ≤ L)
    (h : RingInputs M N K (layout M N K b)) :
    RingInputs L N K (layout L N K b) :=
  layout_inputs L N K b (fun r ↦ (show b r ≤ M by simpa using h.top (tR r)).trans hm)
    (h.ring.trans hm) (h.dimension.trans hm) (h.width.trans hm)

def packedResult (b : Fin 64 → ℕ) : Fin 64 → ℕ := Function.update b 0 (b 14 + b 19)

theorem compile_packKeyC (M N K : ℕ) (b : Fin 64 → ℕ)
    (h : RingInputs M N K (layout M N K b)) (hs : b 14 + b 19 ≤ M) :
    Cert (MVM.compile packKeyC) (layout M N K b) (layout M N K (packedResult b))
      ((2 * M + 5) + appendAllowance M) := by
  let c := Function.update b 0 (b 14)
  have hc := h.update_layout 0 (b 14) (by simpa using h.top (tR 14))
  have p0 := layout_copy_update M N K b h.top 0 14
  have p1 := layout_append_uniform M N K c hc.top 0 19 (by simpa [c] using hs)
  have he : Function.update c 0 (c 0 + c 19) = packedResult b := by simp [c, packedResult]
  rw [he] at p1
  exact p0.seq p1

theorem cert_packPost_Dc (b : Fin 64 → ℕ)
    (h : RingInputs (2 ^ 120) Dc.N Dc.K (layout (2 ^ 120) Dc.N Dc.K b)) :
    Cert (.seq (MVM.compile packKeyC) (.prog MVM.IO.post)) (layout (2 ^ 120) Dc.N Dc.K b)
      (outputBounds (b 14 + b 19)) (2 ^ 250) := by
  have hm : 2 ^ 120 ≤ (2 ^ 121 : ℕ) := by norm_num
  have hi := layout_lift_inputs _ _ _ _ b hm h
  have hs : b 14 + b 19 ≤ 2 ^ 121 := by
    have h14 : b 14 ≤ 2 ^ 120 := by simpa using h.top (tR 14)
    have h19 : b 19 ≤ 2 ^ 120 := by simpa using h.top (tR 19)
    omega
  have p0 := (compile_packKeyC (2 ^ 121) Dc.N Dc.K b hi hs).mono
    (layout_lift _ _ _ _ b hm) le_rfl le_rfl
  have hp := hi.update_layout 0 (b 14 + b 19) hs
  have p1 := cert_vmPost (2 ^ 121) (layout (2 ^ 121) Dc.N Dc.K (packedResult b)) hp.top
  have he : layout (2 ^ 121) Dc.N Dc.K (packedResult b) 41 = b 14 + b 19 := by
    change packedResult b 0 = _; simp [packedResult]
  rw [he] at p1
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num [appendAllowance])

theorem cert_outputProgram_Dc (r : ℕ) (a : Fin 105 → ℕ)
    (h : RingInputs (2 ^ 120) (2 ^ 24) (2 ^ 16) a) :
    Cert (KeyCore.outputProgram Dc Params.Bk r) a
      (outputBounds (candidateTryResult preparedBounds 14 + candidateTryResult preparedBounds 19))
      (2 ^ 503) := by
  have p0 := cert_keyCore_program_Dc r a h
  have p1 := cert_packPost_Dc (candidateTryResult preparedBounds)
    (candidateTryResult_inputs preparedBounds preparedBounds_inputs)
  exact (p0.seq p1).mono le_rfl le_rfl (by norm_num)

end AdvancedEncryption.ExpLUT.Prog.KeyTime
