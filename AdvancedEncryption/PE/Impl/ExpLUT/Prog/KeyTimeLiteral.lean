import PE.Impl.ExpLUT.Prog.KeyTimeOutput

/-! Exact length certificates for physical literal initialization. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM

theorem cert_putW {k : ℕ} (r : Fin k) (w : List Bool) (M : ℕ) (a : Fin k → ℕ)
    (ht : ∀ t, a t ≤ M) (hw : w.length ≤ M) :
    Cert (.prog (SigabaNeo.Tape.Prog.putW r w)) a (Function.update a r w.length)
      ((w.length + 1) * (2 * M + 5)) := by
  induction w with
  | nil =>
    exact (Cert.ofVB (XProg.VB.prim (.clear r) ht)).mono le_rfl le_rfl (by simp; omega)
  | cons b w ih =>
    have hlen : w.length ≤ M := by simp only [List.length_cons] at hw; omega
    have hp := ih hlen
    have hc : ∀ t, Function.update a r w.length t ≤ M := by
      intro t; by_cases he : t = r <;> simp [he, ht, hlen]
    have hq := Cert.ofVB (XProg.VB.prim (.cons r b) hc)
    have he : (Prim.cons r b).lenT (Function.update a r w.length) =
        Function.update a r (b :: w).length := by
      simp [Prim.lenT, Function.update_self]
    rw [he] at hq
    exact (hp.progSeq hq).mono le_rfl le_rfl (by simp only [List.length_cons]; nlinarith)

def literalBounds (f : Store 105) (ts : List (Fin 105)) (a : Fin 105 → ℕ) (t : Fin 105) :=
  if t ∈ ts then (f t).length else a t

def literalWeight (f : Store 105) (ts : List (Fin 105)) :=
  (ts.map (fun t ↦ (f t).length + 1)).sum + 1

theorem cert_setList (f : Store 105) (ts : List (Fin 105)) (M : ℕ) (a : Fin 105 → ℕ)
    (ht : ∀ t, a t ≤ M) (hf : ∀ t ∈ ts, (f t).length ≤ M) :
    Cert (.prog (MVM.IO.setList f ts)) a (literalBounds f ts a)
      (literalWeight f ts * (2 * M + 5)) := by
  induction ts generalizing a with
  | nil =>
    have hp := Cert.ofVB (XProg.VB.prim (.copy (0 : Fin 105) 0) ht)
    apply hp.mono le_rfl
    · intro t; by_cases he : t = 0 <;> simp [Prim.lenT, literalBounds, he]
    · simp [literalWeight]; omega
  | cons t ts ih =>
    have hlen := hf t (by simp)
    have hp := cert_putW t (f t) M a ht hlen
    have hn := update_top a M ht t (f t).length hlen
    have hq := ih (Function.update a t (f t).length) hn (fun r hr ↦ hf r (by simp [hr]))
    have he : literalBounds f ts (Function.update a t (f t).length) = literalBounds f (t :: ts) a := by
      funext j
      simp only [literalBounds, List.mem_cons, Function.update_apply]
      split_ifs <;> simp_all
    rw [he] at hq
    exact (hp.progSeq hq).mono le_rfl le_rfl
      (by simp only [literalWeight, List.map_cons, List.sum_cons]; nlinarith)

theorem literalWeight_le (f : Store 105) (ts : List (Fin 105)) (M : ℕ)
    (hf : ∀ t ∈ ts, (f t).length ≤ M) : literalWeight f ts ≤ ts.length * (M + 1) + 1 := by
  unfold literalWeight
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht := hf t (by simp)
    have hi := ih (fun r hr ↦ hf r (by simp [hr]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

end AdvancedEncryption.ExpLUT.Prog.KeyTime
