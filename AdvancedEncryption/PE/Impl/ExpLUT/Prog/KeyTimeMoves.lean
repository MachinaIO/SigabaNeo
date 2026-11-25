import PE.Impl.ExpLUT.Prog.KeyTimeBasic
/-! Register movement certificates for the actual MVM compiler. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog

theorem Cert.ofVB {k : ℕ} {p : XProg k} {a b : Fin k → ℕ} {T : ℕ}
    (h : XProg.VB p a T b) : Cert p a b T := ⟨(h a le_rfl).2, (h a le_rfl).1⟩

theorem Cert.toVB {k : ℕ} {p : XProg k} {a b : Fin k → ℕ} {T : ℕ}
    (h : Cert p a b T) : XProg.VB p a T b := fun _ hx ↦
  ⟨((XProg.timeBoundT_mono p) hx).trans h.time, ((XProg.lenBoundT_mono p) hx).trans h.len⟩

theorem embedF_update_bound {k m : ℕ} (e : Fin m ↪ Fin k) (a : Fin k → ℕ)
    (j : Fin m) (n : ℕ) :
    embedF e a (Function.update (a ∘ e) j n) = Function.update a (e j) n := by
  funext t
  rcases embedF_cases e a (Function.update (a ∘ e) j n) t with ⟨hn, ht⟩ | ⟨i, rfl, ht⟩
  · rw [ht]
    have hne : t ≠ e j := by
      intro h
      subst t
      rw [partialInv_self] at hn
      contradiction
    simp [Function.update_of_ne hne]
  · rw [ht]
    by_cases hij : i = j
    · subst i; simp
    · have he : e i ≠ e j := fun h ↦ hij (e.injective h)
      simp [Function.update_of_ne hij, Function.update_of_ne he]

/-- A framed primitive changes only its selected output tape. -/
theorem compile_cp_cert (d s : Fin 64) (hds : d ≠ s) (a : Fin 105 → ℕ)
    (M : ℕ) (hM : ∀ t, a t ≤ M) :
    Cert (MVM.compile (.cp d s)) a (Function.update a (tR d) (a (tR s)))
      (2 * (M + 1) + 3) := by
  let e := mkE (fCp d s) (fCp_inj hds)
  have h := (Cert.ofVB (XProg.VB.prim (.copy (0 : Fin 2) 1)
    (fun j ↦ hM (e j)))).frame e
  change Cert (.frame e (.prog (cp 0 1))) a
    (embedF e a (Function.update (a ∘ e) 0 (a (e 1)))) _ at h
  rw [embedF_update_bound] at h
  have h0 : e 0 = tR d := by apply Fin.ext; rfl
  have h1 : e 1 = tR s := by apply Fin.ext; rfl
  rw [h0, h1] at h
  simpa only [MVM.compile, dite_eq_right hds] using h

theorem compile_clr_cert (d : Fin 64) (a : Fin 105 → ℕ)
    (M : ℕ) (hM : ∀ t, a t ≤ M) :
    Cert (MVM.compile (.clr d)) a (Function.update a (tR d) 0) (2 * (M + 1) + 3) := by
  let e := mkE (f1 (tR d)) (f1_inj _)
  have h := (Cert.ofVB (XProg.VB.prim (.clear (0 : Fin 1))
    (fun j ↦ hM (e j)))).frame e
  change Cert (.frame e (.prog (clr 0))) a
    (embedF e a (Function.update (a ∘ e) 0 0)) _ at h
  rw [embedF_update_bound] at h
  exact h

theorem compile_tl_cert (d : Fin 64) (a : Fin 105 → ℕ)
    (M : ℕ) (hM : ∀ t, a t ≤ M) :
    Cert (MVM.compile (.tl d)) a (Function.update a (tR d) (a (tR d) - 1))
      (2 * (M + 1) + 3) := by
  let e := mkE (f1 (tR d)) (f1_inj _)
  have h := (Cert.ofVB (XProg.VB.prim (.tail (0 : Fin 1))
    (fun j ↦ hM (e j)))).frame e
  change Cert (.frame e (.prog (tl 0))) a
    (embedF e a (Function.update (a ∘ e) 0 (a (e 0) - 1))) _ at h
  rw [embedF_update_bound] at h
  exact h

end AdvancedEncryption.ExpLUT.Prog.KeyTime
