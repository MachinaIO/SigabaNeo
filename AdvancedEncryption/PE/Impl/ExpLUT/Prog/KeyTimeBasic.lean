import PE.Impl.ExpLUT.Prog.KeySizeConf

/-! Compositional runtime certificates for the actual 105-tape KeyGen compiler.
The loop rule allows growing output queues; a fixed length invariant would not suffice.
-/
namespace AdvancedEncryption.ExpLUT.Prog
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM
open SigabaNeo.Tape.Prog

namespace KeyTime

/-- Length and time bounds for an actual framed program. -/
structure Cert {k : ℕ} (p : XProg k) (input output : Fin k → ℕ) (T : ℕ) : Prop where
  len : XProg.lenBoundT p input ≤ output
  time : XProg.timeBoundT p input ≤ T

theorem Cert.mono {k : ℕ} {p : XProg k} {a b a' b' : Fin k → ℕ} {T T' : ℕ}
    (h : Cert p a b T) (ha : a' ≤ a) (hb : b ≤ b') (ht : T ≤ T') : Cert p a' b' T' :=
  ⟨((XProg.lenBoundT_mono p) ha).trans (h.len.trans hb),
    ((XProg.timeBoundT_mono p) ha).trans (h.time.trans ht)⟩

theorem Cert.seq {k : ℕ} {p q : XProg k} {a b c : Fin k → ℕ} {T U : ℕ}
    (hp : Cert p a b T) (hq : Cert q b c U) : Cert (.seq p q) a c (T + U) := by
  refine ⟨((XProg.lenBoundT_mono q) hp.len).trans hq.len, ?_⟩
  exact Nat.add_le_add hp.time (((XProg.timeBoundT_mono q) hp.len).trans hq.time)

theorem Cert.ifBit {k : ℕ} (i : Fin k) {p q : XProg k} {a b : Fin k → ℕ} {T U : ℕ}
    (hp : Cert p a b T) (hq : Cert q a b U) : Cert (.ifBit i p q) a b (max T U + 1) :=
  ⟨fun t ↦ max_le (hp.len t) (hq.len t), Nat.add_le_add_right (max_le_max hp.time hq.time) 1⟩

/-- A loop whose output bounds may grow with its iteration index. -/
theorem loop_family {k : ℕ} (i : Fin k) (body : XProg k) (γ : ℕ → Fin k → ℕ)
    (R T : ℕ) (a : Fin k → ℕ) (h0 : a ≤ γ 0) (hc : a i ≤ R)
    (hstep : ∀ j < R, XProg.lenBoundT body (tailB i (γ j)) ≤ γ (j + 1))
    (htime : ∀ j < R, 2 * supB (γ j) + 3 + XProg.timeBoundT body (tailB i (γ j)) ≤ T)
    (hmono : ∀ j ≤ R, γ j ≤ γ R) : Cert (.loop i body) a (γ R) (R * (T + 1) + 2) := by
  have hit : ∀ j, j ≤ R → (XProg.loopStepT i body)^[j] a ≤ γ j := by
    intro j
    induction j with
    | zero => intro _; simpa using h0
    | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply']
      exact (XProg.lenBoundT_mono body (tailB_mono i (ih (by omega)))).trans (hstep j (by omega))
  refine ⟨?_, ?_⟩
  · exact iterSupT_le fun j hj ↦ (hit j (by omega)).trans (hmono j (by omega))
  · refine (XProg.timeBoundT_loop_le i body a (R := T) fun j hj ↦ ?_).trans ?_
    · have h1 := hit j (by omega)
      have h2 := supB_mono h1
      have h3 := XProg.timeBoundT_mono body (tailB_mono i h1)
      have h4 := htime j (by omega)
      show 2 * supB _ + 3 + XProg.timeBoundT body _ ≤ _
      omega
    · exact Nat.add_le_add_right (Nat.mul_le_mul_right (T + 1) hc) 2

/-- MVM repetition uses the compiled register's tape, with no alternate interpreter. -/
theorem rep_family (c : Fin 64) (body : Code) (γ : ℕ → Fin 105 → ℕ)
    (R T : ℕ) (a : Fin 105 → ℕ) (h0 : a ≤ γ 0) (hc : a (tR c) ≤ R)
    (hstep : ∀ j < R, Cert (compile body) (tailB (tR c) (γ j)) (γ (j + 1)) T)
    (M : ℕ) (hM : ∀ j < R, supB (γ j) ≤ M) (hmono : ∀ j ≤ R, γ j ≤ γ R) :
    Cert (compile (.rep c body)) a (γ R) (R * (2 * M + T + 4) + 2) := by
  have ht : ∀ j < R,
      2 * supB (γ j) + 3 + XProg.timeBoundT (compile body) (tailB (tR c) (γ j)) ≤
        2 * M + 3 + T := by
    intro j hj
    have hh := (hstep j hj).time
    have hm := hM j hj
    omega
  have h := loop_family (tR c) (compile body) γ R (2 * M + 3 + T) a h0 hc
      (fun j hj ↦ (hstep j hj).len) ht hmono
  have he : 2 * M + 3 + T + 1 = 2 * M + T + 4 := by omega
  rw [he] at h
  exact h

theorem Cert.frame {k m : ℕ} (e : Fin m ↪ Fin k) {p : XProg m}
    {a : Fin k → ℕ} {b : Fin m → ℕ} {T : ℕ} (h : Cert p (a ∘ e) b T) :
    Cert (.frame e p) a (embedF e a b) T :=
  ⟨embedF_mono e le_rfl h.len, h.time⟩

/-- Appending has an additive output-length bound, including its scratch tapes. -/
theorem appT_cert {k : ℕ} (o x u v : Fin k) (hou : o ≠ u) (hov : o ≠ v)
    (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v) (a : Fin k → ℕ) (M : ℕ)
    (hM : ∀ t, a t ≤ M) (hs : a o + a x ≤ M) :
    Cert (.prog (appT o x u v)) a
      (fun t ↦ if t = o then a o + a x else if t = u then a x else if t = v then 0 else a t)
      ((4 * a x + 6) * (2 * M + 5)) := by
  have h := appT_bounds hou hov huv hxu hxv a hM hs
  exact ⟨h.2, h.1⟩

/-- Exact MVM framing of a distinct-register append. -/
theorem compile_app_cert (d s : Fin 64) (hds : d ≠ s) (a : Fin 105 → ℕ) (M : ℕ)
    (hM : ∀ t, a t ≤ M) (hs : a (tR d) + a (tR s) ≤ M) :
    let e := mkE (fAp d s) (fAp_inj hds)
    let b := a ∘ e
    Cert (MVM.compile (.app d s)) a
      (embedF e a (fun t ↦ if t = 0 then b 0 + b 1 else if t = 2 then b 1
        else if t = 3 then 0 else b t))
      ((4 * a (tR s) + 6) * (2 * M + 5)) := by
  dsimp only
  rw [MVM.compile, dite_eq_right hds]
  apply Cert.frame
  exact appT_cert 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    _ M (fun t ↦ hM _) hs

/-- The self-append case used by binary counter initialization doubles the word length. -/
theorem compile_app_self_cert (d : Fin 64) (a : Fin 105 → ℕ) (M : ℕ)
    (hM : ∀ t, a t ≤ M) (hs : a (tR d) + a (tR d) ≤ M) :
    let e := mkE (fAp1 d) (fAp1_inj d)
    let b := a ∘ e
    Cert (MVM.compile (.app d d)) a
      (embedF e a (fun t ↦ if t = 0 then b 0 + b 0 else if t = 1 then b 0
        else if t = 2 then 0 else b t))
      ((4 * a (tR d) + 6) * (2 * M + 5)) := by
  dsimp only
  rw [MVM.compile, dite_eq_left rfl]
  apply Cert.frame
  exact appT_cert 0 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    _ M (fun t ↦ hM _) hs

end KeyTime
end AdvancedEncryption.ExpLUT.Prog
