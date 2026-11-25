import PE.Impl.RingBTVW.Prog.KeyPTime

/-!
# The time of the key component with a per-tape bound of the `W_f` block

`time_keyP2`: `time_keyP` with the `W_f` block bounded at the per-tape bounds of its call
(`io2 Lsd (frontL c.L W) 0`: the SimData word, the front end's output) instead of a uniform bound
of all its tapes. A block whose cost depends on blank tapes staying blank (loop counters) is
bounded this way (`WfB2Conf.time_wfB2_conf`).
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  Matrix AdvancedEncryption.RingBTVW.Fresh AdvancedEncryption.RingBTVW.Algo
  Cslib Cslib.Probability SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord
open scoped SigabaNeo.Tape.Prog

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

variable (hk c) in
/-- **The window branch** with the `W_f` block bounded at the per-tape bounds `β` of its call. -/
theorem ub_winB2 {wfB : XProg 256} {β : Fin 256 → ℕ} {Twf Gwf : ℕ}
    (hwT : timeBoundT wfB β ≤ Twf) (hwL : ∀ t, lenBoundT wfB β t ≤ Gwf) (cf : KeyCfg) {M : ℕ}
    (hM : tmplMax (keyTmpl hk c cf) ≤ M) (ℓ : Fin 256 → ℕ) (hℓ : ∀ i, ℓ i ≤ M) (hβ : ℓ ≤ β) :
    timeBoundT (winB hk c wfB cf) ℓ ≤ winT hk c (fun _ => Twf) (fun _ => Gwf) cf M ∧
      ∀ i, lenBoundT (winB hk c wfB cf) ℓ i ≤ 2 * winB3 hk c (fun _ => Gwf) cf M := by
  have hT : ∀ x ∈ keyTmpl hk c cf, x.2 ≤ winB3 hk c (fun _ => Gwf) cf M := fun x hx =>
    (le_tmplMax _ x hx).trans (hM.trans (by simp only [winB3, winB1]; omega))
  have uR := (ub_prefP (lenPK hk c) 0 1 100 101 (max Gwf M)).seq <| (ub_putW 4 cf.sW _).seq <|
    (ub_putW 5 (powW K (cf.B - 1)) _).seq <|
    (ub_tmplP 120 (keyTmpl hk c cf) (winB3 hk c (fun _ => Gwf) cf M) hT
      (keyTmpl_ne (Or.inr (Or.inr rfl)))).seq <|
    (ub_keyTry _).seq (ub_clearL _ keyClr)
  set ℓ1 := lenBoundT (prog (.prim (.tail (1 : Fin 256)))) ℓ with hℓ1
  have h1β : ℓ1 ≤ β := fun t => by
    simp only [hℓ1, lenBoundT_prim, Prim.lenT, Function.update_apply]
    split_ifs with h
    · subst h; exact (Nat.sub_le _ _).trans (hβ _)
    · exact hβ t
  have t0 := (ub_prim (Prim.tail (1 : Fin 256)) M ℓ hℓ).1
  have tw : timeBoundT wfB ℓ1 ≤ Twf := (timeBoundT_mono wfB h1β).trans hwT
  have lw : ∀ i, lenBoundT wfB ℓ1 i ≤ max Gwf M := fun i =>
    ((lenBoundT_mono wfB h1β i).trans (hwL i)).trans (le_max_left _ _)
  obtain ⟨tR, lR⟩ := uR (lenBoundT wfB ℓ1) lw
  refine ⟨?_, fun i => ?_⟩
  · show timeBoundT (prog (.prim (.tail (1 : Fin 256)))) ℓ + (timeBoundT wfB ℓ1 + _) ≤ _
    simp only [winT, winB1] at tR ⊢
    rw [hℓ1] at tR tw ⊢
    omega
  · exact lR i

variable (hk c) in
theorem ub_branchB2 {wfB : XProg 256} {β : Fin 256 → ℕ} {Twf Gwf : ℕ}
    (hwT : timeBoundT wfB β ≤ Twf) (hwL : ∀ t, lenBoundT wfB β t ≤ Gwf) (cf : KeyCfg) {M : ℕ}
    (hM : tmplMax (keyTmpl hk c cf) ≤ M) (ℓ : Fin 256 → ℕ) (hℓ : ∀ i, ℓ i ≤ M) (hβ : ℓ ≤ β) :
    timeBoundT (branchB hk c wfB cf) ℓ ≤ branchT hk c (fun _ => Twf) (fun _ => Gwf) cf M ∧
      ∀ i, lenBoundT (branchB hk c wfB cf) ℓ i ≤ branchL hk c (fun _ => Gwf) cf M := by
  obtain ⟨a1, a2⟩ := ub_winB2 hk c hwT hwL cf hM ℓ hℓ hβ
  obtain ⟨b1, b2⟩ := ub_ifBlank (i := 1) (ub_longB M) (ub_dumB hk c M) ℓ hℓ
  refine ⟨?_, fun i => ?_⟩
  · show max _ _ + 1 ≤ _
    simp only [branchT]
    omega
  · show max _ _ ≤ _
    simp only [branchL]
    exact max_le_max (a2 i) (b2 i)

end AdvancedEncryption.RingBTVW.Prog
