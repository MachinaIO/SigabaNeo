import PE.Impl.DualUse.Prog.KeyPTime

/-!
# The time of the key component with a per-tape bound of the `W_f` block

`time_keyP2`: `time_keyP` with the `W_f` block bounded at the per-tape bounds of its call
(`io2 Lsd (frontL c.L W) 0`: the SimData word, the front end's output) instead of a uniform bound
of all its tapes. A block whose cost depends on blank tapes staying blank (loop counters) is
bounded this way (`WfB2Conf.time_wfB2_conf`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  Matrix AdvancedEncryption.RingBTVW AdvancedEncryption.DualUse.Algo
  Cslib Cslib.Probability SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord
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

/-- **`time_keyP` with a per-tape bound of the `W_f` block** at its call. -/
theorem time_keyP2 {sdP : XProg 82} {Ls Ts Lsd : ℕ}
    (hsT : timeBoundT sdP (io2 (R := 80) Ls 0 0) ≤ Ts)
    (hsL : lenBoundT sdP (io2 (R := 80) Ls 0 0) ≤ io2 Lsd 0 0)
    {wfB : XProg 256} {Twf Gwf : ℕ} (W : ℕ)
    (hwT : timeBoundT wfB (io2 (R := 254) Lsd (frontL c.L W) 0) ≤ Twf)
    (hwL : ∀ t, lenBoundT wfB (io2 (R := 254) Lsd (frontL c.L W) 0) t ≤ Gwf)
    (cf : KeyCfg) (K₀ : ℕ) :
    timeBoundT (keyP hk c sdP wfB W cf) (io2 (R := 254) Ls K₀ 0) ≤
        Ts + frontT c.L W K₀ + branchT hk c (fun _ => Twf) (fun _ => Gwf) cf (keyM hk c Lsd W cf) +
          clrT (branchL hk c (fun _ => Gwf) cf (keyM hk c Lsd W cf)) ∧
      lenBoundT (keyP hk c sdP wfB W cf) (io2 (R := 254) Ls K₀ 0) ≤
        io2 (branchL hk c (fun _ => Gwf) cf (keyM hk c Lsd W cf)) 0 0 := by
  set M := keyM hk c Lsd W cf with hMdef
  -- the SimData block
  have e1 : (fun j => io2 (R := 254) Ls K₀ 0 (eSd j)) = io2 (R := 80) Ls 0 0 := io2_eSd Ls K₀ 0
  have l1 : lenBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) ≤ io2 (R := 254) Lsd K₀ 0 := by
    show embedF eSd _ (lenBoundT sdP fun j => io2 (R := 254) Ls K₀ 0 (eSd j)) ≤ _
    rw [e1, ← embedF_eSd Ls K₀ Lsd 0]
    exact embedF_mono _ le_rfl hsL
  have t1 : timeBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) ≤ Ts := by
    rw [timeBoundT_frame, e1]; exact hsT
  -- the front end
  set ℓ1 := lenBoundT (frame eSd sdP) (io2 (R := 254) Ls K₀ 0) with hℓ1
  have v1 : (fun j => ℓ1 (eFr j)) ≤ io2 (R := 6) K₀ 0 0 := by
    rw [← io2_eFr Lsd K₀ 0]; exact fun j => l1 (eFr j)
  have t2 : timeBoundT (frame eFr (frontP c.L W)) ℓ1 ≤ frontT c.L W K₀ := by
    rw [timeBoundT_frame]
    exact (timeBoundT_mono _ v1).trans (timeBoundT_frontP c.L W K₀)
  have l2 : lenBoundT (frame eFr (frontP c.L W)) ℓ1 ≤ io2 (R := 254) Lsd (frontL c.L W) 0 := by
    show embedF eFr ℓ1 (lenBoundT (frontP c.L W) fun j => ℓ1 (eFr j)) ≤ _
    rw [← embedF_eFr Lsd K₀ (frontL c.L W) 0]
    exact embedF_mono _ l1 ((lenBoundT_mono _ v1).trans (lenBoundT_frontP c.L W K₀))
  -- the branches, from the uniform bound `M`
  set ℓ2 := lenBoundT (frame eFr (frontP c.L W)) ℓ1 with hℓ2
  have hℓ2M : ∀ t, ℓ2 t ≤ M := fun t => (l2 t).trans (by
    simp only [io2, hMdef, keyM]; split_ifs <;> omega)
  have ub := ub_branchB2 hk c hwT hwL cf (M := M) (le_max_right _ _) ℓ2 hℓ2M l2
  have hc := ub_clearL (branchL hk c (fun _ => Gwf) cf M) clrAll _ ub.2
  have hlen : clrAll.length * (2 * (branchL hk c (fun _ => Gwf) cf M + 1) + 3) ≤
      256 * (2 * (branchL hk c (fun _ => Gwf) cf M + 1) + 3) := Nat.mul_le_mul_right _ length_clrAll_le
  refine ⟨?_, fun t => ?_⟩
  · show timeBoundT (frame eSd sdP) _ + (timeBoundT (frame eFr (frontP c.L W)) ℓ1 +
      (timeBoundT (branchB hk c wfB cf) ℓ2 +
        timeBoundT (clearL clrAll) (lenBoundT (branchB hk c wfB cf) ℓ2))) ≤ _
    have := ub.1
    have := hc.1
    simp only [clrT]
    omega
  · show lenBoundT (clearL clrAll) (lenBoundT (branchB hk c wfB cf) ℓ2) t ≤ _
    refine (lenBoundT_clearL_le clrAll _ t).trans ?_
    simp only [mem_clrAll]
    by_cases h : t = 0
    · subst h; simp [io2, ub.2 0]
    · have : t.val ≠ 0 := fun e => h (Fin.ext e)
      simp [h, io2, this]


end AdvancedEncryption.DualUse.Prog
