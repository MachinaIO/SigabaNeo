import PE.Impl.DualUse.Prog.CostTools
import PE.Impl.DualUse.Prog.WfB2Time
import PE.Impl.DualUse.Prog.KeyGenCost

/-!
# Per-tape phases for the tight clock of `Dec`

Phases (`XProg.Ph`) keeping exact per-tape bounds where the uniform ones (`UB`) lose them:

* `ph_seqP`: sequencing inside a plain program;
* `ph_mapSound`: a placed subprogram `map u p` with a sound summary (`Sym.Sound`): every primitive
  charged the longest tape (`2 · top + 3`), as many sweeps as the summary counts;
* `ph_tailsX`: `tailsP i n` lowers only tape `i`;
* `ph_prefP'`: `prefP P` appends exactly `P` bits to its target;
* `ph_skipLoopP'`: the reading loop charged `|tn|` rounds, each moving at most `R` bits.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

variable {k : ℕ}

/-- Sequencing inside a plain program. -/
theorem ph_seqP {p q : SigabaNeo.Tape.Prog k} {β₁ β₂ β₃ : Fin k → ℕ} {T U : ℕ}
    (hp : Ph (.prog p) β₁ T β₂) (hq : Ph (.prog q) β₂ U β₃) :
    Ph (.prog (SigabaNeo.Tape.Prog.seq p q)) β₁ (T + U) β₃ := fun ℓ hℓ =>
  ⟨Nat.add_le_add (hp ℓ hℓ).1 (hq _ (hp ℓ hℓ).2).1, (hq _ (hp ℓ hℓ).2).2⟩

/-- **A placed subprogram with a sound summary.** -/
theorem ph_mapSound {m : ℕ} {u : Fin m → Fin k} (hu : Function.Injective u)
    {p : SigabaNeo.Tape.Prog m} {σ σ' : Sym.Asg} {w : Sym.Poly} (hS : Sym.Sound p σ σ' w)
    (ρ : List ℕ) (β βo : Fin k → ℕ) (hin : ∀ j, β (u j) ≤ Sym.bnd ρ σ j)
    (htop : ∀ t, β t ≤ Sym.top ρ) (hout : ∀ j, Sym.bnd ρ σ' j ≤ βo (u j))
    (hrest : ∀ t, (∀ j, u j ≠ t) → β t ≤ βo t) :
    Ph (.prog (SigabaNeo.Tape.Prog.map u p)) β ((2 * Sym.top ρ + 3) * Sym.pEval ρ w) βo := by
  intro ℓ hℓ
  obtain ⟨a, b⟩ := hS ρ k u hu ℓ (fun j => (hℓ _).trans (hin j)) (fun t => (hℓ t).trans (htop t))
  refine ⟨b, fun t => ?_⟩
  show SigabaNeo.Tape.Prog.lenBoundT _ ℓ t ≤ _
  by_cases ht : ∃ j, u j = t
  · obtain ⟨j, rfl⟩ := ht
    exact (a j).trans (hout j)
  · push Not at ht
    rw [SigabaNeo.Tape.Prog.lenBoundT_of_preserves t _
      (SigabaNeo.Tape.Prog.preserves_map_of_not_mem ht p) ℓ]
    exact (hℓ t).trans (hrest t ht)

/-! ### Tails -/

theorem lenBoundT_tailsP (i : Fin k) : ∀ (n : ℕ) (ℓ : Fin k → ℕ),
    SigabaNeo.Tape.Prog.lenBoundT (SigabaNeo.Tape.Prog.tailsP i n) ℓ =
      Function.update ℓ i (ℓ i - n)
  | 0, ℓ => by
    funext t
    simp [SigabaNeo.Tape.Prog.tailsP, SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT]
  | n + 1, ℓ => by
    rw [SigabaNeo.Tape.Prog.tailsP, SigabaNeo.Tape.Prog.lenBoundT, lenBoundT_tailsP i n]
    funext t
    by_cases h : t = i
    · subst h; simp [SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT]; omega
    · simp [SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT, Function.update_apply, h]

theorem ph_tailsX (i : Fin k) (n : ℕ) (β : Fin k → ℕ) :
    Ph (.prog (SigabaNeo.Tape.Prog.tailsP i n)) β ((n + 1) * (2 * (supB β + 1) + 3))
      (Function.update β i (β i - n)) := fun ℓ hℓ => by
  refine ⟨(SigabaNeo.Tape.Prog.ubp_tailsP i n (supB β) ℓ
    (fun t => (hℓ t).trans (le_supB β t))).1, fun t => ?_⟩
  show SigabaNeo.Tape.Prog.lenBoundT _ ℓ t ≤ _
  rw [lenBoundT_tailsP]
  simp only [Function.update_apply]
  split_ifs with h
  · subst h; exact Nat.sub_le_sub_right (hℓ _) n
  · exact hℓ t

/-! ### Prefixes -/

theorem lenBoundT_moveFront_dst {src dst tmp : Fin k} (h1 : dst ≠ src) (h2 : dst ≠ tmp) :
    ∀ (n : ℕ) (ℓ : Fin k → ℕ),
      SigabaNeo.Tape.Prog.lenBoundT (SigabaNeo.Tape.Prog.moveFront n src dst tmp) ℓ dst = ℓ dst + n
  | 0, ℓ => by
    simp [SigabaNeo.Tape.Prog.moveFront, SigabaNeo.Tape.Prog.iter, SigabaNeo.Tape.Prog.lenBoundT,
      Prim.lenT]
  | n + 1, ℓ => by
    have := lenBoundT_moveFront_dst h1 h2 n
    simp only [SigabaNeo.Tape.Prog.moveFront] at this ⊢
    rw [SigabaNeo.Tape.Prog.iter, SigabaNeo.Tape.Prog.lenBoundT, this]
    simp [SigabaNeo.Tape.Prog.stepF, SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT,
      Function.update_apply, h1, h2]
    omega

theorem lenBoundT_prefP_dst (P : ℕ) {src dst a b : Fin k} (h1 : a ≠ dst) (h2 : b ≠ dst)
    (ℓ : Fin k → ℕ) : XProg.lenBoundT (prefP P src dst a b) ℓ dst = ℓ dst + P := by
  simp only [prefP, XProg.lenBoundT]
  show SigabaNeo.Tape.Prog.lenBoundT (.prim (.clear a)) _ dst = _
  simp only [SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT, Function.update_apply, if_neg (Ne.symm h1)]
  rw [lenBoundT_moveFront_dst (Ne.symm h1) (Ne.symm h2)]
  simp [SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT, Function.update_apply, Ne.symm h1]

/-- **A prefix**: the target grows by exactly `P`, the two scratch tapes stay below
`supB β + 1 + P`, the others keep their bounds. -/
theorem ph_prefP' (P : ℕ) {src dst a b : Fin k} (h1 : a ≠ dst) (h2 : b ≠ dst) (β : Fin k → ℕ) :
    Ph (prefP P src dst a b) β (prefT P (supB β))
      (fun t => if t = dst then β dst + P else if t = a ∨ t = b then supB β + 1 + P else β t) := by
  intro ℓ hℓ
  have hu := ub_prefP P src dst a b (supB β) ℓ (fun t => (hℓ t).trans (le_supB β t))
  refine ⟨hu.1, fun t => ?_⟩
  dsimp only
  split_ifs with hd hab
  · subst hd
    rw [lenBoundT_prefP_dst P h1 h2]
    exact Nat.add_le_add_right (hℓ t) P
  · exact hu.2 t
  · push Not at hab
    rw [lenBoundT_of_preserves _ t (preserves_prefP (Ne.symm hab.1) (Ne.symm hd)
      (Ne.symm hab.2)) ℓ]
    exact hℓ t

/-! ### The reading loop, per tape -/

/-- The per-round bound of `skipLoopP`. -/
def skB (β : Fin k → ℕ) (out c c' : Fin k) (O n R j : ℕ) : Fin k → ℕ :=
  fun t => if t = out then O + j * R else if t = c then n else if t = c' then max (β c') R else β t

/-- The time of `skipLoopP` (`X` bounds every tape during the loop). -/
def skT (S X n R : ℕ) : ℕ :=
  (2 * (S + 1) + 3) + (n * (2 * X + 3 + 2 * ((R + 1) * (6 * (X + R) + 20)) + 1) + 2)

/-- **The reading loop, per tape**: `|tn| ≤ n` rounds, each moving at most `R` bits to `out`; the
other tapes stay below `M` and keep their bounds except the counters. -/
theorem ph_skipLoopP' {out src c c' tn tz tr : Fin k} (hd : [out, src, c, c', tn, tz, tr].Nodup)
    {M O n R : ℕ} (β : Fin k → ℕ) (hM : ∀ t, t ≠ out → β t ≤ M) (hO : β out ≤ O)
    (hn : β tn ≤ n) (hz : β tz ≤ R) (hr : β tr ≤ R) (hnM : n ≤ M) (hRM : R ≤ M) :
    Ph (skipLoopP out src c c' tn tz tr) β (skT (supB β) (M + O + n * R) n R)
      (skB β out c c' O n R n) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h05, h06⟩, ⟨h12, h13, h14, h15, h16⟩,
    ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56, -⟩ := hd
  set X := M + O + n * R with hX
  set B := skB β out c c' O n R with hB
  have hc := ph_prim (.copy c tn) β
  have e1 : (Prim.copy c tn).lenT β = Function.update β c (β tn) := rfl
  have hc1 : (Prim.copy c tn).lenT β c = β tn := by rw [e1, Function.update_self]
  have Bz : ∀ j, B j tz = β tz := fun j => by
    simp [hB, skB, Ne.symm h05, Ne.symm h25, Ne.symm h35]
  have Br : ∀ j, B j tr = β tr := fun j => by
    simp [hB, skB, Ne.symm h06, Ne.symm h26, Ne.symm h36]
  have hBX : ∀ j ≤ n, ∀ t, B j t ≤ X := fun j hj t => by
    simp only [hB, skB]
    split_ifs with h1 h2 h3
    · have := Nat.mul_le_mul_right R hj; omega
    · omega
    · subst h3; exact max_le (by have := hM _ h1; omega) (by omega)
    · have := hM t h1; omega
  have hstep : ∀ j < (Prim.copy c tn).lenT β c,
      Ph (XProg.seq (XProg.dropP src c' tz) (XProg.moveP out src c' tr)) (B j)
        (2 * ((R + 1) * (6 * (X + R) + 20))) (B (j + 1)) := by
    intro j hj
    rw [hc1] at hj
    have p1 := ph_dropP h13 h35 (B j)
    have p2 := ph_moveP h01 h03 h13 h36 (Function.update (B j) c' (B j tz))
    have hb1 : ∀ t, Function.update (B j) c' (B j tz) t ≤ X := fun t => by
      simp only [Function.update_apply]; split_ifs
      · exact hBX j (by omega) tz
      · exact hBX j (by omega) t
    refine (p1.seq p2).mono le_rfl ?_ ?_
    · have m1 : mvT (B j) tz ≤ (R + 1) * (6 * (X + R) + 20) := by
        unfold mvT
        have := supB_le_of (hBX j (by omega)); rw [Bz]
        exact Nat.mul_le_mul (by omega) (by omega)
      have m2 : mvT (Function.update (B j) c' (B j tz)) tr ≤ (R + 1) * (6 * (X + R) + 20) := by
        unfold mvT
        have := supB_le_of hb1
        rw [Function.update_of_ne (Ne.symm h36), Br]
        exact Nat.mul_le_mul (by omega) (by omega)
      omega
    · intro t
      have e := Nat.succ_mul j R
      have hjn : j + 1 ≤ n := by omega
      have := Nat.mul_le_mul_right R hjn
      clear_value B
      subst hB
      simp only [mvB, skB, Function.update_apply]
      split_ifs <;> simp_all <;> omega
  have hl := ph_loop_iter c (β := (Prim.copy c tn).lenT β) B (B n) _
    (2 * X + 3 + 2 * ((R + 1) * (6 * (X + R) + 20)))
    (fun t => by
      rw [e1]; clear_value B; subst hB; simp only [skB, Function.update_apply]
      split_ifs <;> simp_all <;> omega)
    hstep
    (fun j hj t => by
      rw [hc1] at hj
      simp only [hB, skB]; split_ifs
      · have := Nat.mul_le_mul_right R (show j ≤ n by omega); omega
      all_goals omega)
    (fun j hj => by
      rw [hc1] at hj
      have := supB_le_of (hBX j (by omega)); omega)
  refine (hc.seq hl).mono le_rfl ?_ le_rfl
  rw [hc1, skT]
  have := Nat.mul_le_mul_right (2 * X + 3 + 2 * ((R + 1) * (6 * (X + R) + 20)) + 1) hn
  omega

theorem tmplTT_le2 {n : ℕ} (c : Fin n) (M T : ℕ) (hTM : T ≤ M) :
    ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ), (∀ i, β i ≤ M) → (∀ x ∈ l, x.2 ≤ T) →
      tmplTT c l β ≤ (l.length + 1) * ((2 * T + 1) * (4 * M + 12))
  | [], β, hβ, _ => by
    simp only [tmplTT, List.length_nil, Nat.zero_add, Nat.one_mul]
    have := supB_le_of hβ
    nlinarith
  | x :: l, β, hβ, hl => by
    simp only [tmplTT, List.length_cons]
    have hx := hl x (by simp)
    have ih := tmplTT_le2 c M T hTM l (natB x.1 c x.2 β) (natB_leT x.1 c x.2 hβ (hx.trans hTM))
      (fun y hy => hl y (by simp [hy]))
    have hs : max (supB β) x.2 ≤ M := max_le (supB_le_of hβ) (hx.trans hTM)
    have : (2 * x.2 + 1) * (4 * max (supB β) x.2 + 12) ≤ (2 * T + 1) * (4 * M + 12) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith

end AdvancedEncryption.DualUse.Prog
