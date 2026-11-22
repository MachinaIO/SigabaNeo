import SigabaNeo.Lib.Machines.Prog.SampleTime

/-!
# Per-tape bounds of program phases

`Ph X βi T βo`: from per-tape bounds below `βi`, `X` takes at most `T` steps (`timeBoundT`) and
leaves its tapes below `βo` (`lenBoundT`). Phases compose (`Ph.seq`); primitives, `natP` and frames
give phases with explicit output bounds.
-/

namespace SigabaNeo.Tape

namespace XProg

variable {k : ℕ}

/-- **A phase**: from bounds below `βi`, at most `T` steps, bounds below `βo` afterwards. -/
def Ph (X : XProg k) (βi : Fin k → ℕ) (T : ℕ) (βo : Fin k → ℕ) : Prop :=
  ∀ ℓ ≤ βi, timeBoundT X ℓ ≤ T ∧ lenBoundT X ℓ ≤ βo

theorem Ph.mono {X : XProg k} {βi βi' βo βo' : Fin k → ℕ} {T T' : ℕ} (h : Ph X βi T βo)
    (hi : βi' ≤ βi) (hT : T ≤ T') (ho : βo ≤ βo') : Ph X βi' T' βo' := fun ℓ hℓ =>
  ⟨(h ℓ (hℓ.trans hi)).1.trans hT, (h ℓ (hℓ.trans hi)).2.trans ho⟩

theorem Ph.seq {X Y : XProg k} {β₁ β₂ β₃ : Fin k → ℕ} {T U : ℕ} (hX : Ph X β₁ T β₂)
    (hY : Ph Y β₂ U β₃) : Ph (.seq X Y) β₁ (T + U) β₃ := fun ℓ hℓ =>
  ⟨Nat.add_le_add (hX ℓ hℓ).1 (hY _ (hX ℓ hℓ).2).1, (hY _ (hX ℓ hℓ).2).2⟩

/-- A primitive. -/
theorem ph_prim (p : Prim k) (β : Fin k → ℕ) :
    Ph (.prog (.prim p)) β (2 * (supB β + 1) + 3) (p.lenT β) := fun ℓ hℓ => by
  refine ⟨?_, p.lenT_mono hℓ⟩
  rw [timeBoundT_prim]
  have := supB_mono hℓ
  have := pad_le p
  omega

/-- **`natP`**: the template `n` on `t`, its counter `c` below `max (β c) n`. -/
theorem ph_natP {t c : Fin k} (hct : c ≠ t) (n : ℕ) (β : Fin k → ℕ) :
    Ph (natP t c n) β ((2 * n + 1) * (4 * max (supB β) n + 12)) (natB t c n β) := fun ℓ hℓ => by
  obtain ⟨h1, h2⟩ := natP_bounds hct n ℓ (max (supB β) n)
    (fun i => ((hℓ i).trans (le_supB β i)).trans (le_max_left _ _)) (le_max_right _ _)
  refine ⟨h2, fun i => (h1 i).trans ?_⟩
  simp only [natB]
  split_ifs
  · exact le_rfl
  · exact max_le_max (hℓ c) le_rfl
  · exact hℓ i

/-- **A frame**, from a phase of its body on its own tapes. -/
theorem ph_frame {m : ℕ} (e : Fin m ↪ Fin k) {p : XProg m} {β : Fin k → ℕ} {T : ℕ}
    {βo : Fin m → ℕ} (h : Ph p (fun j => β (e j)) T βo) :
    Ph (.frame e p) β T (embedF e β βo) := fun ℓ hℓ => by
  have h' := h (fun j => ℓ (e j)) (fun j => hℓ (e j))
  exact ⟨h'.1, embedF_mono e hℓ h'.2⟩

/-- A uniform bound inside a phase. -/
theorem ph_of_ub {X : XProg k} {β : Fin k → ℕ} {M T M' : ℕ} (hM : ∀ i, β i ≤ M)
    (h : ∀ ℓ : Fin k → ℕ, (∀ i, ℓ i ≤ M) → timeBoundT X ℓ ≤ T ∧ ∀ i, lenBoundT X ℓ i ≤ M') :
    Ph X β T (fun _ => M') := fun ℓ hℓ =>
  ⟨(h ℓ fun i => (hℓ i).trans (hM i)).1, (h ℓ fun i => (hℓ i).trans (hM i)).2⟩

end XProg

end SigabaNeo.Tape
