import PE.Impl.RingBTVW.Prog.WfB2Time
import SigabaNeo.Lib.Machines.Prog.AbsBound

/-!
# Tools for the tight clock of `KeyGen`

* `ph_absRun`, `ph_frame_absRun`: a plain (framed) program with an evaluated abstract run
  (`Sym.absRun … = some (σ', w)`, checked by `decide +kernel`) is a phase: from per-tape bounds
  below `bnd ρ σ` and the top `top ρ`, at most `(2 top + 3) · w` steps, bounds below `bnd ρ σ'`.
  Every loop is charged its own counter, not a uniform bound.
* `tmplB_of_not_mem`, `tmplB_key`: the bounds after the templates `tmplP c l` are those of the
  templates on their tapes, the earlier ones elsewhere.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-- The bound after an abstract run, capped by the top (a program of the fragment never lengthens
a word). -/
def capB {k : ℕ} (ρ : List ℕ) (σ : Sym.Asg) : Fin k → ℕ := fun t => min (Sym.bnd ρ σ t) (Sym.top ρ)

theorem capB_le_top {k : ℕ} (ρ : List ℕ) (σ : Sym.Asg) (t : Fin k) : capB ρ σ t ≤ Sym.top ρ :=
  min_le_right _ _

theorem capB_le_bnd {k : ℕ} (ρ : List ℕ) (σ : Sym.Asg) : (capB ρ σ : Fin k → ℕ) ≤ Sym.bnd ρ σ :=
  fun _ => min_le_left _ _

/-- **A plain program with an evaluated abstract run** is a phase. -/
theorem ph_absRun {k fuel : ℕ} {p : Prog k} {σ σ' : Sym.Asg} {w : Sym.Poly}
    (h : Sym.absRun fuel p σ = some (σ', w)) (ρ : List ℕ) {β : Fin k → ℕ}
    (hin : β ≤ Sym.bnd ρ σ) (htop : ∀ t, β t ≤ Sym.top ρ) :
    Ph (.prog p) β ((2 * Sym.top ρ + 3) * Sym.pEval ρ w) (capB ρ σ') := fun ℓ hℓ => by
  have hM : ∀ t, ℓ t ≤ Sym.top ρ := fun t => (hℓ t).trans (htop t)
  obtain ⟨h1, h2⟩ := (Sym.absRun_sound fuel p h).bounds ρ (hℓ.trans hin) hM
  exact ⟨h2, fun t => le_min (h1 t)
    (Sym.lenBoundT_le_const p (Sym.noGrow_of_absRun fuel p h) hM t)⟩

/-- **A framed program with an evaluated abstract run**: only the framed tapes count. -/
theorem ph_frame_absRun {m k fuel : ℕ} {p : Prog m} {σ σ' : Sym.Asg} {w : Sym.Poly}
    (h : Sym.absRun fuel p σ = some (σ', w)) (ρ : List ℕ) (e : Fin m ↪ Fin k) {β : Fin k → ℕ}
    (hin : (fun j => β (e j)) ≤ Sym.bnd ρ σ) (htop : ∀ j, β (e j) ≤ Sym.top ρ) :
    Ph (.frame e (.prog p)) β ((2 * Sym.top ρ + 3) * Sym.pEval ρ w) (embedF e β (capB ρ σ')) :=
  ph_frame e (ph_absRun h ρ hin htop)

/-- Phases of nested sequences may be regrouped. -/
theorem ph_seq_assoc {k : ℕ} {X Y Z : XProg k} {β βo : Fin k → ℕ} {T : ℕ}
    (h : Ph (.seq (.seq X Y) Z) β T βo) : Ph (.seq X (.seq Y Z)) β T βo := fun ℓ hℓ => by
  have := h ℓ hℓ
  refine ⟨?_, this.2⟩
  have e : timeBoundT (.seq X (.seq Y Z)) ℓ = timeBoundT (.seq (.seq X Y) Z) ℓ := by
    simp only [timeBoundT_seq]; show _ = _ + _ + _; rw [Nat.add_assoc]; rfl
  rw [e]; exact this.1

/-! ### The bounds after templates -/

section Tmpl

variable {n : ℕ}

theorem tmplB_of_not_mem (c : Fin n) : ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ) (t : Fin n),
    t ≠ c → t ∉ l.map Prod.fst → tmplB c l β t = β t
  | [], _, _, _, _ => rfl
  | x :: l, β, t, hc, hm => by
    simp only [List.map_cons, List.mem_cons, not_or] at hm
    rw [tmplB, tmplB_of_not_mem c l _ t hc hm.2]
    simp [natB, hm.1, hc]

/-- On the tape of a template (keys distinct, none the counter): its value. -/
theorem tmplB_key (c : Fin n) : ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ), (l.map Prod.fst).Nodup →
    (∀ x ∈ l, x.1 ≠ c) → ∀ x ∈ l, tmplB c l β x.1 = x.2
  | [], _, _, _, x, hx => absurd hx (by simp)
  | y :: l, β, hn, hc, x, hx => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rw [tmplB]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [tmplB_of_not_mem c l _ _ (hc _ (by simp)) (fun h => hn.1 (by
        obtain ⟨z, hz, e⟩ := List.mem_map.mp h; exact ⟨z, hz, e⟩))]
      simp [natB]
    · exact tmplB_key c l _ hn.2 (fun z hz => hc z (by simp [hz])) x hx'

/-- On the counter: at most the larger of its bound and the templates. -/
theorem tmplB_counter_le (c : Fin n) {M : ℕ} : ∀ (l : List (Fin n × ℕ)) (β : Fin n → ℕ),
    β c ≤ M → (∀ x ∈ l, x.2 ≤ M) → (∀ x ∈ l, x.1 ≠ c) → tmplB c l β c ≤ M
  | [], _, h, _, _ => h
  | x :: l, β, h, hl, hc => by
    rw [tmplB]
    refine tmplB_counter_le c l _ ?_ (fun y hy => hl y (by simp [hy]))
      (fun y hy => hc y (by simp [hy]))
    have hne : c ≠ x.1 := Ne.symm (hc x (by simp))
    simpa [natB, hne] using And.intro h (hl x (by simp))

end Tmpl

end AdvancedEncryption.RingBTVW.Prog
