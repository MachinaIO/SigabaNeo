import SigabaNeoStd.Machines.Prog.AbsBound
import SigabaNeoStd.Machines.Prog.SampleTime
import SigabaNeoStd.Machines.Prog.FrameSize

/-!
# Per-tape bound transformers

`VB p ℓin T ℓout`: from any per-tape bound below `ℓin`, the program `p` costs at most `T`
(`XProg.timeBoundT`) and ends below `ℓout` (`XProg.lenBoundT`). They compose (`VB.seq`, `VB.mono`,
`VB.frame`), and:

* `VB.prim`: a primitive, from bounds below `M`;
* `VB.natP`: building the counter `replicate n false` (`natB`);
* **`VB.checkMap`**: a relabelled deterministic program summarised by a checked certificate of the
  abstract interpreter (`Sym.check`): its cost is `(2 · top + 3) · w` and its tapes end below the
  claimed polynomials, the tapes outside its range unchanged. Loops are charged the lengths of
  their own counters, not a uniform bound.

`zv j M`: the vector `M` on the tapes `< j`, `0` on the others (blank scratch); `UBZ j p M T M'`
is `VB p (zv j M) T (zv j M')`, a uniform bound that keeps track of the blank scratch tapes
(`UBZ.seq`, `UBZ.mono`, `UBZ.frame`).
-/

namespace SigabaNeo.Tape

namespace XProg

variable {k : ℕ}

/-- **A per-tape bound transformer.** -/
def VB (p : XProg k) (ℓin : Fin k → ℕ) (T : ℕ) (ℓout : Fin k → ℕ) : Prop :=
  ∀ ℓ, ℓ ≤ ℓin → timeBoundT p ℓ ≤ T ∧ lenBoundT p ℓ ≤ ℓout

theorem VB.seq {p q : XProg k} {a b c : Fin k → ℕ} {T U : ℕ} (hp : VB p a T b) (hq : VB q b U c) :
    VB (XProg.seq p q) a (T + U) c := fun ℓ hℓ =>
  ⟨Nat.add_le_add (hp ℓ hℓ).1 (hq _ (hp ℓ hℓ).2).1, (hq _ (hp ℓ hℓ).2).2⟩

theorem VB.mono {p : XProg k} {a a' b b' : Fin k → ℕ} {T T' : ℕ} (h : VB p a T b) (ha : a' ≤ a)
    (hT : T ≤ T') (hb : b ≤ b') : VB p a' T' b' := fun ℓ hℓ =>
  ⟨(h ℓ (hℓ.trans ha)).1.trans hT, (h ℓ (hℓ.trans ha)).2.trans hb⟩

theorem VB.frame {m : ℕ} (e : Fin m ↪ Fin k) {p : XProg m} {a : Fin k → ℕ} {T : ℕ}
    {b : Fin m → ℕ} (h : VB p (fun j => a (e j)) T b) : VB (frame e p) a T (embedF e a b) :=
  fun ℓ hℓ => ⟨(h _ fun j => hℓ (e j)).1, embedF_mono e hℓ (h _ fun j => hℓ (e j)).2⟩

theorem VB.prim (p : Prim k) {a : Fin k → ℕ} {M : ℕ} (hM : ∀ i, a i ≤ M) :
    VB (prog (.prim p)) a (2 * (M + 1) + 3) (p.lenT a) := fun ℓ hℓ => by
  refine ⟨?_, Prim.lenT_mono p hℓ⟩
  show 2 * (supB ℓ + p.pad) + 3 ≤ _
  have := supB_le_of fun i => (hℓ i).trans (hM i)
  have := pad_le p
  omega

theorem VB.natP {t c : Fin k} (hct : c ≠ t) (n : ℕ) {a : Fin k → ℕ} {M : ℕ} (hM : ∀ i, a i ≤ M)
    (hn : n ≤ M) : VB (natP t c n) a ((2 * n + 1) * (4 * M + 12)) (natB t c n a) := fun ℓ hℓ => by
  obtain ⟨h1, h2⟩ := natP_bounds hct n ℓ M (fun i => (hℓ i).trans (hM i)) hn
  refine ⟨h2, h1.trans fun i => ?_⟩
  simp only [natB]
  split_ifs
  · exact le_rfl
  · exact max_le_max (hℓ c) le_rfl
  · exact hℓ i

open SigabaNeo.Tape.Sym in
/-- **A relabelled program with a checked certificate.** -/
theorem VB.checkMap {m fuel : ℕ} {p : Prog m} {σ claim : Asg} {w : Poly}
    (h : check fuel p σ claim w = true) (ρ : List ℕ) {u : Fin m → Fin k}
    (hu : Function.Injective u) {a b : Fin k → ℕ}
    (hin : ∀ j, a (u j) ≤ pEval ρ (aGet σ j.val)) (hM : ∀ t, a t ≤ top ρ)
    (hout : ∀ j : Fin m, j.val < claim.length → pEval ρ (aGet claim j.val) ≤ b (u j))
    (hscr : ∀ j : Fin m, claim.length ≤ j.val → top ρ ≤ b (u j))
    (hrest : ∀ t, (∀ j, u j ≠ t) → a t ≤ b t) :
    VB (prog (Prog.map u p)) a ((2 * top ρ + 3) * pEval ρ w) b := by
  intro ℓ hℓ
  unfold check at h
  rcases hr : absRun fuel p σ with _ | ⟨σ', w'⟩
  · rw [hr] at h; simp at h
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := absRun_sound fuel p hr ρ k u hu ℓ (fun j => (hℓ (u j)).trans (hin j))
    (fun t => (hℓ t).trans (hM t))
  refine ⟨h2.trans (Nat.mul_le_mul_left _ (pEval_le_of_pLe ρ h.2)), fun t => ?_⟩
  show Prog.lenBoundT (Prog.map u p) ℓ t ≤ b t
  by_cases ht : ∃ j, u j = t
  · obtain ⟨j, rfl⟩ := ht
    by_cases hj : j.val < claim.length
    · refine (h1 j).trans ?_
      have := aLe_spec ρ h.1 j.val
      rw [aGet_take σ' hj] at this
      exact this.trans (hout j hj)
    · exact (Sym.lenBoundT_le_const _ ((noGrow_of_absRun fuel p hr).map u)
        (fun t => (hℓ t).trans (hM t)) (u j)).trans (hscr j (by omega))
  · push Not at ht
    rw [Prog.lenBoundT_of_preserves t _ (Prog.preserves_map_of_not_mem ht p) ℓ]
    exact (hℓ t).trans (hrest t ht)

/-! ### Blank scratch -/

/-- `M` on the tapes `< j`, `0` on the others. -/
def zv (j M : ℕ) : Fin k → ℕ := fun i => if i.val < j then M else 0

theorem zv_le (j M : ℕ) (i : Fin k) : (zv j M : Fin k → ℕ) i ≤ M := by
  unfold zv; split_ifs <;> omega

theorem zv_mono {j M M' : ℕ} (h : M ≤ M') : (zv j M : Fin k → ℕ) ≤ zv j M' := by
  intro i; simp only [zv]; split_ifs <;> omega

/-- **A uniform bound keeping the scratch tapes `≥ j` blank.** -/
def UBZ (j : ℕ) (p : XProg k) (M T M' : ℕ) : Prop := VB p (zv j M) T (zv j M')

theorem UBZ.seq {j : ℕ} {p q : XProg k} {M T M' U M'' : ℕ} (hp : UBZ j p M T M')
    (hq : UBZ j q M' U M'') : UBZ j (XProg.seq p q) M (T + U) M'' := VB.seq hp hq

theorem UBZ.mono {j : ℕ} {p : XProg k} {M T M' T' M'' : ℕ} (h : UBZ j p M T M') (hT : T ≤ T')
    (hM : M' ≤ M'') : UBZ j p M T' M'' := VB.mono h le_rfl hT (zv_mono hM)

/-- **A framed block**: the frame sends the tapes `< j'` of the block to tapes `< j`, the others
to tapes `≥ j`. -/
theorem UBZ.frame {m j j' : ℕ} (e : Fin m ↪ Fin k) (he : ∀ i, (e i).val < j ↔ i.val < j')
    {p : XProg m} {M T M' : ℕ} (h : UBZ j' p M T M') (hM : M ≤ M') :
    UBZ j (frame e p) M T M' := by
  have h' : VB p (fun i => (zv j M : Fin k → ℕ) (e i)) T (zv j' M') := by
    refine VB.mono h (by intro i; simp only [zv, he]; exact le_rfl) le_rfl le_rfl
  refine (VB.frame e h').mono le_rfl le_rfl fun t => ?_
  rcases embedF_cases e (zv j M) (zv j' M') t with ⟨-, h1⟩ | ⟨i, rfl, h1⟩
  · rw [h1]; exact zv_mono hM t
  · rw [h1]; simp only [zv, he]; exact le_rfl

end XProg

end SigabaNeo.Tape

namespace SigabaNeo.Tape.XProg

variable {k : ℕ}

/-! ### The size of a counter built by doubling -/

theorem size_dblP (t c : Fin k) : (dblP t c).size ≤ 135 := by
  simp [dblP, XProg.forN, bitAp, Prog.size, Prim.pad]

/-- **A counter of `n < 2^m` costs `O(m)` states.** -/
theorem size_natP_le (t c : Fin k) : ∀ (n m : ℕ), n < 2 ^ m → (natP t c n).size ≤ 195 * m + 36
  | 0, m, _ => by unfold natP; simp [Prog.size, Prim.pad]
  | n + 1, m, h => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by
      rcases m with _ | m
      · simp at h
      · simp⟩
    have hm : (n + 1) / 2 < 2 ^ m' := by rw [pow_succ] at h; omega
    have ih := size_natP_le t c ((n + 1) / 2) m' hm
    have hd := size_dblP t c
    unfold natP
    split_ifs
    · simp only [size_seq]; omega
    · simp only [size_seq, bitAp, size_prog, Prog.size, Prim.pad]; omega

end SigabaNeo.Tape.XProg

namespace SigabaNeo.Tape.XProg

theorem natB_le' {k : ℕ} {t c : Fin k} {n M : ℕ} {a : Fin k → ℕ} (ha : ∀ i, a i ≤ M) (hn : n ≤ M)
    (i : Fin k) : natB t c n a i ≤ M := by
  simp only [natB]; split_ifs
  · exact hn
  · exact max_le (ha c) hn
  · exact ha i

end SigabaNeo.Tape.XProg

/-! ### Programs as framed programs, structurally -/

namespace SigabaNeo.Tape.Prog

variable {k : ℕ}

/-- A program as a framed program, construct by construct (loops stay loops), so the shape bounds
of `SigabaNeoStd.Machines.Prog.SampleTime` (`ATB`) apply to its parts. -/
def toX : Prog k → XProg k
  | prim p => .prog (prim p)
  | coin i => .prog (coin i)
  | seq p q => .seq (toX p) (toX q)
  | ifBlank i p q => .ifBlank i (toX p) (toX q)
  | ifBit i p q => .ifBit i (toX p) (toX q)
  | loop i body => .loop i (toX body)

theorem denote_toX : ∀ p : Prog k, (toX p).denote = p.denote
  | prim _ => rfl
  | coin _ => rfl
  | seq p q => by funext s; simp only [toX, XProg.denote, denote, denote_toX p, denote_toX q]
  | ifBlank i p q => by funext s; simp only [toX, XProg.denote, denote, denote_toX p, denote_toX q]
  | ifBit i p q => by funext s; simp only [toX, XProg.denote, denote, denote_toX p, denote_toX q]
  | loop i body => by funext s; simp only [toX, XProg.denote, denote, denote_toX body]

theorem law_toX (p : Prog k) (s : Store k) : (toX p).law s = p.law s := by
  simp only [XProg.law, Prog.law, denote_toX]

theorem lenBoundT_toX : ∀ p : Prog k, XProg.lenBoundT (toX p) = lenBoundT p
  | prim _ => rfl
  | coin _ => rfl
  | seq p q => by funext ℓ; simp only [toX, XProg.lenBoundT, lenBoundT, lenBoundT_toX p, lenBoundT_toX q]
  | ifBlank i p q => by
    funext ℓ; simp only [toX, XProg.lenBoundT, lenBoundT, lenBoundT_toX p, lenBoundT_toX q]
  | ifBit i p q => by
    funext ℓ; simp only [toX, XProg.lenBoundT, lenBoundT, lenBoundT_toX p, lenBoundT_toX q]
  | loop i body => by
    funext ℓ; simp only [toX, XProg.lenBoundT, lenBoundT, lenBoundT_toX body]

theorem timeBoundT_toX : ∀ p : Prog k, XProg.timeBoundT (toX p) = timeBoundT p
  | prim _ => rfl
  | coin _ => rfl
  | seq p q => by
    funext ℓ; simp only [toX, XProg.timeBoundT, timeBoundT, timeBoundT_toX p, timeBoundT_toX q,
      lenBoundT_toX p]
  | ifBlank i p q => by
    funext ℓ; simp only [toX, XProg.timeBoundT, timeBoundT, timeBoundT_toX p, timeBoundT_toX q]
  | ifBit i p q => by
    funext ℓ; simp only [toX, XProg.timeBoundT, timeBoundT, timeBoundT_toX p, timeBoundT_toX q]
  | loop i body => by
    funext ℓ
    have e : XProg.loopStepT i (toX body) = loopStepT i body := by
      funext ℓ'; simp only [XProg.loopStepT, loopStepT, lenBoundT_toX body]
    simp only [toX, XProg.timeBoundT, timeBoundT, timeBoundT_toX body, e]

theorem preserves_toX (i : Fin k) : ∀ p : Prog k, p.Preserves i → (toX p).Preserves i
  | prim _, h => h
  | coin _, h => h
  | seq p q, h => ⟨preserves_toX i p h.1, preserves_toX i q h.2⟩
  | ifBlank _ p q, h => ⟨preserves_toX i p h.1, preserves_toX i q h.2⟩
  | ifBit _ p q, h => ⟨preserves_toX i p h.1, preserves_toX i q h.2⟩
  | loop _ body, h => ⟨h.1, preserves_toX i body h.2⟩

theorem wf_toX : ∀ p : Prog k, p.WF → (toX p).WF
  | prim _, _ => trivial
  | coin _, _ => trivial
  | seq p q, h => ⟨wf_toX p h.1, wf_toX q h.2⟩
  | ifBlank _ p q, h => ⟨wf_toX p h.1, wf_toX q h.2⟩
  | ifBit _ p q, h => ⟨wf_toX p h.1, wf_toX q h.2⟩
  | loop i body, h => ⟨wf_toX body h.1, preserves_toX i body h.2⟩

theorem size_toX : ∀ p : Prog k, (toX p).size = p.size
  | prim _ => rfl
  | coin _ => rfl
  | seq p q => by simp only [toX, XProg.size, size, size_toX p, size_toX q]
  | ifBlank _ p q => by simp only [toX, XProg.size, size, size_toX p, size_toX q]
  | ifBit _ p q => by simp only [toX, XProg.size, size, size_toX p, size_toX q]
  | loop _ body => by simp only [toX, XProg.size, size, size_toX body]

end SigabaNeo.Tape.Prog
