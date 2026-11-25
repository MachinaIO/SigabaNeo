import PE.Impl.RingBTVW.Prog.Fields

/-!
# Finishing a component

A component is `seq body (finP o)`: the body leaves the output on the value tape `o`; `finP o`
copies it to tape `0` and clears every other tape (`law_finP`). Hence the output is alone on
tape `0`, and the per-tape length bound at the end is `io2 L 0 0` (`len_comp`): every tape but
`0` was cleared.
-/

namespace AdvancedEncryption.RingBTVW.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-- All the tapes but `0`. -/
def scrL : List (Fin 82) := (List.finRange 82).filter fun t => t ≠ 0

theorem mem_scrL (t : Fin 82) : t ∈ scrL ↔ t ≠ 0 := by simp [scrL]

/-- **Copy the output to tape `0` and clear every other tape.** -/
def finP (o : Fin 82) : XProg 82 := seq (prog (.prim (.copy 0 o))) (clearL scrL)

theorem wf_finP (o : Fin 82) : (finP o).WF := ⟨trivial, wf_clearL _⟩

theorem law_finP (o : Fin 82) (s : Store 82) {v : List Bool} (hv : s o = v) :
    (finP o).law s = PMF.pure (ioS (R := 80) v [] []) := by
  rw [finP, law_seq, law_prim, PMF.pure_bind, law_clearL]
  congr 1
  funext t
  by_cases ht : t = 0
  · subst ht; simp [mem_scrL, Prim.apply, hv, ioS]
  · have h1 : t.val ≠ 0 := fun h => ht (Fin.ext h)
    simp [mem_scrL, ht, ioS, h1]

theorem lenBoundT_clearL : ∀ (l : List (Fin 82)) (ℓ : Fin 82 → ℕ),
    lenBoundT (clearL l) ℓ = fun t => if t ∈ l then 0 else ℓ t
  | [], ℓ => by
    funext t
    show (Prim.copy 0 0).lenT ℓ t = _
    simp only [Prim.lenT, Function.update_apply]
    split_ifs with h <;> simp_all
  | t :: l, ℓ => by
    show lenBoundT (clearL l) ((Prim.clear t).lenT ℓ) = _
    rw [lenBoundT_clearL l]
    funext u
    simp only [Prim.lenT, Function.update_apply, List.mem_cons]
    by_cases h1 : u = t <;> by_cases h2 : u ∈ l <;> simp [h1, h2]

theorem len_finP (o : Fin 82) (ℓ : Fin 82 → ℕ) : lenBoundT (finP o) ℓ = io2 (R := 80) (ℓ o) 0 0 := by
  show lenBoundT (clearL scrL) ((Prim.copy 0 o).lenT ℓ) = _
  rw [lenBoundT_clearL]
  funext t
  by_cases ht : t = 0
  · subst ht; simp [mem_scrL, Prim.lenT, io2]
  · have h1 : t.val ≠ 0 := fun h => ht (Fin.ext h)
    simp [mem_scrL, ht, io2, h1]

/-- The time of `finP` from tapes below `M`. -/
def timeFin (M : ℕ) : ℕ := (2 * (M + 1) + 3) + (scrL.length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem time_finP (o : Fin 82) (M : ℕ) {ℓ : Fin 82 → ℕ} (hℓ : ∀ i, ℓ i ≤ M) :
    timeBoundT (finP o) ℓ ≤ timeFin M := by
  have h1 := VB.prim (.copy 0 o) hℓ
  have h2 := vb_clearL (M := M) scrL (a := (Prim.copy 0 o).lenT ℓ) fun t => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs
    · exact hℓ o
    · exact hℓ t
  exact ((h1.seq h2) ℓ le_rfl).1

/-- **The length bound of a component**: the output below `M'`, every other tape blank. -/
theorem len_comp {body : XProg 82} {M T M' : ℕ} (hb : UBZ 20 body M T M') (o : Fin 82)
    (ℓ : Fin 82 → ℕ) (hℓ : ℓ ≤ zv 20 M) :
    lenBoundT (seq body (finP o)) ℓ ≤ io2 (R := 80) M' 0 0 := by
  show lenBoundT (finP o) (lenBoundT body ℓ) ≤ _
  rw [len_finP]
  intro t
  simp only [io2]
  split_ifs
  · exact ((hb ℓ hℓ).2 o).trans (zv_le 20 M' o)
  · exact le_rfl
  · exact le_rfl

/-- **The time of a component.** -/
theorem time_comp {body : XProg 82} {M T M' : ℕ} (hb : UBZ 20 body M T M') (o : Fin 82)
    (ℓ : Fin 82 → ℕ) (hℓ : ℓ ≤ zv 20 M) :
    timeBoundT (seq body (finP o)) ℓ ≤ T + timeFin M' := by
  rw [timeBoundT_seq]
  exact Nat.add_le_add (hb ℓ hℓ).1 (time_finP o M' fun i => ((hb ℓ hℓ).2 i).trans (zv_le 20 M' i))

theorem io2_le (a b : ℕ) (i : Fin 82) : io2 (R := 80) a b 0 i ≤ max a b := by
  simp only [io2]; split_ifs <;> omega

/-- The inputs of a component fit the scratch-blank shape. -/
theorem io2_le_zv {a b M : ℕ} (h : max a b ≤ M) : io2 (R := 80) a b 0 ≤ zv 20 M := fun i => by
  simp only [io2, zv]; split_ifs <;> first | omega | simp_all

/-- **The word of `1`** at the component level. -/
theorem ub_oneB' (N K M : ℕ) (hM : N * K ≤ M) (h1 : 1 ≤ M) : UBZ 1 (oneB N K) M (timeOneB N K M) M :=
  ub_oneB N K M hM h1

end AdvancedEncryption.RingBTVW.Prog
