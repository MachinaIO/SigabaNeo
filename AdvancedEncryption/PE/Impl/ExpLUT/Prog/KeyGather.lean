import PE.Impl.ExpLUT.Prog.KeyPublicRow
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMUtil

/-! Indexed extraction of ring coordinates from an encoded family, using actual VM instructions. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- Read coordinate j from source register 0 into register 3, preserving the source.
The bit offset is constructed by binary doubling, not by embedding a unary literal. -/
def fetchRingC (N K j : ℕ) : Code := .seq (natC 2 rB1 (j * (N * K))) <|
  .seq (.cp 1 0) <| .seq (.drop 1 2) <| .seq (.cp 3 rZ) (.mvR 3 1)

theorem wf_fetchRingC (N K j : ℕ) : (fetchRingC N K j).WFc :=
  ⟨natC_wfc _ _ _, trivial, trivial, trivial, trivial⟩

theorem fetchRingC_preserves (N K j : ℕ) (i : Fin 64)
    (h1 : i ≠ 1) (h2 : i ≠ 2) (h3 : i ≠ 3) : (fetchRingC N K j).writes i = false := by
  simp [fetchRingC, Code.writes, natC_writes _ _ _ i h2, Ne.symm h1, Ne.symm h3]

/-- Dropping whole ring words agrees with dropping entries of the decoded list. -/
theorem encL_drop_words {N K : ℕ} (xs : List (Rq N K)) (j : ℕ) (hj : j ≤ xs.length) :
    (encL N K xs).drop (j * (N * K)) = encL N K (xs.drop j) := by
  have he := drop_encL (N := N) (K := K) (xs.take j) (xs.drop j)
    (show (xs.take j).length = j by simp [Nat.min_eq_left hj])
  simpa only [List.take_append_drop] using he

/-- Exact coordinate extraction, with no change to the source register. -/
theorem exec_fetchRingC {N K : ℕ} (j : ℕ) (w : St) (xs : List (Rq N K))
    (hj : j < xs.length) (hS : w 0 = encL N K xs)
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) :
    exec N K (fetchRingC N K j) w 3 = encRM N K xs[j] := by
  rw [fetchRingC, exec_seq, exec_natC _ _ (by decide) _ w h1]
  vm_simp
  simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, hS, hZ, List.length_replicate]
  rw [encL_drop_words xs j hj.le, drop_cons_getElem xs hj, encL_cons]
  simp

/-- Append a list of statically selected coordinates to register 4. -/
def gatherAppendC (N K : ℕ) : List ℕ → Code
  | [] => .nop
  | j :: js => .seq (fetchRingC N K j) (.seq (.app 4 3) (gatherAppendC N K js))

def gatherC (N K : ℕ) (js : List ℕ) : Code := .seq (.clr 4) (gatherAppendC N K js)

theorem wf_gatherAppendC (N K : ℕ) : ∀ js, (gatherAppendC N K js).WFc
  | [] => trivial
  | _j :: js => ⟨wf_fetchRingC _ _ _, trivial, wf_gatherAppendC N K js⟩

theorem wf_gatherC (N K : ℕ) (js : List ℕ) : (gatherC N K js).WFc :=
  ⟨trivial, wf_gatherAppendC N K js⟩

theorem gatherAppendC_preserves (N K : ℕ) (i : Fin 64)
    (h1 : i ≠ 1) (h2 : i ≠ 2) (h3 : i ≠ 3) (h4 : i ≠ 4) :
    ∀ js, (gatherAppendC N K js).writes i = false
  | [] => rfl
  | j :: js => by
    simp [gatherAppendC, Code.writes, fetchRingC_preserves N K j i h1 h2 h3,
      gatherAppendC_preserves N K i h1 h2 h3 h4 js, Ne.symm h4]

theorem exec_gatherAppendC {N K : ℕ} (xs : List (Rq N K)) :
    ∀ (js : List ℕ) (w : St) (out : List (Rq N K)), (∀ j ∈ js, j < xs.length) →
    w 0 = encL N K xs → w rB1 = [false] → w rZ = encRM N K 0 → w 4 = encL N K out →
    exec N K (gatherAppendC N K js) w 4 = encL N K (out ++ js.map (fun j ↦ xs.getD j 0))
  | [], w, out, _, _, _, _, ho => by simpa [gatherAppendC] using ho
  | j :: js, w, out, hj, hS, h1, hZ, ho => by
    let v := exec N K (.app 4 3) (exec N K (fetchRingC N K j) w)
    have keep : ∀ i : Fin 64, i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 4 → v i = w i := by
      intro i h1' h2' h3' h4'
      change Function.update (exec N K (fetchRingC N K j) w) 4 _ i = _
      rw [Function.update_of_ne h4', exec_writes _ _ _ (fetchRingC_preserves _ _ _ i h1' h2' h3')]
    have vo : v 4 = encL N K (out ++ [xs.getD j 0]) := by
      change exec N K (fetchRingC N K j) w 4 ++ exec N K (fetchRingC N K j) w 3 = _
      rw [exec_writes _ _ _ (fetchRingC_preserves _ _ _ 4 (by decide) (by decide) (by decide)), ho,
        exec_fetchRingC j w xs (hj j (by simp)) hS h1 hZ,
        List.getD_eq_getElem _ _ (hj j (by simp)), encL_append, encL_singleton]
    have h := exec_gatherAppendC xs js v (out ++ [xs.getD j 0])
      (fun k hk ↦ hj k (by simp [hk]))
      ((keep 0 (by decide) (by decide) (by decide) (by decide)).trans hS)
      ((keep rB1 (by decide) (by decide) (by decide) (by decide)).trans h1)
      ((keep rZ (by decide) (by decide) (by decide) (by decide)).trans hZ) vo
    change exec N K (gatherAppendC N K js) v 4 = _
    simpa only [List.map_cons, List.append_assoc, List.singleton_append] using h

theorem exec_gatherC {N K : ℕ} (xs : List (Rq N K)) (js : List ℕ) (w : St)
    (hj : ∀ j ∈ js, j < xs.length) (hS : w 0 = encL N K xs)
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) :
    exec N K (gatherC N K js) w 4 = encL N K (js.map (fun j ↦ xs.getD j 0)) := by
  rw [gatherC, exec_seq]
  simpa using exec_gatherAppendC xs js (exec N K (.clr 4) w) [] hj
    (by simpa using hS) (by simpa using h1) (by simpa using hZ) (by simp)

/-- Gather an arbitrary selection of coordinates from an explicitly enumerated family. -/
theorem exec_gatherC_family {N K : ℕ} {α : Type} [Enum α] [DecidableEq α]
    (f : α → Rq N K) (is : List α) (w : St)
    (hS : w 0 = encL N K (Enum.list.map f))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) :
    exec N K (gatherC N K (is.map Enum.index)) w 4 = encL N K (is.map f) := by
  rw [exec_gatherC (Enum.list.map f) (is.map Enum.index) w
    (by intro j hj; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hj
        simpa using Enum.index_lt a) hS h1 hZ]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  dsimp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by simpa using Enum.index_lt a), List.getElem_map,
    Enum.getElem_index]

/-- Candidate coordinates used by the positive public-row blocks. -/
def positiveSelection (D : Dims) (i : Fin (setting D).E.W) :
    PublicPos (Wb D) (Jh D) (setting D).τ →
      PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W
  | .inl w => .inl (i, w)
  | .inr (.inl (k, c)) => .inr (.inl (i, k, c))
  | .inr (.inr c) => .inr (.inr c)

/-- The negative gadget block reads the unique predecessor row for each helper. -/
noncomputable def negativeSelection (D : Dims) (i : Fin (setting D).E.W)
    (kc : Jh D × Col (setting D).τ) :
    PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W :=
  .inr (.inl ((helperMap D).backRow i kc.1, kc.1, kc.2))

open Classical in
noncomputable def positiveGatherC (D : Dims) (i : Fin (setting D).E.W) : Code :=
  gatherC D.N D.K (Enum.list.map (Enum.index ∘ positiveSelection D i))

open Classical in
noncomputable def negativeGatherC (D : Dims) (i : Fin (setting D).E.W) : Code :=
  gatherC D.N D.K (Enum.list.map (Enum.index ∘ negativeSelection D i))

theorem exec_positiveGatherC (D : Dims) (i : Fin (setting D).E.W)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hS : w 0 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (positiveGatherC D i) w 4 =
      encL D.N D.K (Enum.list.map (publicPosInput p i)) := by
  classical
  have h := exec_gatherC_family p (Enum.list.map (positiveSelection D i)) w hS h1 hZ
  simp only [List.map_map] at h
  have he : p ∘ positiveSelection D i = publicPosInput p i := by
    funext t
    rcases t with w | ⟨k, c⟩ | c <;> rfl
  rw [he] at h
  exact h

theorem exec_negativeGatherC (D : Dims) (i : Fin (setting D).E.W)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D) (w : St)
    (hS : w 0 = encL D.N D.K (Enum.list.map p))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (negativeGatherC D i) w 4 =
      encL D.N D.K (Enum.list.map (publicNegInput (helperMap D) p i)) := by
  classical
  have h := exec_gatherC_family p (Enum.list.map (negativeSelection D i)) w hS h1 hZ
  simp only [List.map_map] at h
  have he : p ∘ negativeSelection D i = publicNegInput (helperMap D) p i := by
    funext kc; rfl
  rw [he] at h
  exact h

theorem wf_positiveGatherC (D : Dims) (i : Fin (setting D).E.W) :
    (positiveGatherC D i).WFc := wf_gatherC _ _ _

theorem wf_negativeGatherC (D : Dims) (i : Fin (setting D).E.W) :
    (negativeGatherC D i).WFc := wf_gatherC _ _ _

end AdvancedEncryption.ExpLUT.Prog
