import PE.Impl.ExpLUT.Prog.EncDigitMath

/-! # The digit machine's stream order is the scheme's `Dig` codec order -/

namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix

/-- Enumerating list positions and reading them reconstructs the list. -/
theorem map_range_getD {α : Type} (l : List α) (a : α) :
    (List.range' 0 l.length).map (fun i ↦ l.getD i a) = l := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range', zero_add, one_mul]
    exact List.getD_eq_getElem _ _ hi'

/-- A natural-indexed stream traverses an explicit enumeration exactly once. -/
theorem wordStream_enum {α β : Type} [Enum α] {n : ℕ}
    (e : FixedEnc β n) (f : α → β) (a : α) :
    wordStream e (fun i ↦ f ((Enum.list (α := α)).getD i a)) 0
      (Enum.list (α := α)).length = (FixedEnc.fun (α := α) e).enc f := by
  unfold wordStream
  rw [show (fun i ↦ f ((Enum.list (α := α)).getD i a)) =
    f ∘ (fun i ↦ (Enum.list (α := α)).getD i a) from rfl,
    ← List.map_map, map_range_getD]
  rfl

/-- The corresponding equality for streams of complete blocks. -/
theorem blockStream_enum {α : Type} [Enum α] (f : α → List Bool) (a : α) :
    blockStream (fun i ↦ f ((Enum.list (α := α)).getD i a)) 0
      (Enum.list (α := α)).length = (Enum.list (α := α)).flatMap f := by
  unfold blockStream
  have h := congrArg (List.flatMap f) (map_range_getD (Enum.list (α := α)) a)
  simpa only [List.flatMap_map] using h

variable (D : Dims)

/-- Row/column of an entry, in the canonical matrix traversal order. -/
def entryAt (t : ℕ) : Fin 2 × Col D.K :=
  (Enum.list (α := Fin 2 × Col D.K)).getD t (0, 0, ⟨0, D.K_pos⟩)

/-- The digit position associated with the two loops of the actual machine. -/
def digAt (t i : ℕ) : Dig D.K :=
  ((entryAt D t).1, (entryAt D t).2, ⟨i % D.K, Nat.mod_lt _ D.K_pos⟩)

/-- The inner digit loop follows the `Fin K` enumeration. -/
theorem wordStream_fin {α : Type} {n : ℕ} (e : FixedEnc α n) (f : Fin D.K → α) :
    wordStream e (fun i ↦ f ⟨i % D.K, Nat.mod_lt _ D.K_pos⟩) 0 D.K =
      (FixedEnc.fun (α := Fin D.K) e).enc f := by
  have h := wordStream_enum e f (⟨0, D.K_pos⟩ : Fin D.K)
  simp only [len_fin] at h
  rw [← h]
  unfold wordStream
  apply congrArg (fun l : List α ↦ l.flatMap e.enc)
  apply List.map_congr_left
  intro i hi
  have hi' : i < D.K := by simpa using hi
  rw [List.getD_eq_getElem _ _ (by simpa [len_fin] using hi'), Enum.getElem_fin]
  simp [Nat.mod_eq_of_lt hi']

/-- The matrix-entry enumeration has exactly `4K` entries. -/
theorem length_entries : (Enum.list (α := Fin 2 × Col D.K)).length =
    D.K + D.K + (D.K + D.K) := by
  rw [Enum.length_prod, len_fin, length_col]; omega

/-- Nested entry/digit loops match the right-associated `Dig` product enumeration. -/
theorem digitBlocks_codec {α : Type} {n : ℕ} (e : FixedEnc α n) (F : Dig D.K → α) :
    blockStream (fun t ↦ wordStream e (fun i ↦ F (digAt D t i)) 0 D.K) 0
      (D.K + D.K + (D.K + D.K)) = (FixedEnc.fun (α := Dig D.K) e).enc F := by
  have hi (t : ℕ) : wordStream e (fun i ↦ F (digAt D t i)) 0 D.K =
      (FixedEnc.fun (α := Fin D.K) e).enc (fun i ↦ F ((entryAt D t).1, (entryAt D t).2, i)) :=
    wordStream_fin D e (fun i ↦ F ((entryAt D t).1, (entryAt D t).2, i))
  simp_rw [hi]
  rw [← length_entries D]
  unfold entryAt
  rw [blockStream_enum (fun p : Fin 2 × Col D.K ↦
    (FixedEnc.fun (α := Fin D.K) e).enc (fun i ↦ F (p.1, p.2, i))) (0, 0, ⟨0, D.K_pos⟩)]
  simp [FixedEnc.fun, FixedEnc.encList, Dig, Enum.list, List.product,
    List.flatMap_map, List.flatMap_assoc]

/-- Canonical entry words are exactly the row-major matrix codec. -/
theorem entryBlocks_codec (C : Fin 2 → Col D.K → Rg D) :
    blockStream (fun t ↦ wd D (C (entryAt D t).1 (entryAt D t).2)) 0
      (D.K + D.K + (D.K + D.K)) = (matE D (Fin 2) (Col D.K)).enc C := by
  rw [← length_entries D]
  unfold entryAt
  rw [blockStream_enum (fun p : Fin 2 × Col D.K ↦ wd D (C p.1 p.2)) (0, 0, ⟨0, D.K_pos⟩)]
  simp [matE, FixedEnc.fun, FixedEnc.encList, Enum.list, List.product,
    List.flatMap_map, List.flatMap_assoc, wd]

/-- The row family of a gadget ciphertext encrypted under the decoded secret word. -/
noncomputable def digitRows (s : List Bool) (C : Fin 2 → Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D)
    (d : Dig D.K) : Col D.K → Rg D :=
  sec (decRM D.N D.K s) ᵥ* A d -
    (digits (setting D) C d • sec (decRM D.N D.K s)) ᵥ* GD D + E d

/-- The natural-indexed loop's row is the corresponding `Dig`-indexed scheme row. -/
theorem digitRow_digAt (s : List Bool) (C : Fin 2 → Col D.K → Rg D)
    (A : Dig D.K → Fin 2 → Col D.K → Rg D) (E : Dig D.K → Col D.K → Rg D)
    (t i : ℕ) :
    digitRow D s (C (entryAt D t).1 (entryAt D t).2)
      (fun k ↦ A (digAt D t k)) (fun k ↦ E (digAt D t k)) i =
      digitRows D s C A E (digAt D t i) := rfl

/-- The complete word-level digit phase, stated directly with scheme codecs. -/
theorem deSteps_encoded {s : List Bool} (hs : s.length = D.N * D.K)
    (C : Fin 2 → Col D.K → Rg D) (A : Dig D.K → Fin 2 → Col D.K → Rg D)
    (E : Dig D.K → Col D.K → Rg D) (out restC restA restE : List Bool)
    (hout : (D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ out.length) :
    (deOut D.N D.K (D.K + D.K) s)^[D.K + D.K + (D.K + D.K)]
      ((matE D (Fin 2) (Col D.K)).enc C ++ restC, out,
        (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc A ++ restA,
        (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc E ++ restE) =
      (restC, (out ++ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
        (digitRows D s C A E)).drop ((D.K + D.K + (D.K + D.K)) *
          (D.K * ((D.K + D.K) * (D.N * D.K)))), restA, restE) := by
  have hc := deOut_stream D hs (fun t ↦ C (entryAt D t).1 (entryAt D t).2)
    (fun t i ↦ A (digAt D t i)) (fun t i ↦ E (digAt D t i)) 0
    (D.K + D.K + (D.K + D.K)) out restC restA restE hout
  rw [entryBlocks_codec, digitBlocks_codec, digitBlocks_codec] at hc
  have hr (t : ℕ) : digitRow D s (C (entryAt D t).1 (entryAt D t).2)
      (fun k ↦ A (digAt D t k)) (fun k ↦ E (digAt D t k)) =
      fun i ↦ digitRows D s C A E (digAt D t i) := funext (fun _ ↦ rfl)
  simp_rw [hr] at hc
  rw [digitBlocks_codec] at hc
  exact hc

/-- The actual digit machine consumes scheme codecs and writes the scheme row-family codec. -/
theorem run_deP_encoded (S : Store 74) (h : DigitOK D S)
    (C : Fin 2 → Col D.K → Rg D) (A : Dig D.K → Fin 2 → Col D.K → Rg D)
    (E : Dig D.K → Col D.K → Rg D) (restC restA restE : List Bool)
    (hcount : (S 14).length = D.K + D.K + (D.K + D.K))
    (hC : S 2 = (matE D (Fin 2) (Col D.K)).enc C ++ restC)
    (hA : S 3 = (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K))).enc A ++ restA)
    (hE : S 4 = (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc E ++ restE)
    (hout : (D.K + D.K + (D.K + D.K)) *
      (D.K * ((D.K + D.K) * (D.N * D.K))) ≤ (S 0).length) :
    deP.run S = Function.update (Function.update (Function.update (Function.update S 2 restC) 0
      ((S 0 ++ (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc
        (digitRows D (S 1) C A E)).drop ((D.K + D.K + (D.K + D.K)) *
          (D.K * ((D.K + D.K) * (D.N * D.K)))))) 3 restA) 4 restE := by
  have hc := run_deP_scheme D S h (fun t ↦ C (entryAt D t).1 (entryAt D t).2)
    (fun t i ↦ A (digAt D t i)) (fun t i ↦ E (digAt D t i)) 0
    (D.K + D.K + (D.K + D.K)) restC restA restE hcount
    (by rw [entryBlocks_codec]; exact hC)
    (by rw [digitBlocks_codec]; exact hA)
    (by rw [digitBlocks_codec]; exact hE) hout
  have hr (t : ℕ) : digitRow D (S 1) (C (entryAt D t).1 (entryAt D t).2)
      (fun k ↦ A (digAt D t k)) (fun k ↦ E (digAt D t k)) =
      fun i ↦ digitRows D (S 1) C A E (digAt D t i) := funext (fun _ ↦ rfl)
  simp_rw [hr] at hc
  rw [digitBlocks_codec] at hc
  exact hc

end AdvancedEncryption.ExpLUT.Prog.EncW
