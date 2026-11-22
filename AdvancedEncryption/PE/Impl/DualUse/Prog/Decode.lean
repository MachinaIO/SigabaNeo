import PE.Impl.DualUse.Prog.DecodeWord
import PE.Impl.DualUse.Prog.Layout
import PE.Impl.DualUse.Registry

/-!
# The decoding machines of the reductions

The first part `P` of a reduction machine (`PE.Impl.DualUse.ReductionMachine`) turns the
registry's Ring-LWE word into the initial state of the reduction's handlers: the instance in the
fixed-length layout of `PE.Impl.DualUse.Prog.Layout`, **preceded by the marker bit `true`** (so the
state word never starts with `false`).

* `enumFin α`: the position in the explicit enumeration `Enum α`, as an equivalence
  `α ≃ Fin |α|` (its inverse is the enumeration itself). The registry's words are reindexed by it
  (instead of the noncomputable `Fintype.equivFin`), so the samples come in the order of the
  layouts: `real3_wordE`, `unif3_wordE`, `real5_wordE`, `unif5_wordE` are `real3_word` … of
  `PE.Impl.DualUse.Registry` for this reindexing.
* `inst3Of`, `inst5Of`: the instance of a word (`split3`, `split5` of the decoded pair, reindexed
  by `enumFin`), as `wordDist` reads it (`wordDist_split3`, `wordDist_split5`).
* `dec3M N K k` (hybrid 3 and the ideal side) and `dec5M N K k d` (hybrid 5): the parser
  `SigabaNeo.Tape.Prog.decodeM` (the second negating the public parts), clocked for the registry's
  words (`encLen`).
* **`run_dec3M`**, **`run_dec5M`**: on every word of the support of the registry's real or uniform
  law, the output is `PMF.pure (true :: inst3Enc.enc (inst3Of w))`, resp.
  `PMF.pure (true :: (inst5Enc d).enc (inst5Of w))`; on any word at most `encLen` bits long it is
  the point mass at `decodeW …` (`run_decodeM`).
* `cost_dec3M_le`, `cost_dec5M_le`: the costs (`cost_decodeM_le`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW
  Cslib Cslib.Probability

/-! ### The explicit reindexing -/

/-- **The position in the explicit enumeration**, as an equivalence with `Fin |α|`. -/
def enumFin (α : Type) [Enum α] [Fintype α] [DecidableEq α] : α ≃ Fin (Fintype.card α) :=
  (List.Nodup.getEquivOfForallMemList (Enum.list (α := α)) Enum.nodup Enum.complete).symm.trans
    (finCongr (by
      simpa using Fintype.card_congr
        (List.Nodup.getEquivOfForallMemList (Enum.list (α := α)) Enum.nodup Enum.complete)))

theorem enumFin_apply {α : Type} [Enum α] [Fintype α] [DecidableEq α] (a : α) :
    (enumFin α a : ℕ) = Enum.index a := rfl

/-- The enumeration, reindexed, is `0, 1, …`. -/
theorem map_enumFin (α : Type) [Enum α] [Fintype α] [DecidableEq α] :
    (Enum.list (α := α)).map (enumFin α) = List.finRange (Fintype.card α) := by
  have hl : (Enum.list (α := α)).length = Fintype.card α := by
    simpa using Fintype.card_congr
      (List.Nodup.getEquivOfForallMemList (Enum.list (α := α)) Enum.nodup Enum.complete)
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_finRange]
  ext
  simp only [enumFin_apply, Enum.index, Fin.val_cast]
  exact List.get_idxOf Enum.nodup ⟨i, by simpa using h1⟩

theorem flatMap_enumFin {α β : Type} [Enum α] [Fintype α] [DecidableEq α]
    (g : Fin (Fintype.card α) → List β) :
    (Enum.list (α := α)).flatMap (fun a => g (enumFin α a)) =
      (List.finRange (Fintype.card α)).flatMap g := by
  rw [← map_enumFin α, List.flatMap_map]

/-! ### The words of the instances -/

variable {N K k : ℕ}

theorem matEnc_row {s : Type} [Enum s] (f : s → Rg N K) :
    (matEnc (N := N) (K := K) (Fin 1) s).enc (rowOf f) =
      (Enum.list (α := s)).flatMap fun c => (ringEnc N K).enc (f c) := by
  show (((List.finRange 1).map (rowOf f)).flatMap fun r =>
    ((Enum.list (α := s)).map r).flatMap (ringEnc N K).enc) = _
  show List.flatMap (fun r : s → Rg N K => ((Enum.list (α := s)).map r).flatMap (ringEnc N K).enc)
    [fun c => f c] = _
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map]

theorem matEnc_neg_row {s : Type} [Enum s] (f : s → Rg N K) :
    (matEnc (N := N) (K := K) (Fin 1) s).enc (-rowOf f) =
      (Enum.list (α := s)).flatMap fun c => (ringEnc N K).enc (-f c) := by
  rw [show -rowOf f = rowOf (fun c => -f c) by ext i c; simp [rowOf]]
  exact matEnc_row _

/-- **The word of a hybrid-3 instance**: the entries of `a`, then those of `b`, in the order of
`Col k`. -/
theorem inst3Enc_split3 (v : (Col k → Rg N K) × (Col k → Rg N K)) :
    (inst3Enc (N := N) (K := K) (k := k)).enc (split3 v) =
      (Enum.list (α := Col k)).flatMap (fun c => (ringEnc N K).enc (v.1 c)) ++
        (Enum.list (α := Col k)).flatMap (fun c => (ringEnc N K).enc (v.2 c)) := by
  show (matEnc (Fin 1) (Col k)).enc (rowOf v.1) ++ (matEnc (Fin 1) (Col k)).enc (rowOf v.2) = _
  rw [matEnc_row, matEnc_row]

/-- **The word of a hybrid-5 instance**: the negated public parts, then the values, each in the
order of `Idx5 (Fin d) k`. -/
theorem inst5Enc_split5 {d : ℕ}
    (v : (Idx5 (Fin d) k → Rg N K) × (Idx5 (Fin d) k → Rg N K)) :
    (inst5Enc (N := N) (K := K) (k := k) d).enc (split5 v) =
      (Enum.list (α := Idx5 (Fin d) k)).flatMap (fun i => (ringEnc N K).enc (-v.1 i)) ++
        (Enum.list (α := Idx5 (Fin d) k)).flatMap (fun i => (ringEnc N K).enc (v.2 i)) := by
  show ((matEnc (Fin 1) (Fin d)).enc (-rowOf fun c => v.1 (.inl c)) ++
      ((matEnc (Fin 1) (Col k)).enc (-rowOf fun c => v.1 (.inr (.inl c))) ++
        ((matEnc (Fin 1) (Col k)).enc (-rowOf fun c => v.1 (.inr (.inr (.inl c)))) ++
          (ringEnc N K).enc (-v.1 (.inr (.inr (.inr ()))))))) ++
    ((matEnc (Fin 1) (Fin d)).enc (rowOf fun c => v.2 (.inl c)) ++
      ((matEnc (Fin 1) (Col k)).enc (rowOf fun c => v.2 (.inr (.inl c))) ++
        ((matEnc (Fin 1) (Col k)).enc (rowOf fun c => v.2 (.inr (.inr (.inl c)))) ++
          (ringEnc N K).enc (v.2 (.inr (.inr (.inr ()))))))) = _
  simp only [matEnc_row, matEnc_neg_row]
  show _ = ((Enum.list (α := Fin d)).map Sum.inl ++ ((Enum.list (α := Col k)).map Sum.inl ++
      ((Enum.list (α := Col k)).map Sum.inl ++ [()].map Sum.inr).map Sum.inr).map Sum.inr).flatMap _ ++
    ((Enum.list (α := Fin d)).map Sum.inl ++ ((Enum.list (α := Col k)).map Sum.inl ++
      ((Enum.list (α := Col k)).map Sum.inl ++ [()].map Sum.inr).map Sum.inr).map Sum.inr).flatMap _
  simp [List.flatMap_append, List.flatMap_map, Function.comp_def]

/-! ### The instances of the registry's words -/

/-- The samples of hybrid 3. -/
abbrev m3 (k : ℕ) : ℕ := Fintype.card (Col k)

/-- The samples of hybrid 5. -/
abbrev m5 (k d : ℕ) : ℕ := Fintype.card (Idx5 (Fin d) k)

open Classical in
/-- **The instance of hybrid 3 (or of the ideal side) of a word**: the decoded pair, reindexed by
the enumeration of `Col k`, split (the zero instance for words that encode no pair). -/
noncomputable def inst3Of (w : List Bool) : Inst3T N K k :=
  if h : ∃ v : (Fin (m3 k) → Rg N K) × (Fin (m3 k) → Rg N K), encodeRing v = w then
    split3 (h.choose.1 ∘ enumFin (Col k), h.choose.2 ∘ enumFin (Col k))
  else 0

theorem inst3Of_encodeRing (v : (Fin (m3 k) → Rg N K) × (Fin (m3 k) → Rg N K)) :
    inst3Of (N := N) (K := K) (k := k) (encodeRing v) =
      split3 (v.1 ∘ enumFin (Col k), v.2 ∘ enumFin (Col k)) := by
  have h : ∃ v' : (Fin (m3 k) → Rg N K) × (Fin (m3 k) → Rg N K), encodeRing v' = encodeRing v :=
    ⟨v, rfl⟩
  unfold inst3Of
  rw [dite_eq_left_of_eq_true (eq_true h), encodeRing_injective h.choose_spec]

open Classical in
/-- **The instance of hybrid 5 of a word**: the decoded pair, reindexed by the enumeration of
`Idx5 (Fin d) k`, split (the public parts negated). -/
noncomputable def inst5Of (d : ℕ) (w : List Bool) :
    Pub (Fin d) (Rg N K) k × Pub (Fin d) (Rg N K) k :=
  if h : ∃ v : (Fin (m5 k d) → Rg N K) × (Fin (m5 k d) → Rg N K), encodeRing v = w then
    split5 (h.choose.1 ∘ enumFin (Idx5 (Fin d) k), h.choose.2 ∘ enumFin (Idx5 (Fin d) k))
  else 0

theorem inst5Of_encodeRing (d : ℕ) (v : (Fin (m5 k d) → Rg N K) × (Fin (m5 k d) → Rg N K)) :
    inst5Of (N := N) (K := K) (k := k) d (encodeRing v) =
      split5 (v.1 ∘ enumFin (Idx5 (Fin d) k), v.2 ∘ enumFin (Idx5 (Fin d) k)) := by
  have h : ∃ v' : (Fin (m5 k d) → Rg N K) × (Fin (m5 k d) → Rg N K), encodeRing v' = encodeRing v :=
    ⟨v, rfl⟩
  unfold inst5Of
  rw [dite_eq_left_of_eq_true (eq_true h), encodeRing_injective h.choose_spec]

/-- `wordDist` reads the instance `inst3Of`. -/
theorem wordDist_split3 (g : Inst3T N K k → PMF Bool)
    (v : (Fin (m3 k) → Rg N K) × (Fin (m3 k) → Rg N K)) :
    wordDist (enumFin (Col k)) (g ∘ split3) (encodeRing v) = g (inst3Of (encodeRing v)) := by
  rw [wordDist_encode, inst3Of_encodeRing]; rfl

/-- `wordDist` reads the instance `inst5Of`. -/
theorem wordDist_split5 (d : ℕ) (g : Pub (Fin d) (Rg N K) k × Pub (Fin d) (Rg N K) k → PMF Bool)
    (v : (Fin (m5 k d) → Rg N K) × (Fin (m5 k d) → Rg N K)) :
    wordDist (enumFin (Idx5 (Fin d) k)) (g ∘ split5) (encodeRing v) =
      g (inst5Of d (encodeRing v)) := by
  rw [wordDist_encode, inst5Of_encodeRing]; rfl

/-! ### The machines -/

variable (N K k) in
/-- **The decoding machine of hybrid 3 and of the ideal side.** -/
noncomputable def dec3M : Machine :=
  Tape.Prog.decodeM false K (2 * m3 k * N * K) (encLen (m3 k) N K)

variable (N K k) in
/-- **The decoding machine of hybrid 5**: the public parts negated. -/
noncomputable def dec5M (d : ℕ) : Machine :=
  Tape.Prog.decodeM true K (2 * m5 k d * N * K) (encLen (m5 k d) N K)

/-- **The decoding machine of hybrid 3 on an encoded pair**: `true`, then the word of the
instance. -/
theorem run_dec3M_encodeRing (v : (Fin (m3 k) → Rg N K) × (Fin (m3 k) → Rg N K)) :
    (dec3M N K k).run (encodeRing v) =
      PMF.pure (true :: (inst3Enc (N := N) (K := K) (k := k)).enc (inst3Of (encodeRing v))) := by
  rw [dec3M, Tape.Prog.run_decodeM _ _ _ _ _ (length_encodeRing_le v), decodeW_encodeRing,
    inst3Of_encodeRing, inst3Enc_split3]
  simp only [Bool.false_eq_true, ↓reduceIte, Function.comp_apply]
  rw [flatMap_enumFin (fun j => (ringEnc N K).enc (v.1 j)),
    flatMap_enumFin (fun j => (ringEnc N K).enc (v.2 j))]

/-- **The decoding machine of hybrid 5 on an encoded pair.** -/
theorem run_dec5M_encodeRing (d : ℕ) (v : (Fin (m5 k d) → Rg N K) × (Fin (m5 k d) → Rg N K)) :
    (dec5M N K k d).run (encodeRing v) =
      PMF.pure (true :: (inst5Enc (N := N) (K := K) (k := k) d).enc (inst5Of d (encodeRing v))) := by
  rw [dec5M, Tape.Prog.run_decodeM _ _ _ _ _ (length_encodeRing_le v), decodeW_encodeRing,
    inst5Of_encodeRing, inst5Enc_split5]
  simp only [↓reduceIte, Function.comp_apply]
  rw [flatMap_enumFin (fun j => (ringEnc N K).enc (-v.1 j)),
    flatMap_enumFin (fun j => (ringEnc N K).enc (v.2 j))]

/-- The words of the registry's real and uniform laws are encoded pairs. -/
theorem mem_range_encodeRing (p : RingLWE.Params) {w : List Bool}
    (hw : haveI : NeZero p.q := ⟨p.q_pos.ne'⟩
      w ∈ (ModuleLWE.realLaw p.toModule).support ∨ w ∈ (ModuleLWE.idealLaw p.toModule).support) :
    haveI : NeZero p.q := ⟨p.q_pos.ne'⟩
    ∃ v : (Fin p.m → Negacyclic (ZMod p.q) p.N) × (Fin p.m → Negacyclic (ZMod p.q) p.N),
      encodeRing v = w := by
  have : NeZero p.q := ⟨p.q_pos.ne'⟩
  rcases hw with hw | hw
  · rw [ringLWE_realLaw_eq, PMF.support_map] at hw
    obtain ⟨v, -, rfl⟩ := hw
    exact ⟨v, rfl⟩
  · rw [ringLWE_idealLaw_eq, PMF.support_map] at hw
    obtain ⟨v, -, rfl⟩ := hw
    exact ⟨v, rfl⟩

/-- **The decoding machine of hybrid 3, in the form of `hP`** (`acceptProb_reduction`): on every
word of the support of the registry's real or uniform law of `params3`, the point mass at the
marker `true` followed by the word of the instance `inst3Of w`. -/
theorem run_dec3M (err : SecretDist) (w : List Bool)
    (hw : w ∈ (ModuleLWE.realLaw (params3 N (2 ^ K) k err).toModule).support ∨
      w ∈ (ModuleLWE.idealLaw (params3 N (2 ^ K) k err).toModule).support) :
    (dec3M N K k).run w =
      PMF.pure (true :: (inst3Enc (N := N) (K := K) (k := k)).enc (inst3Of w)) := by
  obtain ⟨v, rfl⟩ := mem_range_encodeRing (params3 N (2 ^ K) k err) hw
  exact run_dec3M_encodeRing (N := N) (K := K) (k := k) v

/-- **The decoding machine of hybrid 5, in the form of `hP`.** -/
theorem run_dec5M (d : ℕ) (err : SecretDist) (w : List Bool)
    (hw : w ∈ (ModuleLWE.realLaw (params5 N (2 ^ K) k (Fin d) err).toModule).support ∨
      w ∈ (ModuleLWE.idealLaw (params5 N (2 ^ K) k (Fin d) err).toModule).support) :
    (dec5M N K k d).run w =
      PMF.pure (true :: (inst5Enc (N := N) (K := K) (k := k) d).enc (inst5Of d w)) := by
  have h1 : ∃ v : (Fin (m5 k d) → Rg N K) × (Fin (m5 k d) → Rg N K), encodeRing v = w :=
    mem_range_encodeRing (params5 N (2 ^ K) k (Fin d) err) hw
  obtain ⟨v, rfl⟩ := h1
  exact run_dec5M_encodeRing d v

/-! ### Costs -/

theorem cost_dec3M_le :
    (dec3M N K k).cost ≤ 500 * (encLen (m3 k) N K + K + 2 * m3 k * N * K + 9) ^ 3 +
      6 * 3 ^ 13 * (60 * (K + 2 * m3 k * N * K) + 5518) * (60 * (K + 2 * m3 k * N * K) + 5574) :=
  Tape.Prog.cost_decodeM_le _ _ _ _

theorem cost_dec5M_le (d : ℕ) :
    (dec5M N K k d).cost ≤ 500 * (encLen (m5 k d) N K + K + 2 * m5 k d * N * K + 9) ^ 3 +
      6 * 3 ^ 13 * (60 * (K + 2 * m5 k d * N * K) + 5518) *
        (60 * (K + 2 * m5 k d * N * K) + 5574) :=
  Tape.Prog.cost_decodeM_le _ _ _ _

/-! ### The registry's words, reindexed by the enumerations -/

/-- **Real words of hybrid 3**, reindexed by `enumFin`. -/
theorem real3_wordE (err : SecretDist) (g : Inst3 N (2 ^ K) k → PMF Bool) :
    (ModuleLWE.realLaw (params3 N (2 ^ K) k err).toModule).bind
        (wordDist (enumFin (Col k) : Col k ≃ Fin (params3 N (2 ^ K) k err).m) (g ∘ split3)) =
      (inst3Real (polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err))).bind g := by
  rw [inst3Real_eq, PMF.bind_map]
  exact realLaw_bind_wordDist (params3 N (2 ^ K) k err) (enumFin (Col k)) _

/-- **Uniform words of hybrid 3**, reindexed by `enumFin`. -/
theorem unif3_wordE (err : SecretDist) (g : Inst3 N (2 ^ K) k → PMF Bool) :
    (ModuleLWE.idealLaw (params3 N (2 ^ K) k err).toModule).bind
        (wordDist (enumFin (Col k) : Col k ≃ Fin (params3 N (2 ^ K) k err).m) (g ∘ split3)) =
      inst3Unif.bind g := by
  rw [inst3Unif_eq, PMF.bind_map]
  exact idealLaw_bind_wordDist (params3 N (2 ^ K) k err) (enumFin (Col k)) _

/-- **Real words of hybrid 5**, reindexed by `enumFin`. -/
theorem real5_wordE (d : ℕ) (err : SecretDist)
    (g : Pub (Fin d) (Rg N K) k × Pub (Fin d) (Rg N K) k → PMF Bool) :
    (ModuleLWE.realLaw (params5 N (2 ^ K) k (Fin d) err).toModule).bind
        (wordDist (enumFin (Idx5 (Fin d) k) : Idx5 (Fin d) k ≃ Fin (params5 N (2 ^ K) k (Fin d) err).m)
          (g ∘ split5)) =
      (nfReal (Wd := Fin d) (k := k) (polyOf (N := N) (ModuleLWE.coeffLaw (2 ^ K) err))).bind g := by
  rw [nfReal_eq, PMF.bind_map]
  exact realLaw_bind_wordDist (params5 N (2 ^ K) k (Fin d) err) (enumFin (Idx5 (Fin d) k)) _

/-- **Uniform words of hybrid 5**, reindexed by `enumFin`. -/
theorem unif5_wordE (d : ℕ) (err : SecretDist)
    (g : Pub (Fin d) (Rg N K) k × Pub (Fin d) (Rg N K) k → PMF Bool) :
    (ModuleLWE.idealLaw (params5 N (2 ^ K) k (Fin d) err).toModule).bind
        (wordDist (enumFin (Idx5 (Fin d) k) : Idx5 (Fin d) k ≃ Fin (params5 N (2 ^ K) k (Fin d) err).m)
          (g ∘ split5)) =
      nfUnif.bind g := by
  rw [nfUnif_eq, PMF.bind_map]
  exact idealLaw_bind_wordDist (params5 N (2 ^ K) k (Fin d) err) (enumFin (Idx5 (Fin d) k)) _

end AdvancedEncryption.DualUse.Prog
