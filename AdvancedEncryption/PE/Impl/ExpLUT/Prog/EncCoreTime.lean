import PE.Impl.ExpLUT.Prog.EncLoopTime

/-! # Clock of the complete deterministic encryption core in any tape bank -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Params

/-- Compose tape placements before expanding the large literal programs. -/
theorem map_map_enc {a b c : ℕ} (u : Fin a → Fin b) (v : Fin b → Fin c)
    (p : SigabaNeo.Tape.Prog a) : map v (map u p) = map (v ∘ u) p := by
  induction p with
  | prim p => cases p <;> rfl
  | coin i => rfl
  | seq p q hp hq => simp only [map, hp, hq]
  | ifBlank i p q hp hq => simp only [map, hp, hq, Function.comp_apply]
  | ifBit i p q hp hq => simp only [map, hp, hq, Function.comp_apply]
  | loop i p hp => simp only [map, hp, Function.comp_apply]

theorem map_seq_enc {n k : ℕ} (u : Fin n → Fin k) (p q : SigabaNeo.Tape.Prog n) :
    map u (.seq p q) = .seq (map u p) (map u q) := rfl

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_cin_mapped {k : ℕ} (u : Fin 104 → Fin k) {ℓ : Fin k → ℕ}
    (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) (hn : ℓ (u 35) ≤ 16) :
    timeBoundT (map u cinP) ℓ ≤ 2 ^ 811 := by
  have h := time_forN_noGrow (map u cinBody) ((show cinBody.NoGrow from rfl).map u)
    (u 39) (u 35) hℓ hn
  have hc : cinBody.tbC = 9925 := congrArg Prod.fst degrees_cinBody
  have hd : cinBody.tbD = 8 := congrArg Prod.snd degrees_cinBody
  rw [tbC_map, tbD_map, hc, hd] at h
  exact h.trans (by norm_num)

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_cinbot_mapped {k : ℕ} (u : Fin 104 → Fin k) {ℓ : Fin k → ℕ}
    (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) (hn : ℓ (u 35) ≤ 16) :
    timeBoundT (map u cinbotP) ℓ ≤ 2 ^ 613 := by
  have h := time_forN_noGrow (map u (map tCb1 cbP))
    ((show (map tCb1 cbP).NoGrow from rfl).map u) (u 39) (u 35) hℓ hn
  have hc : (map tCb1 cbP).tbC = 4998 := congrArg Prod.fst degrees_cinbotBody
  have hd : (map tCb1 cbP).tbD = 6 := congrArg Prod.snd degrees_cinbotBody
  rw [tbC_map, tbD_map, hc, hd] at h
  exact h.trans (by norm_num)

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_tailEnd_mapped {k : ℕ} (u : Fin 104 → Fin k) {ℓ : Fin k → ℕ}
    (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) : timeBoundT (map u (.seq c0P cmP)) ℓ ≤ 2 ^ 609 := by
  have hc : (SigabaNeo.Tape.Prog.seq c0P cmP).tbC = 8976 := congrArg Prod.fst degrees_tailEnd
  have hd : (SigabaNeo.Tape.Prog.seq c0P cmP).tbD = 6 := congrArg Prod.snd degrees_tailEnd
  exact (mapped_poly (.seq c0P cmP) (by rfl) (by rw [hc, hd]; norm_num) k u ℓ hℓ).1

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem time_tail_mapped {k : ℕ} (u : Fin 104 → Fin k) (hu : Function.Injective u)
    {ℓ : Fin k → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) (hn : ℓ (u 35) ≤ 16) :
    timeBoundT (map u tailP) ℓ ≤ 2 ^ 812 := by
  have h1 := time_cinbot_mapped u hℓ hn
  have hl1 := Sym.lenBoundT_le_const (map u cinbotP) ((show cinbotP.NoGrow from rfl).map u) hℓ
  have hn1 : lenBoundT (map u cinbotP) ℓ (u 35) ≤ 16 := by
    rw [lenBoundT_of_preserves _ _ ((preserves_map hu 35 cinbotP).mpr cinbot_preserves_count)]
    exact hn
  have h2 := time_cin_mapped u hl1 hn1
  have hl2 := Sym.lenBoundT_le_const (map u cinP) ((show cinP.NoGrow from rfl).map u) hl1
  have h3 := time_tailEnd_mapped u hl2
  exact (Nat.add_le_add h1 (Nat.add_le_add h2 h3)).trans (by norm_num)

/-- A phase disjoint from the attribute-count template leaves its bound untouched. -/
theorem count_after_map {n k : ℕ} (u : Fin 321 → Fin k) (hu : Function.Injective u)
    (v : Fin n → Fin 321) (hv : ∀ i, v i ≠ tailSlot 35)
    (p : SigabaNeo.Tape.Prog n) (ℓ : Fin k → ℕ) :
    lenBoundT (map (u ∘ v) p) ℓ (u (tailSlot 35)) = ℓ (u (tailSlot 35)) :=
  lenBoundT_of_preserves _ _ (preserves_map_of_not_mem
    (fun i he => hv i (hu he)) p) ℓ

/-- Compose three length-bounded phases and a final phase with a preserved counter. -/
theorem phase_four {k : ℕ} (p q r s : SigabaNeo.Tape.Prog k) (c : Fin k)
    {T U V W : ℕ} (hp : PhaseBound p T) (hq : PhaseBound q U) (hr : PhaseBound r V)
    (hpc : p.Preserves c) (hqc : q.Preserves c) (hrc : r.Preserves c)
    (hs : ∀ ℓ, (∀ i, ℓ i ≤ 2 ^ 99) → ℓ c ≤ 16 →
      timeBoundT s ℓ ≤ W ∧ ∀ i, lenBoundT s ℓ i ≤ 2 ^ 99)
    {ℓ : Fin k → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) (hn : ℓ c ≤ 16) :
    timeBoundT (.seq p (.seq q (.seq r s))) ℓ ≤ T + (U + (V + W)) ∧
      ∀ i, lenBoundT (.seq p (.seq q (.seq r s))) ℓ i ≤ 2 ^ 99 := by
  have h1 := hp ℓ hℓ
  have h2 := hq _ h1.2
  have h3 := hr _ h2.2
  have hn3 : lenBoundT r (lenBoundT q (lenBoundT p ℓ)) c ≤ 16 := by
    rw [lenBoundT_of_preserves _ _ hrc, lenBoundT_of_preserves _ _ hqc,
      lenBoundT_of_preserves _ _ hpc]
    exact hn
  have h4 := hs _ h3.2 hn3
  exact ⟨Nat.add_le_add h1.1 (Nat.add_le_add h2.1 (Nat.add_le_add h3.1 h4.1)), h4.2⟩

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
/-- The actual four-phase core costs at most `2^814`, including all 22 helper/aut rounds. -/
theorem time_core_mapped {k : ℕ} (u : Fin 321 → Fin k) (hu : Function.Injective u)
    {ℓ : Fin k → ℕ} (hℓ : ∀ i, ℓ i ≤ 2 ^ 99) (hn : ℓ (u (tailSlot 35)) ≤ 16) :
    timeBoundT (map u (encCoreP Dc)) ℓ ≤ 2 ^ 814 ∧
      ∀ i, lenBoundT (map u (encCoreP Dc)) ℓ i ≤ 2 ^ 99 := by
  have hc : mrowP.tbC = 4356 := congrArg Prod.fst degrees_mrow
  have hd : mrowP.tbD = 6 := congrArg Prod.snd degrees_mrow
  have b1 : PhaseBound (map (u ∘ bSlot) mrowP) (2 ^ 608) :=
    mapped_poly _ noGrow_mrowP (by rw [hc, hd]; norm_num) k _
  have b2 := mapped_helperPairs 0 22 (by omega) k (u ∘ helperSlot)
  have b3 := mapped_autBlocks 0 22 (by omega) k (u ∘ autSlot)
  have pc1 : (map (u ∘ bSlot) mrowP).Preserves (u (tailSlot 35)) :=
    preserves_map_of_not_mem (fun i he =>
      phaseSlot_separate (by decide) (by decide) (by decide) i (35 : Fin 104) (by decide) (hu he)) _
  have pc2 : (map (u ∘ helperSlot) (helperPairsP Dc 0 22)).Preserves (u (tailSlot 35)) :=
    preserves_map_of_not_mem (fun i he =>
      phaseSlot_separate (by decide) (by decide) (by decide) i (35 : Fin 104) (by decide) (hu he)) _
  have pc3 : (map (u ∘ autSlot) (autBlocksP Dc 0 22)).Preserves (u (tailSlot 35)) :=
    preserves_map_of_not_mem (fun i he =>
      phaseSlot_separate (by decide) (by decide) (by decide) i (35 : Fin 104) (by decide) (hu he)) _
  have hs : ∀ a : Fin k → ℕ, (∀ i, a i ≤ 2 ^ 99) → a (u (tailSlot 35)) ≤ 16 →
      timeBoundT (map (u ∘ tailSlot) tailP) a ≤ 2 ^ 812 ∧
        ∀ i, lenBoundT (map (u ∘ tailSlot) tailP) a i ≤ 2 ^ 99 :=
    fun a ha hn => ⟨time_tail_mapped _ (hu.comp tailSlot_inj) ha hn,
      Sym.lenBoundT_le_const _ (noGrow_tailP.map _) ha⟩
  have h := phase_four _ _ _ _ _ b1 b2 b3 pc1 pc2 pc3 hs hℓ hn
  simp only [encCoreP, map_seq_enc, map_map_enc]
  exact ⟨h.1.trans (by norm_num), h.2⟩

end AdvancedEncryption.ExpLUT.Prog.EncW
