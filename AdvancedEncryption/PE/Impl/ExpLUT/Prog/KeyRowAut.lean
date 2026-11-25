import PE.Impl.ExpLUT.Prog.KeyGather

/-! Bounded automorphism exponents and executable gathering of public coefficients. -/
namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- An automorphism index represented by a template shorter than `2N`. -/
def rowExponent (D : Dims) (i : ℕ) : ℕ := gD D ^ i % (2 * D.N)

theorem rowExponent_odd (D : Dims) (i : ℕ) : Odd (rowExponent D i) := by
  rw [rowExponent, Nat.odd_iff, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 D.N)]
  exact Nat.odd_iff.mp ((odd_gD D).pow)

theorem rowExponent_pos (D : Dims) (i : ℕ) : 0 < rowExponent D i :=
  (rowExponent_odd D i).pos

theorem rowExponent_lt (D : Dims) (i : ℕ) : rowExponent D i < 2 * D.N :=
  Nat.mod_lt _ (by have := D.N_pos; omega)

theorem aut_rowExponent (D : Dims) (i : ℕ) (a : Rg D) :
    aut D.N (rowExponent D i) a = (setting D).E.σ ((setting D).idx i) a := by
  rw [rowExponent, aut_mod_two_n]
  change aut D.N (gD D ^ i) a = autσ D.N (gD D ^ i) a
  exact (autσ_of_odd ((odd_gD D).pow) a).symm

/-- Install the two bounded counters and apply the automorphism to the gathered queue. -/
def autGatheredC (n k : ℕ) : Code := .seq (.cp rQa 4) <|
  .seq (natC rQc rB1 n) <| .seq (natC rQk rB1 k) <|
  .seq autQC (.cp 4 rQa)

theorem wf_autGatheredC (n k : ℕ) : (autGatheredC n k).WFc := by
  refine ⟨trivial, natC_wfc _ _ _, natC_wfc _ _ _, ?_, trivial⟩
  simp [autQC, autQBody, Code.WFc, Code.writes]

theorem exec_autGatheredC {N K : ℕ} (hN : 0 < N) (hK : 0 < K)
    (k : ℕ) (hk : 0 < k) (w : St) (xs : List (Rq N K))
    (hX : w 4 = encL N K xs) (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) :
    exec N K (autGatheredC xs.length k) w 4 = encL N K (xs.map (aut N k)) := by
  rw [autGatheredC, exec_seq]
  rw [exec_seq, exec_natC _ _ (by decide) _ _ (by simpa using h1)]
  rw [exec_seq, exec_natC _ _ (by decide) _ _ (by simpa using h1)]
  rw [exec_seq, exec_cp, Function.update_self]
  apply exec_autQC hN hK _ xs xs.length k hk rfl
  · simpa using hX
  · simp
  · simp
  · simpa using hZ

/-- Static coordinate extraction followed by a bounded automorphism. -/
def gatherAutC (N K k : ℕ) (js : List ℕ) : Code :=
  .seq (gatherC N K js) (autGatheredC js.length k)

theorem wf_gatherAutC (N K k : ℕ) (js : List ℕ) : (gatherAutC N K k js).WFc :=
  ⟨wf_gatherC _ _ _, wf_autGatheredC _ _⟩

theorem gatherC_preserves (N K : ℕ) (js : List ℕ) (i : Fin 64)
    (h1 : i ≠ 1) (h2 : i ≠ 2) (h3 : i ≠ 3) (h4 : i ≠ 4) :
    (gatherC N K js).writes i = false := by
  simp [gatherC, Code.writes, Ne.symm h4, gatherAppendC_preserves N K i h1 h2 h3 h4 js]

/-- The coefficient queue is generated from encoded source data by VM instructions. -/
theorem exec_gatherAutC_family {N K : ℕ} (hN : 0 < N) (hK : 0 < K)
    (k : ℕ) (hk : 0 < k) {α : Type} [Enum α] [DecidableEq α]
    (f : α → Rq N K) (is : List α) (w : St)
    (hS : w 0 = encL N K (Enum.list.map f))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM N K 0) :
    exec N K (gatherAutC N K k (is.map Enum.index)) w 4 =
      encL N K (is.map (fun a ↦ aut N k (f a))) := by
  rw [gatherAutC, exec_seq]
  have h := exec_autGatheredC hN hK k hk
    (exec N K (gatherC N K (is.map Enum.index)) w) (is.map f)
    (exec_gatherC_family f is w hS h1 hZ)
    (by rw [exec_writes _ _ _ (gatherC_preserves _ _ _ rB1 (by decide) (by decide) (by decide) (by decide)), h1])
    (by rw [exec_writes _ _ _ (gatherC_preserves _ _ _ rZ (by decide) (by decide) (by decide) (by decide)), hZ])
  simpa only [List.length_map, List.map_map, Function.comp_def] using h

/-- Gathered public coefficients use the scheme's automorphism with a bounded template. -/
theorem exec_gatherRowAut_family (D : Dims) (i : ℕ)
    {α : Type} [Enum α] [DecidableEq α] (f : α → Rg D) (is : List α) (w : St)
    (hS : w 0 = encL D.N D.K (Enum.list.map f))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (gatherAutC D.N D.K (rowExponent D i) (is.map Enum.index)) w 4 =
      encL D.N D.K (is.map (fun a ↦ (setting D).E.σ ((setting D).idx i) (f a))) := by
  simpa only [aut_rowExponent] using
    exec_gatherAutC_family D.N_pos D.K_pos (rowExponent D i) (rowExponent_pos D i)
      f is w hS h1 hZ

/-- The correction kernel can use the bounded exponent rather than a raw exponential template. -/
theorem exec_autDotC_corrected_bounded (D : Dims)
    (T : Matrix (Wb D) (Fin D.K) (Rg D))
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (z : ZIdx (setting D).τ (setting D).E.W → Rg D)
    (i : Fin (setting D).E.W) (row : Wb D) (w : St)
    (hA : w rQa = encL D.N D.K (List.ofFn (T row)))
    (hB : w rQb = encL D.N D.K (List.ofFn (fun c : Fin D.K ↦ z (i, c))))
    (hC : w rQc = List.replicate D.K false)
    (hQk : w rQk = List.replicate (rowExponent D i.val) false)
    (hI : w rIa = encRM D.N D.K (p (.inl (i, row))))
    (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K autDotC w rIa = encRM D.N D.K
      ((p - realTrap (S := setting D) (J := Jh D) T z) (.inl (i, row))) ∧
    exec D.N D.K autDotC w rQa = [] ∧ exec D.N D.K autDotC w rQb = [] := by
  have h := exec_autDotC D.N_pos D.K_pos w (List.ofFn (T row))
    (List.ofFn (fun c : Fin D.K ↦ z (i, c))) D.K (rowExponent D i.val)
    (rowExponent_pos D i.val) (p (.inl (i, row))) (by simp) (by simp) hA hB hC hQk hI hZ
  rw [zip_aut_ofFn] at h
  simp only [rowExponent, aut_mod_two_n] at h
  rw [← corrected_inl D T p z i row] at h
  exact h

/-- Encoded B/H entries in their explicit product/sum enumeration. -/
abbrev BHSource (D : Dims) :=
  (Fin 2 × (Wb D ⊕ Fin (setting D).τ)) ⊕ (Jh D × Fin 2 × Col (setting D).τ)

abbrev BHRow (D : Dims) := Wb D ⊕ (Jh D × Col (setting D).τ)

def bhSource (D : Dims) (mpk : MPKt D) : BHSource D → Rg D
  | .inl (row, c) => mpk.B row c
  | .inr (k, row, c) => mpk.H k row c

def bhSelection (D : Dims) : BHRow D → BHSource D
  | .inl w => .inl (0, .inl w)
  | .inr (k, c) => .inr (k, 0, c)

open Classical in
noncomputable def gatherBHC (D : Dims) (i : ℕ) : Code :=
  gatherAutC D.N D.K (rowExponent D i) (Enum.list.map (Enum.index ∘ bhSelection D))

/-- The actual generated B/H coefficient stream for a public-map row. -/
theorem exec_gatherBHC (D : Dims) (i : ℕ) (mpk : MPKt D) (w : St)
    (hS : w 0 = encL D.N D.K (Enum.list.map (bhSource D mpk)))
    (h1 : w rB1 = [false]) (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K (gatherBHC D i) w 4 = encL D.N D.K
      (Enum.list.map (fun t : BHRow D ↦ (setting D).E.σ ((setting D).idx i)
        (bhSource D mpk (bhSelection D t)))) := by
  classical
  have h := exec_gatherRowAut_family D i (bhSource D mpk)
    (Enum.list.map (bhSelection D)) w hS h1 hZ
  simpa only [gatherBHC, List.map_map, Function.comp_def] using h

theorem wf_gatherBHC (D : Dims) (i : ℕ) : (gatherBHC D i).WFc :=
  wf_gatherAutC _ _ _ _

end AdvancedEncryption.ExpLUT.Prog
