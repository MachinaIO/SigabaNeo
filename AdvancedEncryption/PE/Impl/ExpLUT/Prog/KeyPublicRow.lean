import PE.Impl.ExpLUT.Prog.KeyShift

/-! Sparse public-map rows and their signed inner-product execution kernel. -/
namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices

/-- Only the unique predecessor row contributes each helper's negative gadget term. -/
theorem pubShort_backRow {R : Type*} [CommRing R] {S : Setting R}
    {Wb J Pos : Type*} [Fintype Wb] [Fintype J] [DecidableEq Wb] [DecidableEq J]
    (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (p : PIdx Wb J S.τ S.E.W → R) (i : Fin S.E.W) :
    pubShort M mpk F p i =
      (∑ w, S.E.σ (S.idx i) (mpk.B 0 (.inl w)) * p (.inl (i, w))) +
      (∑ k, ∑ c, S.E.σ (S.idx i) (mpk.H k 0 c) * p (.inr (.inl (i, k, c)))) -
      (∑ k, ∑ c, S.G 0 c * p (.inr (.inl (M.backRow i k, k, c)))) +
      (if i = S.row0 then ∑ c, keyPK M mpk F 0 c * p (.inr (.inr c)) else 0) := by
  rw [pubShort_apply]
  congr 2
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact sum_mulRow M i k _

namespace Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo (encRM)

/-- Input registers 10/11/12 hold the negative row pair and its length.
Register 13 saves the positive product while the same kernel computes the negative product. -/
def signedDotC : Code := .seq (.cp rIa rZ) <| .seq ipC <|
  .seq (.cp 13 rIa) <| .seq (.cp rQa 10) <| .seq (.cp rQb 11) <|
  .seq (.cp rQc 12) <| .seq (.cp rIa rZ) <|
  .seq ipC (.op .sub rIa 13 rIa)

theorem wf_signedDotC : signedDotC.WFc := by
  simp [signedDotC, ipC, ipBody, Code.WFc, Code.writes]

/-- The executable signed inner product used to combine positive and negative public-row terms. -/
theorem exec_signedDotC {N K : ℕ} (hK : 0 < K) (w : St)
    (a b c d : List (Rq N K)) (n m : ℕ)
    (ha : a.length = n) (hb : b.length = n) (hc : c.length = m) (hd : d.length = m)
    (hA : w rQa = encL N K a) (hB : w rQb = encL N K b)
    (hC : w 10 = encL N K c) (hD : w 11 = encL N K d)
    (hn : w rQc = List.replicate n false) (hm : w 12 = List.replicate m false)
    (hZ : w rZ = encRM N K 0) :
    exec N K signedDotC w rIa =
      encRM N K ((List.zipWith (· * ·) a b).sum - (List.zipWith (· * ·) c d).sum) := by
  let w0 := exec N K (.cp rIa rZ) w
  have f0 : ∀ i : Fin 64, i ≠ rIa → w0 i = w i :=
    fun i hi ↦ Function.update_of_ne hi _ _
  have hpos := (exec_ipC hK w0 a b [] [] n 0 ha hb
    (by simpa using (f0 _ (by decide)).trans hA)
    (by simpa using (f0 _ (by decide)).trans hB)
    ((f0 _ (by decide)).trans hn) hZ ((f0 _ (by decide)).trans hZ)).1
  simp only [zero_add] at hpos
  let w1 := exec N K ipC w0
  let load : Code := .seq (.cp 13 rIa) <| .seq (.cp rQa 10) <| .seq (.cp rQb 11) <|
    .seq (.cp rQc 12) (.cp rIa rZ)
  let w2 := exec N K load w1
  have f1 : ∀ i : Fin 64, ipC.writes i = false → i ≠ rIa → w1 i = w i := by
    intro i hi hi'
    change exec N K ipC w0 i = _
    rw [exec_writes _ _ _ hi, f0 i hi']
  have inputs : w2 rQa = encL N K c ∧ w2 rQb = encL N K d ∧
      w2 rQc = List.replicate m false ∧ w2 rIa = encRM N K 0 ∧
      w2 rZ = encRM N K 0 ∧ w2 13 = encRM N K (List.zipWith (· * ·) a b).sum := by
    have t10 := (f1 10 (by decide) (by decide)).trans hC
    have t11 := (f1 11 (by decide) (by decide)).trans hD
    have t12 := (f1 12 (by decide) (by decide)).trans hm
    have tz := (f1 rZ (by decide) (by decide)).trans hZ
    dsimp [w2, load]; vm_simp
    simp [t10, t11, t12, tz, show w1 rIa = _ from hpos]
  have hneg := (exec_ipC hK w2 c d [] [] m 0 hc hd
    (by simpa using inputs.1) (by simpa using inputs.2.1) inputs.2.2.1
    inputs.2.2.2.1 inputs.2.2.2.2.1).1
  simp only [zero_add] at hneg
  have saved : exec N K ipC w2 13 = encRM N K (List.zipWith (· * ·) a b).sum := by
    rw [exec_writes _ _ _ (by decide), inputs.2.2.2.2.2]
  change exec N K (.op .sub rIa 13 rIa) (exec N K ipC w2) rIa = _
  vm_simp
  simp [saved, hneg, canonW_sub hK]

/-- Row-stream indices omit the zero blocks of the full key matrix. -/
abbrev PublicPos (Wb J : Type) (τ : ℕ) := Wb ⊕ (J × Col τ) ⊕ Col τ

section Streams
variable {R : Type} [CommRing R] {S : Setting R} {Wb J Pos : Type}
  [Fintype Wb] [Fintype J] [DecidableEq Wb] [DecidableEq J]

noncomputable def publicPosCoeff (M : HelperMap S J) (mpk : MPK S Wb J Pos)
    (F : BP Pos) (i : Fin S.E.W) : PublicPos Wb J S.τ → R
  | .inl w => S.E.σ (S.idx i) (mpk.B 0 (.inl w))
  | .inr (.inl (k, c)) => S.E.σ (S.idx i) (mpk.H k 0 c)
  | .inr (.inr c) => if i = S.row0 then keyPK M mpk F 0 c else 0

def publicPosInput (p : PIdx Wb J S.τ S.E.W → R) (i : Fin S.E.W) : PublicPos Wb J S.τ → R
  | .inl w => p (.inl (i, w))
  | .inr (.inl (k, c)) => p (.inr (.inl (i, k, c)))
  | .inr (.inr c) => p (.inr (.inr c))

noncomputable def publicNegCoeff : J × Col S.τ → R := fun kc ↦ S.G 0 kc.2

def publicNegInput (M : HelperMap S J) (p : PIdx Wb J S.τ S.E.W → R)
    (i : Fin S.E.W) : J × Col S.τ → R :=
  fun kc ↦ p (.inr (.inl (M.backRow i kc.1, kc.1, kc.2)))

theorem public_signed_sum (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (p : PIdx Wb J S.τ S.E.W → R) (i : Fin S.E.W) :
    (∑ t, publicPosCoeff M mpk F i t * publicPosInput p i t) -
      (∑ t, publicNegCoeff (S := S) t * publicNegInput M p i t) = pubShort M mpk F p i := by
  rw [pubShort_backRow]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, publicPosCoeff, publicPosInput,
    publicNegCoeff, publicNegInput, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  ring
end Streams

/-- An inner product of explicitly enumerated streams is the finite algebraic inner product. -/
theorem zip_enum_sum {α R : Type} [Enum α] [Fintype α] [DecidableEq α] [CommRing R]
    (a b : α → R) :
    (List.zipWith (· * ·) (Enum.list.map a) (Enum.list.map b)).sum = ∑ t, a t * b t := by
  have he : List.zipWith (· * ·) (Enum.list.map a) (Enum.list.map b) =
      Enum.list.map (fun t ↦ a t * b t) := by
    apply List.ext_getElem
    · simp
    · intro j hj hj'; simp
  rw [he, ← List.sum_toFinset _ Enum.nodup]
  have hu : (Enum.list (α := α)).toFinset = Finset.univ := by
    ext t; simp [Enum.complete t]
  rw [hu]

/-- The sparse stream representation has exactly the public-map semantics. -/
theorem public_streams_eq {R : Type} [CommRing R] {S : Setting R} {Wb J Pos : Type}
    [Fintype Wb] [Fintype J] [DecidableEq Wb] [DecidableEq J] [Enum Wb] [Enum J]
    (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (p : PIdx Wb J S.τ S.E.W → R) (i : Fin S.E.W) :
    (List.zipWith (· * ·) (Enum.list.map (publicPosCoeff M mpk F i))
      (Enum.list.map (publicPosInput p i))).sum -
    (List.zipWith (· * ·) (Enum.list.map (publicNegCoeff (S := S) (J := J)))
      (Enum.list.map (publicNegInput M p i))).sum = pubShort M mpk F p i := by
  rw [zip_enum_sum, zip_enum_sum, public_signed_sum]

/-- The VM signed-product kernel computes an actual public-map row from its sparse streams. -/
theorem exec_signedDotC_public (D : Dims) (w : St) (mpk : MPKt D) (F : BP Pos)
    (p : PIdx (Wb D) (Jh D) (setting D).τ (setting D).E.W → Rg D)
    (i : Fin (setting D).E.W)
    (hA : w rQa = encL D.N D.K (Enum.list.map (publicPosCoeff (helperMap D) mpk F i)))
    (hB : w rQb = encL D.N D.K (Enum.list.map (publicPosInput p i)))
    (hC : w 10 = encL D.N D.K (Enum.list.map (publicNegCoeff (S := setting D) (J := Jh D))))
    (hD : w 11 = encL D.N D.K (Enum.list.map (publicNegInput (helperMap D) p i)))
    (hn : w rQc = List.replicate (Enum.list (α := PublicPos (Wb D) (Jh D) (setting D).τ)).length false)
    (hm : w 12 = List.replicate (Enum.list (α := Jh D × Col (setting D).τ)).length false)
    (hZ : w rZ = encRM D.N D.K 0) :
    exec D.N D.K signedDotC w rIa = encRM D.N D.K (pubShort (helperMap D) mpk F p i) := by
  have h := exec_signedDotC D.K_pos w
    (Enum.list.map (publicPosCoeff (helperMap D) mpk F i)) (Enum.list.map (publicPosInput p i))
    (Enum.list.map (publicNegCoeff (S := setting D) (J := Jh D)))
    (Enum.list.map (publicNegInput (helperMap D) p i)) _ _
    (List.length_map ..) (List.length_map ..) (List.length_map ..) (List.length_map ..)
    hA hB hC hD hn hm hZ
  exact h.trans (congrArg (encRM D.N D.K) (public_streams_eq (helperMap D) mpk F p i))

end Prog
end AdvancedEncryption.ExpLUT
