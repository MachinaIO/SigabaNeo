import PE.Impl.DualUse.Prog.Layout
import SigabaNeo.Lib.Encode.Laws
import SigabaNeo.Lib.Machines.Prog.Sample

/-!
# The laws of the encoded secrets

The words of the secrets of the reductions, under their laws, as concatenations of independent
blocks of *coefficient words*:

* `μB N K`: the word of a binary ring element `bitVal b` for a fair `b`: one fair bit, then
  `N · K − 1` zeros (`coefB_eq`, for `N, K ≥ 1`);
* `μF K w`: the word of a flooding coefficient (uniform in `{0, …, 2^w − 1}`, as a residue mod
  `2^K`): `min w K` fair bits, then `K − w` zeros (`coefF_eq`);
* uniform blocks: fair bits.

Field laws: `wLaw_eq` (binary columns), `rmLaw_eq` (`lawRmBin`, column-major `rmTEnc`),
`eLaw_eq` (`lawEc`). **`setup5_enc`**: the word of the secret of hybrid 5,
`(setup5 x).map sec5Enc.enc`, is the concatenation of `encDate x`, `N · K` fair bits (`u₀`),
`|JC| · d` fair bits (`w`), `10 · 2k · d` independent `μB` (the `Rᵢ`), and `|JC| · N` independent
`μF` (the errors).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ}

/-! ### Coefficient words -/

/-- A binary ring element: one fair bit, then `N · K − 1` zeros. -/
noncomputable def μB (N K : ℕ) : PMF (List Bool) :=
  cat (BitString.uniformList 1) (PMF.pure (List.replicate (N * K - 1) false))

/-- A flooding coefficient: `min w K` fair bits, then `K − w` zeros. -/
noncomputable def μF (K w : ℕ) : PMF (List Bool) :=
  cat (BitString.uniformList (min w K)) (PMF.pure (List.replicate (K - w) false))

theorem concatN_head_zero (v : List Bool) (K : ℕ) : ∀ n : ℕ,
    Algo.concatN (n + 1) (fun t => if t = 0 then v else Algo.zeroW K) = v ++ List.replicate (n * K) false
  | 0 => by simp [Algo.concatN]
  | n + 1 => by
    rw [Algo.concatN, concatN_head_zero v K n, if_neg (by omega), Algo.zeroW, List.append_assoc,
      List.replicate_append_replicate, Nat.succ_mul]

theorem enc_bitVal (hN : 0 < N) (hK : 0 < K) (b : Bool) :
    (ringEnc N K).enc (bitVal (R := Rg N K) b) = b :: List.replicate (N * K - 1) false := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have h := Algo.enc_bitR (N := N' + 1) (K := K' + 1) b
  rw [show bitVal (R := Rg (N' + 1) (K' + 1)) b = if b then 1 else 0 from rfl, h, Algo.constW,
    concatN_head_zero]
  simp only [Algo.bitW, Algo.zeroW, List.cons_append, List.replicate_append_replicate]
  congr 2
  rw [Nat.add_mul, Nat.succ_mul]; omega

/-- **Binary ring elements.** -/
theorem coefB_eq (hN : 0 < N) (hK : 0 < K) :
    (PMF.uniformOfFintype Bool).map (fun b => (ringEnc N K).enc (bitVal (R := Rg N K) b)) =
      μB N K := by
  rw [μB, SigabaNeo.Tape.XProg.uniformList_one, cat, PMF.bind_map]
  simp only [Function.comp_def, PMF.pure_map, enc_bitVal hN hK]
  exact (PMF.bind_pure_comp _ _).symm

theorem takeD_eq_map : ∀ (n : ℕ) (u : List Bool),
    Tape.takeD n u = (List.finRange n).map fun i : Fin n => u.getD i.val false
  | 0, u => rfl
  | n + 1, u => by
    rw [Tape.takeD, takeD_eq_map n u.tail, List.finRange_succ, List.map_cons, List.map_map]
    cases u <;> simp [Tape.hd, Function.comp_def]

/-- The flooding coefficient word of `t < 2^w`. -/
def gF (K w : ℕ) (t : Fin (2 ^ w)) : List Bool := (zmodEnc K).enc ((t : ℕ) : ZMod (2 ^ K))

/-- The bits of `t < 2^w`. -/
def finBits (w : ℕ) (t : Fin (2 ^ w)) : Fin w → Bool := fun i => t.val.testBit i

theorem finBits_bijective (w : ℕ) : Function.Bijective (finBits w) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => Fin.ext (Nat.eq_of_testBit_eq fun j => ?_), by simp⟩
  by_cases hj : j < w
  · exact congrFun h ⟨j, hj⟩
  · have hw : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hw), Nat.testBit_lt_two_pow (b.isLt.trans_le hw)]

theorem gF_eq (K w : ℕ) (t : Fin (2 ^ w)) : gF K w t = Tape.takeD K (List.ofFn (finBits w t)) := by
  have : NeZero (2 ^ K) := ⟨by positivity⟩
  rw [takeD_eq_map, gF]
  show (List.finRange K).map _ = _
  refine List.map_congr_left fun i _ => ?_
  rw [ZMod.val_natCast, Nat.testBit_mod_two_pow]
  simp only [i.isLt, decide_true, Bool.true_and]
  by_cases hi : i.val < w
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]; rfl
  · rw [List.getD_eq_default _ _ (by simpa using hi),
      Nat.testBit_lt_two_pow (t.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- **Flooding coefficients.** -/
theorem coefF_eq (K w : ℕ) : (PMF.uniformOfFintype (Fin (2 ^ w))).map (gF K w) = μF K w := by
  have hu : (PMF.uniformOfFintype (Fin (2 ^ w))).map (finBits w) = PMF.uniformOfFintype _ :=
    PMF.uniformOfFintype_map_equiv (Equiv.ofBijective _ (finBits_bijective w))
  have h1 : (PMF.uniformOfFintype (Fin (2 ^ w))).map (gF K w) =
      (BitString.uniformList w).map (Tape.takeD K) := by
    rw [show gF K w = Tape.takeD K ∘ List.ofFn ∘ finBits w from funext (gF_eq K w),
      ← PMF.map_comp, ← PMF.map_comp, hu]
    rfl
  rw [h1, μF]
  by_cases hKw : K ≤ w
  · rw [Nat.min_eq_right hKw, Nat.sub_eq_zero_of_le hKw, List.replicate_zero, cat_pure_nil_right,
      ← BitString.uniformList_take hKw]
    refine PMF.map_congr_on_support _ _ _ fun u hu => ?_
    rw [Tape.takeD_eq_take (by rw [BitString.length_of_mem_support_uniformList hu]; exact hKw)]
  · rw [Nat.min_eq_left (by omega), cat]
    rw [← PMF.bind_pure_comp]
    refine PMF.bind_congr_on_support _ _ _ fun u hu => ?_
    have hl := BitString.length_of_mem_support_uniformList hu
    simp only [Function.comp_apply, PMF.pure_map]
    congr 1
    rw [show K = w + (K - w) by omega, Tape.takeD_add, Tape.takeD_of_length' hl, ← hl,
      List.drop_length, Tape.takeD_nil, hl]
    congr 2; omega

end AdvancedEncryption.DualUse.Prog
