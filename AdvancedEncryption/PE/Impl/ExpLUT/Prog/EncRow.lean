import PE.Impl.ExpLUT.Prog.EncSamplers
import SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.EncRow

/-!
# Encoding rows of `Enc` on the words of the scheme

`encRowP` (`SigabaNeo.Lib.Lattices.ProgAlgo.Mersenne.EncRow`) on the words of families of ring
elements (`vecE D α`, in the order of `Enum α`): **`rowW_vecE`**: from the words of `s` and of the
families `A₀`, `A₁`, `Z`, `E` over `α`, it writes the word of the family
`c ↦ s A₀ c + A₁ c − Z c + E c`. With `A₀`, `A₁` the rows of a public matrix, `Z c = (z G)_c` and
`E` the errors, this is one encoding `s A − z G + e` of the ciphertext of §5.1 (`b`, `h_k`,
`c^aut_{t,d}`, the bottom rows of `C^in_t`, `c^in_{t,d}`, `c₀`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape

variable (D : Dims)

/-- Entry `c` of the word of a family is the word of the `c`-th element. -/
theorem blk_vecE {α : Type} [Enum α] (f : α → Rg D) (c : ℕ)
    (hc : c < (Enum.list (α := α)).length) :
    blk (D.N * D.K) c ((vecE D α).enc f) = (rEnc D).enc (f (Enum.list (α := α))[c]) := by
  have h := FixedEnc.fun_block (α := α) (rEnc D) f c hc
  have hl : ((((vecE D α).enc f).drop (c * (D.N * D.K))).take (D.N * D.K)).length = D.N * D.K := by
    rw [h, FixedEnc.length]
  unfold blk
  rw [takeD_eq_take (by rw [List.length_take] at hl; omega)]
  exact h

theorem decRM_rEnc (a : Rg D) : decRM D.N D.K ((rEnc D).enc a) = a := decRM_encRM D.K_pos a

/-- The word of a family as a concatenation over its enumeration. -/
theorem vecE_concatN {α : Type} [Enum α] (F : α → Rg D) :
    (vecE D α).enc F = concatN (Enum.list (α := α)).length
      fun c => if h : c < (Enum.list (α := α)).length then (rEnc D).enc (F (Enum.list (α := α))[c])
        else [] := by
  rw [concatN_finRange]
  show ((Enum.list (α := α)).map F).flatMap (rEnc D).enc = _
  rw [List.flatMap_map]
  conv_lhs => rw [← List.map_getElem_finRange (Enum.list (α := α))]
  rw [List.flatMap_map]
  refine List.flatMap_congr fun i _ => ?_
  rw [dif_pos i.isLt]

/-- **An encoding row on the words of families**: the word of `c ↦ s A₀ c + A₁ c − Z c + E c`. -/
theorem rowW_vecE {α : Type} [Enum α] (s : Rg D) (A0 A1 Z E : α → Rg D) :
    rowW D.N D.K (Enum.list (α := α)).length ((rEnc D).enc s) ((vecE D α).enc A0)
      ((vecE D α).enc A1) ((vecE D α).enc Z) ((vecE D α).enc E) =
      (vecE D α).enc fun c => s * A0 c + A1 c - Z c + E c := by
  rw [rowW_eq D.K_pos (FixedEnc.length _ _)]
  conv_rhs => rw [vecE_concatN]
  refine concatN_congr fun c hc => ?_
  rw [dif_pos hc, blk_vecE D A0 c hc, blk_vecE D A1 c hc, blk_vecE D Z c hc, blk_vecE D E c hc,
    decRM_rEnc, decRM_rEnc, decRM_rEnc, decRM_rEnc, decRM_rEnc]
  rfl

end AdvancedEncryption.ExpLUT.Prog
