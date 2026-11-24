import PE.Impl.ExpLUT.AH.Conf

/-!
# KeyGen (package F3): the key boxes of the machine

`kbOf D B hB r : KeyBoxes D`: the big box is the image of `|P| N B` fair bits, `B` per coefficient
of the short part, read as centered residues (`cenEmb`), i.e. **`Big = famBig B`** (`kbOf_Big`),
whatever the order in which a machine consumes the bits; the small box is the ball of radius `r`
(`famBall r`). Coverage (`kbCover_of`): shifts within `s` are covered when `r + s ≤ 2^{B−1} − 1`.

At the concrete parameters (`Dc`, `B = Bk = 18750`, `r = 2^{Bk−1} − 1 − 2^{18500}`): **`kbDc`**,
**`kbCover_Dc : KbCover kbDc coverBound`** (`coverBound = 2^18500`), the box hypothesis of
package G.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Lattices Cslib AdvancedEncryption.ExpLUT.Params

variable (D : Dims)

/-- The short coordinates of the keys at `D`. -/
abbrev PIdxD := PIdx (Wb D) (Jh D) D.K (2 ^ D.b)

/-- The coins of the big box: one bit `(p, j, β)` per bit `β < B` of coefficient `j` of entry `p`. -/
abbrev CoinIdx (B : ℕ) := (PIdxD D × Fin D.N) × Fin B

/-- **The embedding of the coins**: `B` bits per coefficient, as centered residues. -/
noncomputable def coinEmb (B : ℕ) (hB : 2 ^ B ≤ D.q) :
    (Fin (Fintype.card (CoinIdx D B)) → Bool) ↪ (PIdxD D → Rg D) :=
  ((((Fintype.equivFin (CoinIdx D B)).arrowCongr (Equiv.refl Bool)).symm.trans
      (Equiv.curry _ _ _)).toEmbedding.trans
    (Function.Embedding.piCongrRight fun _ : PIdxD D × Fin D.N => cenEmb B hB)).trans
    famCoeffs.symm.toEmbedding

/-- **The key boxes**: `Big` the image of the coins, `Small` the ball of radius `r`. -/
noncomputable def kbOf (B : ℕ) (hB : 2 ^ B ≤ D.q) (r : ℕ) : KeyBoxes D where
  mB := Fintype.card (CoinIdx D B)
  emb := coinEmb D B hB
  Small := famBall D.q D.N (PIdxD D) r

theorem kbOf_Big (B : ℕ) (hB : 2 ^ B ≤ D.q) (r : ℕ) :
    (kbOf D B hB r).Big = famBig D.q D.N (PIdxD D) B hB := by
  simp only [KeyBoxes.Big, kbOf, coinEmb, famBig, bigBox, ← Finset.map_map]
  congr 2
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
  exact ⟨_, Finset.mem_univ _, Equiv.apply_symm_apply _ x⟩

theorem kbOf_Small (B : ℕ) (hB : 2 ^ B ≤ D.q) (r : ℕ) :
    (kbOf D B hB r).Small = famBall D.q D.N (PIdxD D) r := rfl

/-- **Coverage**: shifts within `s` are covered when `r + s ≤ 2^{B−1} − 1`. -/
theorem kbCover_of (B : ℕ) (hB : 2 ^ B ≤ D.q) (hB1 : 1 ≤ B) (r s : ℕ)
    (hrs : r + s ≤ 2 ^ (B - 1) - 1) : KbCover (kbOf D B hB r) s := by
  intro x hx t ht
  rw [kbOf_Big]
  rw [kbOf_Small] at hx
  exact famBall_subset_big B hB hB1 (famBall_mono hrs (add_mem_famBall hx ht))

theorem kbCover_of_eq {kb : KeyBoxes D} {B : ℕ} {hB : 2 ^ B ≤ D.q} {r : ℕ}
    (hkb : kb = kbOf D B hB r) (hB1 : 1 ≤ B) (s : ℕ) (hrs : r + s ≤ 2 ^ (B - 1) - 1) :
    KbCover kb s := by
  subst hkb; exact kbCover_of D B hB hB1 r s hrs

/-! ### The concrete boxes

As for package P's boxes, the concrete key boxes are opaque (`irreducible_def`): the elaborator
`whnf`s the type of a hypothesis `x ∈ kbDc.Small`, which would enumerate the box. -/

theorem hBk_Dc : 2 ^ Bk ≤ Dc.q := hBk

/-- The radius of the small box: `2^{Bk−1} − 1 − 2^{18500}`. -/
noncomputable def rSmall : ℕ := 2 ^ (Bk - 1) - 1 - coverBound

theorem rSmall_def : rSmall = 2 ^ (Bk - 1) - 1 - coverBound := rfl

/-- **The key boxes at `Dc`**: `Bk = 18750` bits per coefficient, the ball of radius
`2^{Bk−1} − 1 − 2^{18500}`. -/
noncomputable irreducible_def kbDc : KeyBoxes Dc := kbOf Dc Bk hBk_Dc rSmall

/-- **The key boxes cover the shifts within `2^{18500}`** (package G's `KbCover`). -/
theorem sub_add_le_of {A c : ℕ} (h : 2 * c + 2 ≤ A) : (A - 1 - c) + c ≤ A - 1 := by omega

theorem rSmall_add : rSmall + coverBound ≤ 2 ^ (Bk - 1) - 1 := by
  rw [rSmall_def]; exact sub_add_le_of two_cover_le



theorem kbCover_Dc : KbCover kbDc coverBound :=
  kbCover_of_eq Dc kbDc_def one_le_Bk coverBound rSmall_add

end AdvancedEncryption.ExpLUT.Prog
