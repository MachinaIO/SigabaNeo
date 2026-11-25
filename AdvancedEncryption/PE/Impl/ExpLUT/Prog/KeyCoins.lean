import PE.Impl.ExpLUT.Prog.KeyTryVM
import PE.Impl.ExpLUT.Prog.KeyBoxW
import SigabaNeoStd.Lattices.CoinsUniform

/-!
# KeyGen (package F3): the coins of the box try

The `KeyGen` machine reads the coins of one try of box rejection as the queue
`decList cs B 2^{B−1} |P|` (`exec_decQC`): the short coordinates `p ∈ P = PIdx` in the order of
their enumeration, `N B` coins per element, `B` coins per coefficient read as `val − 2^{B−1}`.

* `coinDec D B cs : P → R`: the family read from the coins (`coinDec_ofFn`: it is
  `famCoeffs.symm` of the centered residues `cenEmb` of the coins, re-indexed by the explicit
  bijection `coinIdx`);
* **`map_uniformList_coinDec`**: the law of `coinDec` on `|P| N B` fair coins is the uniform law
  on the big box `famBig B`, hence on `(kbOf D B hB r).Big` (`map_uniformList_coinDec_kbOf`);
* `map_coinDec`: the queue of the machine is `(Enum.list P).map (coinDec cs)`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape.MVM Cslib Cslib.BitString
open SigabaNeo.Lattices.Algo (val)
open Cslib.Probability

/-! ### Enumerations as equivalences -/

/-- The position in an enumeration, as an equivalence. -/
def enumEquiv (α : Type) [Enum α] [DecidableEq α] : α ≃ Fin (Enum.list (α := α)).length where
  toFun a := ⟨Enum.index a, Enum.index_lt a⟩
  invFun i := (Enum.list (α := α))[i]
  left_inv a := Enum.getElem_index a
  right_inv i := Fin.ext (List.Nodup.idxOf_getElem Enum.nodup _ _)

/-! ### Values of coin words -/

theorem val_ofFn : ∀ {B : ℕ} (bs : Fin B → Bool), val (List.ofFn bs) = (bitsEquiv B bs : ℕ)
  | 0, bs => by simp [bitsEquiv, finFunctionFinEquiv_apply]
  | B + 1, bs => by
    rw [List.ofFn_succ, Algo.val_cons, val_ofFn (fun i => bs i.succ)]
    simp only [bitsEquiv, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
      Function.comp_apply, finFunctionFinEquiv_apply, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
      mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
    simp only [Equiv.refl_symm, Equiv.refl_apply]
    congr 1
    · cases bs 0 <;> rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring

theorem take_drop_ofFn {m : ℕ} (r : Fin m → Bool) (a B : ℕ) (h : a + B ≤ m) :
    ((List.ofFn r).drop a).take B = List.ofFn (fun β : Fin B => r ⟨a + β, by omega⟩) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp

variable (D : Dims)

/-! ### The family read from the coins -/

/-- The number of short coordinates. -/
abbrev nPI : ℕ := (Enum.list (α := PIdxD D)).length

/-- The center of the coefficients of the big box: `2^{B−1}`. -/
def cB (B : ℕ) : ZMod (2 ^ D.K - 1) := 2 ^ (B - 1)

/-- **The short part read from the coins**: element `t` (in the order of `Enum`) from the coins
`[t N B, (t + 1) N B)`. -/
noncomputable def coinDec (B : ℕ) (cs : List Bool) : PIdxD D → Rg D :=
  fun p => (decList D.N D.K cs B (cB D B) (nPI D)).getD (Enum.index p) 0

/-- **The machine's queue is the family in the order of `Enum`.** -/
theorem map_coinDec (B : ℕ) (cs : List Bool) :
    (Enum.list (α := PIdxD D)).map (coinDec D B cs) = decList D.N D.K cs B (cB D B) (nPI D) := by
  apply List.ext_getElem
  · simp [decList]
  · intro i h1 h2
    have hi' : i < (Enum.list (α := PIdxD D)).length := by simpa using h1
    simp only [List.getElem_map, coinDec]
    have hi : Enum.index (Enum.list (α := PIdxD D))[i] = i := by
      exact congrArg Fin.val ((enumEquiv (PIdxD D)).apply_symm_apply ⟨i, hi'⟩)
    rw [hi, List.getD_eq_getElem _ _ h2]

/-- The position of the coin of bit `β` of coefficient `j` of `p`: `idx p · N B + B j + β`. -/
def coinIdx (B : ℕ) : (PIdxD D × Fin D.N) × Fin B ≃ Fin (nPI D * D.N * B) :=
  ((Equiv.prodCongr ((Equiv.prodCongr (enumEquiv (PIdxD D)) (Equiv.refl _)).trans finProdFinEquiv)
    (Equiv.refl _)).trans finProdFinEquiv)

theorem coinIdx_val (B : ℕ) (p : PIdxD D) (j : Fin D.N) (β : Fin B) :
    (coinIdx D B ((p, j), β) : ℕ) = Enum.index p * (D.N * B) + B * j + β := by
  simp only [coinIdx, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.coe_refl, id,
    finProdFinEquiv_apply_val, enumEquiv, Equiv.coe_fn_mk]
  ring

theorem cenEmb_eq (B : ℕ) (hB : 2 ^ B ≤ D.q) (bs : Fin B → Bool) :
    (cenEmb B hB bs : ZMod D.q) = ((val (List.ofFn bs) : ℕ) : ZMod (2 ^ D.K - 1)) - cB D B := by
  rw [val_ofFn]
  simp only [cenEmb, Function.Embedding.coeFn_mk, cB]
  push_cast
  rfl

/-- **The family read from fair coins** is the image of the coins under the centered residues,
re-indexed by `coinIdx`. -/
theorem coinDec_ofFn (B : ℕ) (hB : 2 ^ B ≤ D.q) (r : Fin (nPI D * D.N * B) → Bool) :
    coinDec D B (List.ofFn r) = famCoeffs.symm (fun pj : PIdxD D × Fin D.N =>
      cenEmb B hB (fun β => r (coinIdx D B (pj, β)))) := by
  apply famCoeffs.injective
  rw [Equiv.apply_symm_apply]
  funext ⟨p, j⟩
  rw [famCoeffs_apply]
  have hp := Enum.index_lt p
  have hlen : (List.ofFn r).length = nPI D * (D.N * B) := by simp [Nat.mul_assoc]
  simp only [coinDec, decList]
  rw [List.getD_eq_getElem _ _ (by simpa using hp), List.getElem_map, List.getElem_range,
    decCoins, Negacyclic.coeffs_ofCoeffs, cenEmb_eq]
  congr 3
  have hj := j.isLt
  have hle : Enum.index p * (D.N * B) + D.N * B ≤ nPI D * D.N * B := by
    have : (Enum.index p + 1) * (D.N * B) ≤ nPI D * (D.N * B) := Nat.mul_le_mul_right _ hp
    rw [Nat.mul_assoc]; rw [add_mul, one_mul] at this; exact this
  have hjB : B * j + B ≤ D.N * B := by
    have : (j.val + 1) * B ≤ D.N * B := Nat.mul_le_mul_right _ hj
    rw [add_mul, one_mul, mul_comm] at this; exact this
  rw [chunk, take_drop_ofFn r _ _ hle, take_drop_ofFn _ _ _ hjB]
  congr 1
  funext β
  simp only [List.getElem_ofFn]
  congr 1
  apply Fin.ext
  rw [coinIdx_val]
  simp only
  omega

/-- The re-indexing of the coins. -/
def coinRe (B : ℕ) :
    (Fin (nPI D * D.N * B) → Bool) ≃ (PIdxD D × Fin D.N → Fin B → Bool) :=
  (Equiv.arrowCongr (coinIdx D B).symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

theorem coinRe_apply (B : ℕ) (r : Fin (nPI D * D.N * B) → Bool) (pj : PIdxD D × Fin D.N)
    (β : Fin B) : coinRe D B r pj β = r (coinIdx D B (pj, β)) := by
  simp [coinRe]

/-- **The law of the short part read from fair coins**: uniform on the big box. -/
theorem map_uniformList_coinDec (B : ℕ) (hB : 2 ^ B ≤ D.q) :
    (uniformList (nPI D * D.N * B)).map (coinDec D B) =
      PMF.uniformOfFinset (famBig D.q D.N (PIdxD D) B hB) (famBig_nonempty B hB) := by
  have hf : (fun r : Fin (nPI D * D.N * B) → Bool => coinDec D B (List.ofFn r)) =
      famCoeffs.symm ∘ (Function.Embedding.piCongrRight fun _ : PIdxD D × Fin D.N => cenEmb B hB) ∘
        coinRe D B := by
    funext r
    rw [coinDec_ofFn D B hB]
    simp only [Function.comp_apply]
    congr 1
  apply map_uniformList_eq_uniformOfFinset
  · rw [hf]
    exact famCoeffs.symm.injective.comp
      ((Function.Embedding.injective _).comp (coinRe D B).injective)
  · rw [hf, ← Finset.image_image, ← Finset.image_image, Finset.image_univ_equiv,
      famBig, bigBox, Finset.map_eq_image,
      Finset.map_eq_image, Finset.image_image, Finset.image_image]
    rfl

/-- **The same, for the key boxes `kbOf`.** -/
theorem map_uniformList_coinDec_kbOf (B : ℕ) (hB : 2 ^ B ≤ D.q) (r : ℕ) :
    (uniformList (nPI D * D.N * B)).map (coinDec D B) =
      PMF.uniformOfFinset (kbOf D B hB r).Big (kbOf D B hB r).hBig := by
  rw [map_uniformList_coinDec D B hB]
  congr 1
  exact (kbOf_Big D B hB r).symm

end AdvancedEncryption.ExpLUT.Prog
