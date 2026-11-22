import PE.Impl.DualUse.SimGame5
import PE.Impl.DualUse.Algo.KeyMatrix
import SigabaNeo.Lib.Lattices.Algo.SimWords

/-!
# The word layouts of the reductions' challengers

The tape programs of the three Ring-LWE reductions (hybrid 3, hybrid 5, the ideal side) exchange
values as **fixed-length words** (`FixedEnc`). This file fixes those layouts once, for the
programs of `PE.Impl.DualUse.Prog.*` and for the key component (the simulated `KeyGen*`, which
reads the encoding of the `SimData`).

Conventions (those of the codec `PE.Impl.DualUse.Codec`):

* a ring element of `Rg N K` is `ringEnc N K`: its `N` coefficients, each `K` bits, least
  significant bit first (`N · K` bits);
* a matrix `Matrix r s (Rg N K)` is `matEnc r s`: its entries in row-major order along the
  enumerations `Enum r`, `Enum s` (`Fin n`: in order; products: lexicographic; sums: left part
  first). For `s = Col k` this is the word `colsW` of `SigabaNeo.Lattices.Algo` (`matEnc_cols`):
  the columns `(a, i)` in the order `p ↦ (p / k, p % k)`;
* a function on an enumerated type is the concatenation of its values in the enumeration's order
  (`FixedEnc.fun`), a product the concatenation of its fields (`FixedEnc.prod`), first field first;
* a bit is one bit (`bitEnc`); a date is its 10 bits `encDate` (`dateEnc`).

## The layouts

| value | encoding | fields, in order |
|---|---|---|
| hybrid 3 / ideal instance `(a, b)` | `inst3Enc` | `a`, `b` (rows `1 × Col k`) |
| hybrid 5 instance `(P, P')` | `inst5Enc` | `pubEnc P`, `pubEnc P'`; `pubEnc (B₀, a, z, p)` = `B₀` (`1 × Fin d`), `a`, `z`, `p` |
| `Sec3` | `sec3Enc` (the `Rᵢ` column-major, `rmTEnc`) | `x`, `B₀`, `w`, `p`, `rest = (s, e₀, e₁, Rm, e')`, `e` |
| `Sec5` | `sec5Enc` (the `Rᵢ` column-major) | `x`, `u₀`, `w`, `Rm`, `e` |
| `SecI` | `secIEnc` | `x`, `B₀`, `w`, `p`, `r = (s, e₀, e₁, Rm, ej, e')`, `ct` (`ctEnc`) |
| `SimData` | `sdEnc` | `mpk` (`pkEnc`), `c₀`, `Rm`, `W`, `Ψ`, `x` |

Here `w : JC → (Fin d → Bool)` is `FixedEnc.fun (FixedEnc.fun bitEnc)` over
`JC = (Attr × Index) × Col k`, `Rm`, `W`, `Ψ`, `e` are functions of matrices (`FixedEnc.fun
(matEnc …)`), and `EncCoins` is encoded field by field (`coinsEnc`).

All lengths are explicit (`*_len` abbreviations), so a program reads a field as the block at a
known offset.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-! ### Atoms -/

/-- **A bit**: one bit. -/
def bitEnc : FixedEnc Bool 1 where
  enc b := [b]
  inj _ _ h := by simpa using h
  length _ := rfl

/-- **A date**: its 10 bits, the month then the day, each most significant bit first. -/
def dateEnc : FixedEnc Date 10 where
  enc := encDate
  inj := encDate.injective
  length := length_encDate

/-- An encoding along an equivalence (to change the shape of a product). -/
def FixedEnc.equiv {α β : Type} {n : ℕ} (e : FixedEnc β n) (f : α ≃ β) : FixedEnc α n :=
  e.comap f f.injective

/-! ### Instances -/

/-- The instances of hybrid 3 and of the ideal side: `(a, b)`. -/
abbrev Inst3T (N K k : ℕ) := Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K)

/-- **Instances of hybrid 3 and of the ideal side**: `a`, then `b`. -/
def inst3Enc :=
  (matEnc (N := N) (K := K) (Fin 1) (Col k)).prod (matEnc (N := N) (K := K) (Fin 1) (Col k))

/-- The public part `(B₀, a, z, p)` of a hybrid-5 instance. -/
def pubEnc (d : ℕ) :=
  (matEnc (N := N) (K := K) (Fin 1) (Fin d)).prod ((matEnc (N := N) (K := K) (Fin 1) (Col k)).prod
    ((matEnc (N := N) (K := K) (Fin 1) (Col k)).prod (ringEnc N K)))

/-- **Instances of hybrid 5**: the public part, then the values. -/
def inst5Enc (d : ℕ) := (pubEnc (N := N) (K := K) (k := k) d).prod (pubEnc (N := N) (K := K) (k := k) d)

/-! ### Coins -/

/-- Binary columns `w : JC → (Fin d → Bool)`. -/
def wEnc := FixedEnc.fun (α := JC (Sdw (N := N) hk)) (FixedEnc.fun (α := Fin c.d) bitEnc)

/-- The matrices `Rᵢ` (or the `Wⱼ`) as ring matrices `Fin d × Col k`. -/
def rmEnc := FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin c.d) (Col k))

/-- A matrix by its columns (column-major): the transpose's row-major word. -/
def matTEnc (r s : Type) [Enum r] [Enum s] :=
  (matEnc (N := N) (K := K) s r).comap Matrix.transpose Matrix.transpose_injective

/-- **The matrices `Rᵢ` in the secrets**: column-major (`i`, then the column `c`, then the row
`a`), the order of the coins of `lawRmBin`. -/
def rmTEnc := FixedEnc.fun (α := Fin 10) (matTEnc (N := N) (K := K) (Fin c.d) (Col k))

/-- The errors of the encodings, `e : Attr × Index → 1 × Col k`. -/
def eEnc := FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
  (matEnc (N := N) (K := K) (Fin 1) (Col k))

/-- The coins other than the encodings' errors: `(s, e₀, e₁, Rm, e')`. -/
def restEnc :=
  (ringEnc N K).prod ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).prod
    ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).prod ((rmTEnc c).prod (ringEnc N K))))

/-- The coins of `Enc` as a tuple. -/
def coinsTuple (r : EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) :=
  (r.s, r.e₀, r.e₁, r.Rm, r.ej, r.e')

theorem coinsTuple_injective : Function.Injective (coinsTuple hk c) := by
  intro a b h
  cases a; cases b
  simp only [coinsTuple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  subst h1 h2 h3 h4 h5 h6; rfl

/-- **The coins of `Enc`**: `s`, `e₀`, `e₁`, `Rm`, `ej`, `e'`. -/
def coinsEnc :=
  ((ringEnc N K).prod ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).prod
    ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).prod ((rmTEnc c).prod ((eEnc (N := N) hk).prod (ringEnc N K)))))).comap
    (coinsTuple hk c) (coinsTuple_injective hk c)

/-! ### The secrets of the reductions -/

/-- **The secret of hybrid 3**: `x`, `B₀`, `w`, `p`, `rest`, `e`. -/
def sec3Enc :=
  dateEnc.prod ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).prod ((wEnc hk c).prod
    ((ringEnc N K).prod ((restEnc c).prod (eEnc (N := N) hk)))))

/-- **The secret of hybrid 5**: `x`, `u₀`, `w`, `Rm`, `e`. -/
def sec5Enc :=
  dateEnc.prod ((ringEnc N K).prod ((wEnc hk c).prod ((rmTEnc c).prod (eEnc (N := N) hk))))

/-- **The secret of the ideal side**: `x`, `B₀`, `w`, `p`, the coins, the uniform challenge. -/
def secIEnc :=
  dateEnc.prod ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).prod ((wEnc hk c).prod
    ((ringEnc N K).prod ((coinsEnc hk c).prod (ctEnc hk c)))))

/-! ### What the reduction knows -/

/-- The simulation data as a tuple. -/
def sdTuple (s : SimData hk c) := (s.mpk, s.c₀, s.Rm, s.W, s.Ψ, s.x)

theorem sdTuple_injective : Function.Injective (sdTuple (hk := hk) (c := c)) := by
  intro a b h
  cases a; cases b
  simp only [sdTuple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  subst h1 h2 h3 h4 h5 h6; rfl

/-- **The simulation data**, the input of the key component: `mpk` (`pkEnc`), `c₀`
(`1 × Fin d`), the `Rᵢ` (`Fin d × Col k`, `i < 10`), the `Wⱼ` (`Fin d × Col k`, along
`Attr × Index`), the `Ψᵢ` (`Fin 2 × Col k`), and the date `x` (10 bits). -/
def sdEnc :=
  ((pkEnc hk c).prod ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).prod ((rmEnc c).prod
    ((FixedEnc.fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)
      (matEnc (N := N) (K := K) (Fin c.d) (Col k))).prod
    ((FixedEnc.fun (α := Fin 10) (matEnc (N := N) (K := K) (Fin 2) (Col k))).prod dateEnc))))).comap
    (sdTuple hk c) (sdTuple_injective hk c)

theorem sdEnc_enc (s : SimData hk c) :
    (sdEnc hk c).enc s = (pkEnc hk c).enc s.mpk ++ ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc s.c₀ ++
      ((rmEnc c).enc s.Rm ++ ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin c.d) (Col k))).enc s.W ++
        ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin 2) (Col k))).enc s.Ψ ++ dateEnc.enc s.x)))) := rfl

/-! ### Matrices with the gadget columns are `colsW` -/

theorem matEnc_fin_eq_matW {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Rg N K)) :
    (matEnc (N := N) (K := K) (Fin m) (Fin n)).enc M = Algo.matW N K m n M := by
  show ((List.finRange m).map (fun i => (M i : Fin n → Rg N K))).flatMap
      (fun r => ((List.finRange n).map r).flatMap (ringEnc N K).enc) = _
  rw [List.flatMap_map, Algo.flatMap_finRange, Algo.matW, Algo.concatN_mul]
  refine Algo.concatN_congr fun i hi => ?_
  rw [dite_eq_left_of_eq_true (eq_true hi), List.flatMap_map, Algo.flatMap_finRange]
  refine Algo.concatN_congr fun j hj => ?_
  have hij : i * n + j < m * n := by
    have := Nat.mul_le_mul_right n (show i + 1 ≤ m from hi); rw [Nat.add_mul] at this; omega
  rw [dite_eq_left_of_eq_true (eq_true hj), dite_eq_left_of_eq_true (eq_true hij)]
  have h1 : (i * n + j) / n = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (i * n + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  congr 2
  · exact Fin.ext h1.symm
  · exact Fin.ext h2.symm

/-- The enumeration of `Col k` is the order `p ↦ (p / k, p % k)`. -/
theorem enum_col : (Enum.list (α := Col k)) = (List.finRange (2 * k)).map (Algo.colE k) := by
  have hl : (Enum.list (α := Col k)).length = 2 * k := by
    rw [Enum.length_prod]; simp [Enum.list]
  apply List.ext_getElem (by rw [hl]; simp)
  intro p h1 h2
  rw [List.getElem_map, List.getElem_finRange]
  have hp : p < 2 * k := by rwa [hl] at h1
  have hk : 0 < k := by omega
  have hq : p / k < 2 := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hp)
  have hr : p % k < k := Nat.mod_lt p hk
  have hlk : (Enum.list (α := Fin k)).length = k := by simp [Enum.list]
  have e : p = p / k * (Enum.list (α := Fin k)).length + p % k := by
    rw [hlk, Nat.mul_comm]; exact (Nat.div_add_mod p k).symm
  have := Enum.getElem_prod (α := Fin 2) (β := Fin k) (p / k) (p % k) (by simpa [Enum.list] using hq)
    (by rwa [hlk]) (by rw [← e]; exact h1)
  simp only [← e] at this
  rw [this, Enum.getElem_fin, Enum.getElem_fin, Algo.colE_apply]
  rfl

/-- **The codec's word of a matrix with the gadget columns** is `colsW`. -/
theorem matEnc_cols {m : ℕ} (M : Matrix (Fin m) (Col k) (Rg N K)) :
    (matEnc (N := N) (K := K) (Fin m) (Col k)).enc M = Algo.colsW N K k m M := by
  rw [Algo.colsW, ← matEnc_fin_eq_matW]
  show ((List.finRange m).map (fun i => (M i : Col k → Rg N K))).flatMap
      (fun r => ((Enum.list (α := Col k)).map r).flatMap (ringEnc N K).enc) =
    ((List.finRange m).map (fun i => ((M.submatrix id (Algo.colE k)) i : Fin (2 * k) → Rg N K))).flatMap
      (fun r => ((List.finRange (2 * k)).map r).flatMap (ringEnc N K).enc)
  rw [enum_col]
  simp only [List.map_map, List.flatMap_map]
  rfl

end AdvancedEncryption.DualUse.Prog
