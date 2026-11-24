import PE.Impl.ExpLUT.AH.CircBridge
import PE.Impl.ExpLUT.Prog.Eval

/-!
# The secret of the reduction's handlers (package G2)

The reduction's handlers keep a finite secret (`RedComps.Sig`) that represents the machines'
reduction secret `redSecW` through a map. Here the **raw secret** `RawSec D`: the selected
attribute, the circular instance, and the coins of `redSecW` (`B̄⁽²⁾`, `H⁽²⁾`, `d₂`, the flooding
errors, the programming `zr`); `rawF` computes the reduction secret (`redPub`, `redCore`), and
`rawSetup i x` draws the coins in the order of `redSecW`:

* **`map_rawSetup`**: `(rawSetup D χfl i x).map (rawF D) = redSecW D χfl x i` (the `map_setupS`
  field of `RedComps`);
* `rawEnc D : FixedEnc (RawSec D) _`: the attribute bits, the instance as its ring-level pair (the
  canonical words of the rows, `toPair`), the canonical words of the coins in `Enum` order, the
  bits of `zr`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open scoped ENNReal

variable (D : Dims)

/-- **The raw secret of the handlers**: attribute, instance, `B̄⁽²⁾`, `H⁽²⁾`, `d₂`, flooding errors,
programming. -/
abbrev RawSec := Attribute w8 × CInst D × (BCol (Wb D) D.K → Rg D) × (Jh D → Col D.K → Rg D) ×
  Rg D × FloodV (setting D) Pos × (PrI (setting D) Pos → Wb D → Bool)

/-- **The reduction secret of a raw secret.** -/
noncomputable def rawF (s : RawSec D) : RSec D :=
  (attrN s.1, redPub s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1, s.2.2.2.2.2.2,
    redCore s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1, s.2.2.2.2.2.1)

/-- **The law of the raw secret** for the instance `i` and the attribute `x`: the coins of
`redSecW`, in its order. -/
noncomputable def rawSetup (χfl : PMF (Rg D)) (i : CInst D) (x : Attribute w8) : PMF (RawSec D) :=
  (iidLaw (unifW D) (BCol (Wb D) D.K)).bind fun B2 =>
  (iidFam (unifW D) (Jh D) (Col D.K)).bind fun H2 =>
  (unifW D).bind fun d2 =>
  (floodLaw (setting D) Pos χfl).bind fun fl =>
  (zrLaw (setting D) (Wb D) Pos).map fun zr => (x, i, B2, H2, d2, fl, zr)

/-- **The raw secret represents the machines' reduction secret.** -/
theorem map_rawSetup (χfl : PMF (Rg D)) (i : CInst D) (x : Attribute w8) :
    (rawSetup D χfl i x).map (rawF D) = redSecW D χfl x i := by
  simp only [rawSetup, redSecW, PMF.map_bind, PMF.map_comp]
  rfl

/-! ### The encoding of the raw secret -/

/-- The attribute bits. -/
def attrEnc : FixedEnc (Attribute w8) 128 where
  enc := encAttribute w8
  inj := (encAttribute w8).injective
  length := length_encAttribute w8

/-- The instance, as the canonical words of its ring-level pair (rows in the registry's order). -/
noncomputable def instEnc :=
  ((vecE D (Fin (circParamsD D).rows)).prod (vecE D (Fin (circParamsD D).rows))).comap (toPair D)
    (fun i j (h : toPair D i = toPair D j) => by rw [← ofPair_toPair D i, ← ofPair_toPair D j, h])

/-- The flooding errors. -/
noncomputable def floodEnc :=
  ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).prod
    ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).prod
    ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).prod
      (vecE D (Col D.K)))))

/-- The programming bits. -/
noncomputable def zrEnc :=
  FixedEnc.fun (α := PrI (setting D) Pos) (FixedEnc.fun (α := Wb D) bitEnc)

/-- **The encoding of the raw secret.** -/
noncomputable def rawEnc :=
  (attrEnc).prod ((instEnc D).prod ((vecE D (BCol (Wb D) D.K)).prod
    ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).prod ((rEnc D).prod
    ((floodEnc D).prod (zrEnc D))))))

end AdvancedEncryption.ExpLUT.Prog
