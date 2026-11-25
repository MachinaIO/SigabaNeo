import PE.Impl.ExpLUT.AH.RedSecret
import PE.Impl.ExpLUT.AH.RedGame
import PE.Impl.ExpLUT.Prog.DecCoefMath
import PE.Impl.ExpLUT.Prog.DecFinalD
/-!
# The public key of the reduction, as words (package G2, `pubP`)

The specification of the reduction's public-key component `pubP` (`Generic.Comps.law_pub`): from
the raw secret `σ` (`rawEnc`), the word `(mpkEnc D).enc (pubK D σ)` of the public key of the view
of H2 (`pubK D σ = (redView D (rawF D σ)).1`). Here the public key is described field by field
from the parts of the raw secret, and its word as the concatenation of the word lists that the
phases of `pubP` produce, in the order of `Enum`:

* `B = [aB; B̄⁽²⁾]` (**`pubK_B`**), `H_k = [aH k; H⁽²⁾ k]` (**`pubK_H`**), `d = [ad; d₂]`
  (**`pubK_d`**): copies of the instance and of the coins;
* `a_t = Ā ⬝ zr(Z_t) + X^{w x_t} G⁽¹⁾` (**`pubK_a`**), `A₀ = B̄ ⬝ zr(R₀) + G` (**`pubK_A0`**),
  `A^in_{t,d} = B̄ ⬝ zr(R^in_{t,d}) + δ^in_{t,d} G` (**`pubK_Ain`**) and
  `A^aut_{t,d} = σ_{g_t}(B̄ ⬝ zr(R^aut_{t,d})) + δ^aut_{t,d} G` (**`pubK_Aaut`**), with the digits
  `δ^in_{t,d} = d(cinMat(a_t, cb_t))`, `δ^aut_{t,d} = d(autGC …)` (the bottom rows `cb_t` of `cb2`
  and the helpers `h = v_H − G⁽²⁾ + H⁽²⁾` of `redCore`);
* **`pubWord_eq`**: the word of the public key is `wB ++ wH ++ wa ++ wA0 ++ wAin ++ wAaut ++ wd`,
  each a concatenation of `encRM` words along `Enum`.

The encodings as word lists (`pvecE_enc`, `pfun_enc`, `pmatE2_enc`) are copies, under new names,
of lemmas of `Prog/DecMachineCode` (not imported here).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Encodings as word lists -/

section Enc

variable {D : Dims}

theorem pvecE_enc {α : Type} [Enum α] (v : α → Rg D) :
    (vecE D α).enc v = ((Enum.list (α := α)).map fun c => encRM D.N D.K (v c)).flatten := by
  show ((Enum.list (α := α)).map v).flatMap _ = _
  simp [List.flatMap, List.map_map, Function.comp_def, rEnc_enc]

theorem pfun_enc {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (f : α → β) :
    (FixedEnc.fun (α := α) e).enc f = ((Enum.list (α := α)).map fun a => e.enc (f a)).flatten := by
  show ((Enum.list (α := α)).map f).flatMap _ = _
  simp [List.flatMap, List.map_map, Function.comp_def]

theorem pmatE2_enc {α : Type} [Enum α] (M : Fin 2 → α → Rg D) :
    (matE D (Fin 2) α).enc M = (vecE D α).enc (M 0) ++ (vecE D α).enc (M 1) := by
  show ((Enum.list (α := Fin 2)).map M).flatMap (vecE D α).enc = _
  show List.flatMap (vecE D α).enc [M 0, M 1] = _
  simp [List.flatMap]

/-- The words of a function into the ring, along `Enum`. -/
noncomputable def pwordsOf {α : Type} [Enum α] (v : α → Rg D) : List Bool :=
  ((Enum.list (α := α)).map fun c => encRM D.N D.K (v c)).flatten

theorem vecE_wordsOf {α : Type} [Enum α] (v : α → Rg D) : (vecE D α).enc v = pwordsOf v :=
  pvecE_enc v

theorem matE2_wordsOf {α : Type} [Enum α] (M : Fin 2 → α → Rg D) :
    (matE D (Fin 2) α).enc M = pwordsOf (M 0) ++ pwordsOf (M 1) := by
  rw [pmatE2_enc, vecE_wordsOf, vecE_wordsOf]

/-- Families of matrices: per index, the words of row `0`, then of row `1`. -/
theorem funMat_enc {β : Type} [Enum β] (F : β → Fin 2 → Col D.K → Rg D) :
    (FixedEnc.fun (α := β) (matE D (Fin 2) (Col D.K))).enc F =
      ((Enum.list (α := β)).map fun b => pwordsOf (F b 0) ++ pwordsOf (F b 1)).flatten := by
  refine (pfun_enc (α := β) (matE D (Fin 2) (Col D.K)) F).trans ?_
  congr 1
  exact List.map_congr_left fun b _ => matE2_wordsOf (F b)

/-- Two levels of families of matrices, along `Enum (α × β)`. -/
theorem funMat2_enc {α β : Type} [Enum α] [Enum β] (F : α → β → Fin 2 → Col D.K → Rg D) :
    (FixedEnc.fun (α := α) (FixedEnc.fun (α := β) (matE D (Fin 2) (Col D.K)))).enc F =
      ((Enum.list (α := α × β)).map fun p => pwordsOf (F p.1 p.2 0) ++ pwordsOf (F p.1 p.2 1)).flatten := by
  refine (pfun_enc (α := α) (FixedEnc.fun (α := β) (matE D (Fin 2) (Col D.K))) F).trans ?_
  have e : ∀ a, (FixedEnc.fun (α := β) (matE D (Fin 2) (Col D.K))).enc (F a) =
      ((Enum.list (α := β)).map fun b => pwordsOf (F a b 0) ++ pwordsOf (F a b 1)).flatten :=
    fun a => funMat_enc (F a)
  simp only [e]
  rw [enum_prod, map_product, List.flatten_flatten, List.map_map]
  rfl

end Enc

/-! ### The public key of a raw secret -/

variable (D : Dims)

/-- **The public key of a raw secret**: the public key of H2's view. -/
noncomputable def pubK (σ : RawSec D) : MPKt D := (redView D (rawF D σ)).1

/-- `Ā`: the `Wb` columns of the instance's `aB`. -/
def abarR (σ : RawSec D) : Wb D → Rg D := fun v => σ.2.1.aB (.inl v)

/-- `B̄⁽²⁾`: the `Wb` columns of the coins `B⁽²⁾`. -/
def b2barR (σ : RawSec D) : Wb D → Rg D := fun v => σ.2.2.1 (.inl v)

/-- The rows of `B̄`. -/
def bbR (σ : RawSec D) : Fin 2 → Wb D → Rg D := ![abarR D σ, b2barR D σ]

/-- The programming bits. -/
abbrev zrR (σ : RawSec D) : PrI (setting D) Pos → Wb D → Bool := σ.2.2.2.2.2.2

/-- The flooding errors. -/
abbrev flR (σ : RawSec D) : FloodV (setting D) Pos := σ.2.2.2.2.2.1

/-- `b̄ = v_B + B⁽²⁾` on the `Wb` columns. -/
def bbarP (σ : RawSec D) : Wb D → Rg D := fun v => σ.2.1.vB (.inl v) + σ.2.2.1 (.inl v)

/-- The helpers `h_k = v_H k − G⁽²⁾ + H⁽²⁾ k`. -/
noncomputable def hR (σ : RawSec D) : Jh D → Col D.K → Rg D :=
  fun k c => σ.2.1.vH k c - (setting D).G 1 c + σ.2.2.2.1 k c

/-- `H_k = [aH k; H⁽²⁾ k]`. -/
def HR (σ : RawSec D) : Jh D → Matrix (Fin 2) (Col D.K) (Rg D) :=
  fun k => Matrix.of ![σ.2.1.aH k, σ.2.2.2.1 k]

/-- `a_t = Ā ⬝ zr(Z_t) + X^{w x_t} G⁽¹⁾`. -/
noncomputable def aR (σ : RawSec D) (t : Pos) (c : Col D.K) : Rg D :=
  abarR D σ ⬝ᵥ bv (zrR D σ (.inl (t, c))) + (setting D).E.X ^ (wSt * attrN σ.1 t) * (setting D).G 0 c

/-- The bottom rows `cb_t = (B̄⁽²⁾ − b̄) ⬝ zr(Z_t) + e_t + X^{w x_t} G⁽²⁾`. -/
noncomputable def cbR (σ : RawSec D) (t : Pos) (c : Col D.K) : Rg D :=
  (b2barR D σ - bbarP D σ) ⬝ᵥ bv (zrR D σ (.inl (t, c))) + (flR D σ).2.1 t c +
    (setting D).E.X ^ (wSt * attrN σ.1 t) * (setting D).G 1 c

/-- The digit of `A^in_{t,d}`. -/
noncomputable def dinR (σ : RawSec D) (t : Pos) (d : Dig D.K) : Rg D :=
  digits (setting D) (cinMat (aR D σ t) (cbR D σ t)) d

/-- The digit of `A^aut_{t,d}`. -/
noncomputable def dautR (σ : RawSec D) (t : Fin D.b) (d : Dig D.K) : Rg D :=
  digits (setting D) (autGC (helperMap D) (HR D σ) (hR D σ) t) d

variable {D}

theorem redPub_Bb (σ : RawSec D) (ρ : Fin 2) :
    (redPub σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1).Bb ρ = bbR D σ ρ := by
  fin_cases ρ <;> rfl

theorem pubK_B (σ : RawSec D) : (pubK D σ).B = Matrix.of ![σ.2.1.aB, σ.2.2.1] := by
  ext ρ c
  fin_cases ρ <;> rcases c with v | c <;> rfl

theorem pubK_H (σ : RawSec D) : (pubK D σ).H = HR D σ := rfl

theorem pubK_d (σ : RawSec D) : (pubK D σ).d = ![σ.2.1.ad, σ.2.2.2.2.1] := rfl

theorem pubK_a (σ : RawSec D) : (pubK D σ).a = aR D σ := rfl

theorem pubK_A0 (σ : RawSec D) (ρ : Fin 2) (c : Col D.K) :
    (pubK D σ).A0 ρ c = bbR D σ ρ ⬝ᵥ bv (zrR D σ (.inr (.inl c))) + (setting D).G ρ c := by
  fin_cases ρ <;> rfl

theorem cb2_eq (σ : RawSec D) :
    cb2 wSt (redPub σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1) (attrN σ.1) (zrR D σ)
      (redCore σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1) (flR D σ) = cbR D σ := by
  funext t c
  rfl

theorem progA_eq (σ : RawSec D) :
    progA wSt (attrN σ.1) (hpOf (redPub σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1).Bb (zrR D σ)) =
      aR D σ := rfl

theorem pubK_Ain (σ : RawSec D) (t : Pos) (d : Dig D.K) (ρ : Fin 2) (c : Col D.K) :
    (pubK D σ).Ain t d ρ c =
      bbR D σ ρ ⬝ᵥ bv (zrR D σ (.inr (.inr (.inl (t, d, c))))) + dinR D σ t d * (setting D).G ρ c := by
  fin_cases ρ <;> rfl

theorem pubK_Aaut (σ : RawSec D) (t : Fin D.b) (d : Dig D.K) (ρ : Fin 2) (c : Col D.K) :
    (pubK D σ).Aaut t d ρ c =
      (setting D).E.σ ((setting D).kf t) (bbR D σ ρ ⬝ᵥ bv (zrR D σ (.inr (.inr (.inr (t, d, c)))))) +
        dautR D σ t d * (setting D).G ρ c := by
  fin_cases ρ <;> rfl

/-! ### The word of the public key -/

/-- The word of `B`. -/
noncomputable def wB (σ : RawSec D) : List Bool := pwordsOf σ.2.1.aB ++ pwordsOf σ.2.2.1

/-- The word of the `H_k`. -/
noncomputable def wH (σ : RawSec D) : List Bool :=
  ((Enum.list (α := Jh D)).map fun k => pwordsOf (σ.2.1.aH k) ++ pwordsOf (σ.2.2.2.1 k)).flatten

/-- The word of the `a_t`. -/
noncomputable def wa (σ : RawSec D) : List Bool :=
  ((Enum.list (α := Pos × Col D.K)).map fun p => encRM D.N D.K (aR D σ p.1 p.2)).flatten

/-- The row `ρ` of `A₀`. -/
noncomputable def wA0row (σ : RawSec D) (ρ : Fin 2) : List Bool :=
  pwordsOf fun c : Col D.K => bbR D σ ρ ⬝ᵥ bv (zrR D σ (.inr (.inl c))) + (setting D).G ρ c

/-- The row `ρ` of `A^in_{t,d}`. -/
noncomputable def wAinRow (σ : RawSec D) (t : Pos) (d : Dig D.K) (ρ : Fin 2) : List Bool :=
  pwordsOf fun c : Col D.K =>
    bbR D σ ρ ⬝ᵥ bv (zrR D σ (.inr (.inr (.inl (t, d, c))))) + dinR D σ t d * (setting D).G ρ c

/-- The row `ρ` of `A^aut_{t,d}`. -/
noncomputable def wAautRow (σ : RawSec D) (t : Fin D.b) (d : Dig D.K) (ρ : Fin 2) : List Bool :=
  pwordsOf fun c : Col D.K =>
    (setting D).E.σ ((setting D).kf t) (bbR D σ ρ ⬝ᵥ bv (zrR D σ (.inr (.inr (.inr (t, d, c)))))) +
      dautR D σ t d * (setting D).G ρ c

/-- The word of the `A^in`. -/
noncomputable def wAin (σ : RawSec D) : List Bool :=
  ((Enum.list (α := Pos × Dig D.K)).map fun p => wAinRow σ p.1 p.2 0 ++ wAinRow σ p.1 p.2 1).flatten

/-- The word of the `A^aut`. -/
noncomputable def wAaut (σ : RawSec D) : List Bool :=
  ((Enum.list (α := Fin D.b × Dig D.K)).map fun p =>
    wAautRow σ p.1 p.2 0 ++ wAautRow σ p.1 p.2 1).flatten

/-- The word of `d`. -/
noncomputable def wd (σ : RawSec D) : List Bool :=
  encRM D.N D.K σ.2.1.ad ++ encRM D.N D.K σ.2.2.2.2.1

/-- **The word of the public key of a raw secret**, field by field. -/
theorem pubWord_eq (σ : RawSec D) :
    (mpkEnc D).enc (pubK D σ) =
      wB σ ++ (wH σ ++ (wa σ ++ ((wA0row σ 0 ++ wA0row σ 1) ++ (wAin σ ++ (wAaut σ ++ wd σ))))) := by
  show (matE D (Fin 2) (BCol (Wb D) D.K)).enc (pubK D σ).B ++
    ((FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc (pubK D σ).H ++
    ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc (pubK D σ).a ++
    ((matE D (Fin 2) (Col D.K)).enc (pubK D σ).A0 ++
    ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
      (pubK D σ).Ain ++
    ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
      (pubK D σ).Aaut ++ (vecE D (Fin 2)).enc (pubK D σ).d))))) = _
  congr 1
  · exact (matE2_wordsOf (D := D) (pubK D σ).B).trans (by rw [pubK_B]; rfl)
  congr 1
  · exact funMat_enc (D := D) (pubK D σ).H
  congr 1
  · refine (pfun_enc (α := Pos) (vecE D (Col D.K)) (pubK D σ).a).trans ?_
    have e : ∀ t, (vecE D (Col D.K)).enc (aR D σ t) =
        ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (aR D σ t c)).flatten :=
      fun t => pvecE_enc (D := D) (aR D σ t)
    show (List.map (fun t => (vecE D (Col D.K)).enc (aR D σ t)) Enum.list).flatten = _
    simp only [e]
    rw [wa, show (Enum.list (α := Pos × Col D.K)) =
      (Enum.list (α := Pos)).product (Enum.list (α := Col D.K)) from rfl, map_product,
      List.flatten_flatten, List.map_map]
    rfl
  congr 1
  · refine (matE2_wordsOf (D := D) (pubK D σ).A0).trans ?_
    congr 1
  congr 1
  · refine (funMat2_enc (D := D) (pubK D σ).Ain).trans ?_
    congr 1
  congr 1
  · refine (funMat2_enc (D := D) (pubK D σ).Aaut).trans ?_
    congr 1
  · rw [pvecE_enc, pubK_d]
    show [encRM D.N D.K σ.2.1.ad, encRM D.N D.K σ.2.2.2.2.1].flatten = _
    simp [wd]

/-! ### The addends: digits times the gadget -/

/-- **`δ G`, entrywise**: `2^i δ` on the diagonal blocks (`c = (ρ, i)`), `0` elsewhere. -/
theorem mul_G_apply (δ : Rg D) (ρ : Fin 2) (c : Col D.K) :
    δ * (setting D).G ρ c = if ρ = c.1 then (2 : ZMod (2 ^ D.K - 1)) ^ (c.2 : ℕ) • δ else 0 :=
  smul_G_apply D δ ρ c

/-- The digits of the setting are the binary digits. -/
theorem setting_d (x : Rg D) (i : Fin D.K) : (setting D).D.d x i = binaryDigit x i := rfl

/-- **The digit of `A^in_{t,(r,c',i)}`**: the `i`-th binary digit of `a_t c'` (`r = 0`) or of
`cb_t c'` (`r = 1`). -/
theorem dinR_apply (σ : RawSec D) (t : Pos) (r : Fin 2) (c' : Col D.K) (i : Fin D.K) :
    dinR D σ t (r, c', i) = binaryDigit (if r = 0 then aR D σ t c' else cbR D σ t c') i := by
  fin_cases r <;> rfl

/-- **The digit of `A^aut_{t,(r,c',i)}`**: the `i`-th binary digit of the entry of
`C_{g_t} = σ_{g_t}(H_{(t,1)}) − [0; σ_{g_t}(h_{(t,1)})]`. -/
theorem dautR_apply (σ : RawSec D) (t : Fin D.b) (r : Fin 2) (c' : Col D.K) (i : Fin D.K) :
    dautR D σ t (r, c', i) = binaryDigit
      ((setting D).E.σ ((setting D).kf t) (HR D σ (t, 1) r c') -
        if r = 1 then (setting D).E.σ ((setting D).kf t) (hR D σ (t, 1) c') else 0) i := rfl

end AdvancedEncryption.ExpLUT.Prog
