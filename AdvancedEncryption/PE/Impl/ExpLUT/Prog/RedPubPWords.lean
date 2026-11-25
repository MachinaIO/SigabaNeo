import PE.Impl.ExpLUT.Prog.RedPubPCode
/-!
# The fields of the raw secret as words (package G2, `pubP`)

**`prawEnc_fields`**: the word of the raw secret is the concatenation of the fields that
`parseC` pops (`pfields σ`, in order) and the programming bits of `R^aut` (`pzAutW σ`, left in
`ra`). Copies (under new names) of `RedChalMath.zrEnc_split`, `rawEnc_split`, which are not
imported here.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable {D : Dims}

/-! ### The programming bits -/

theorem pbitEnc_fun_enc {α : Type} [Enum α] (z : α → Bool) :
    (FixedEnc.fun (α := α) bitEnc).enc z = (Enum.list (α := α)).map z := by
  rw [pfun_enc]
  have : ∀ l : List α, (l.map fun a => bitEnc.enc (z a)).flatten = l.map z := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, List.flatten_cons, ih]; rfl
  exact this _

/-- The bits of the columns of a part of the programming. -/
def pzrBlocks {α : Type} [Enum α] (zr : PrI (setting D) Pos → Wb D → Bool)
    (ι : α → PrI (setting D) Pos) : List (List Bool) :=
  (Enum.list (α := α)).map fun a => (Enum.list (α := Wb D)).map (zr (ι a))

theorem pzrEnc_split (zr : PrI (setting D) Pos → Wb D → Bool) :
    (zrEnc D).enc zr =
      (pzrBlocks zr fun p : Pos × Col D.K => .inl p).flatten ++
        ((pzrBlocks zr fun c : Col D.K => .inr (.inl c)).flatten ++
        ((pzrBlocks zr fun p : Pos × Dig D.K × Col D.K => .inr (.inr (.inl p))).flatten ++
          (pzrBlocks zr fun p : Fin D.b × Dig D.K × Col D.K => .inr (.inr (.inr p))).flatten)) := by
  rw [zrEnc, pfun_enc]
  have e : ∀ i, (FixedEnc.fun (α := Wb D) bitEnc).enc (zr i) = (Enum.list (α := Wb D)).map (zr i) :=
    fun i => pbitEnc_fun_enc (zr i)
  simp only [e]
  rw [enum_sum, enum_sum, enum_sum]
  simp only [List.map_append, List.map_map, List.flatten_append, pzrBlocks]
  rfl

theorem plength_zrBlocks {α : Type} [Enum α] (zr : PrI (setting D) Pos → Wb D → Bool)
    (ι : α → PrI (setting D) Pos) : (pzrBlocks zr ι).flatten.length = pnE α * pnE (Wb D) := by
  rw [length_flatten_of (n := pnE (Wb D)), pzrBlocks, List.length_map]
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  simp

/-! ### The fields -/

section Fields

variable (σ : RawSec D)

/-- `H⁽²⁾`. -/
noncomputable def ph2W : List Bool := (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc σ.2.2.2.1

/-- The flooding errors of `A^aut` (dropped). -/
noncomputable def pfl1W : List Bool :=
  (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc σ.2.2.2.2.2.1.1

/-- The flooding errors `e_t` of the bottom rows. -/
noncomputable def pfl2W : List Bool :=
  (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc σ.2.2.2.2.2.1.2.1

/-- The other flooding errors (dropped). -/
noncomputable def pfl3W : List Bool :=
  (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
    σ.2.2.2.2.2.1.2.2.1 ++ (vecE D (Col D.K)).enc σ.2.2.2.2.2.1.2.2.2

/-- The programming bits of `Z_t`. -/
def pzZW : List Bool := (pzrBlocks σ.2.2.2.2.2.2 fun p : Pos × Col D.K => .inl p).flatten

/-- The programming bits of `R₀`. -/
def pzR0W : List Bool := (pzrBlocks σ.2.2.2.2.2.2 fun c : Col D.K => .inr (.inl c)).flatten

/-- The programming bits of `R^in`. -/
def pzRinW : List Bool :=
  (pzrBlocks σ.2.2.2.2.2.2 fun p : Pos × Dig D.K × Col D.K => .inr (.inr (.inl p))).flatten

/-- The programming bits of `R^aut`. -/
def pzAutW : List Bool :=
  (pzrBlocks σ.2.2.2.2.2.2 fun p : Fin D.b × Dig D.K × Col D.K => .inr (.inr (.inr p))).flatten

/-- **The fields popped by `parseC`**, in order. -/
noncomputable def pfields : List (List Bool) :=
  [encAttribute w8 σ.1, pwordsOf σ.2.1.aB, encRM D.N D.K σ.2.1.ad,
    ringWords (plainHL D σ.2.1.aH), ringWords (keyHL D σ.2.1.aH),
    pwordsOf σ.2.1.vB, encRM D.N D.K σ.2.1.vd,
    ringWords (plainHL D σ.2.1.vH), ringWords (keyHL D σ.2.1.vH),
    pwordsOf σ.2.2.1, ph2W σ, encRM D.N D.K σ.2.2.2.2.1, pfl1W σ, pfl2W σ, pfl3W σ,
    pzZW σ, pzR0W σ, pzRinW σ]

end Fields

/-- **The raw secret as its fields.** -/
theorem prawEnc_fields (σ : RawSec D) :
    (rawEnc D).enc σ = (pfields σ).flatten ++ pzAutW σ := by
  have e1 : (rawEnc D).enc σ =
      encAttribute w8 σ.1 ++ ((instEnc D).enc σ.2.1 ++ ((vecE D (BCol (Wb D) D.K)).enc σ.2.2.1 ++
        ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc σ.2.2.2.1 ++
        ((rEnc D).enc σ.2.2.2.2.1 ++ ((floodEnc D).enc σ.2.2.2.2.2.1 ++
          (zrEnc D).enc σ.2.2.2.2.2.2))))) := rfl
  have e2 : (instEnc D).enc σ.2.1 = (vecE D (Fin (circParamsD D).rows)).enc (toPair D σ.2.1).1 ++
      (vecE D (Fin (circParamsD D).rows)).enc (toPair D σ.2.1).2 := rfl
  have e3 : (floodEnc D).enc σ.2.2.2.2.2.1 = pfl1W σ ++ (pfl2W σ ++ pfl3W σ) := by
    show _ ++ (_ ++ (_ ++ _)) = _
    simp [pfl1W, pfl2W, pfl3W]
  rw [e1, e2, instA_words, instV_words, e3, pzrEnc_split, vecE_wordsOf]
  simp only [pfields, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
    rEnc_enc]
  rfl

/-! ### Lengths -/

theorem length_plainHL {β : Type} (F : Jh D → Col D.K → β) :
    (plainHL D F).length = D.K * pnE (Jh D) := by
  simp [plainHL, List.length_flatten, Function.comp_def, List.map_const', List.sum_replicate]

theorem length_keyHL {β : Type} (F : Jh D → Col D.K → β) :
    (keyHL D F).length = D.K * pnE (Jh D) := by
  simp [keyHL, List.length_flatten, Function.comp_def, List.map_const', List.sum_replicate]

theorem length_ringWords (l : List (Rg D)) : (ringWords l).length = l.length * (D.N * D.K) := by
  rw [ringWords, length_flatten_of (n := D.N * D.K)]
  · simp
  · intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _

theorem length_pwordsOf {α : Type} [Enum α] (v : α → Rg D) :
    (pwordsOf v).length = pnE α * (D.N * D.K) := by
  rw [pwordsOf, length_flatten_of (n := D.N * D.K)]
  · simp
  · intro x hx; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx; exact length_encRM _ _ _

end AdvancedEncryption.ExpLUT.Prog.RedPubP
