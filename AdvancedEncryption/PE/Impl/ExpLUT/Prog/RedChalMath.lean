import PE.Impl.ExpLUT.AH.RedCompsR
import PE.Impl.ExpLUT.Prog.DecMachineCode
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMHash
/-!
# The words of the reduction's public data (package G2, `pubP`/`chalP`)

Bridges between the `RingVM` kernels (`SigabaNeo.Tape.RingVM.Hash.hashC`, `SigabaNeo.Tape.RingVM.Hash.hashPhase`) and the encodings of
the reduction's secret (`rawEnc`) and outputs (`mpkEnc`, `ctEnc`):

* **`hashV_enum`**: the hash of the words of `f : Wb → Rg` with the bits of `z : Wb → Bool` (in the
  order of `Enum`) is `f ⬝ᵥ bv z`, the binary hash of `hpOf`/`ct2`/`cb2`;
* **`zrEnc_enc`**, `zrEnc_split`: the programming bits, one block of `m̄` bits per column `i`
  (in the order of `Enum (PrI …)`), and its four parts (`Z_t`, `R₀`, `R^in`, `R^aut`);
* `floodEnc_split`, `rawEnc_split`: the words of the raw secret, field by field;
* **`phase_words`**: the output of a hash phase on enumerated blocks is the list of the words
  `encRM (φ a (f ⬝ᵥ bv (g a)) + e a)` in the order of `Enum`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable {D : Dims}

/-! ### Sums along enumerations -/

theorem sum_map_enum {α M : Type} [Enum α] [Fintype α] [AddCommMonoid M] (g : α → M) :
    ((Enum.list (α := α)).map g).sum = ∑ a, g a := by
  classical
  rw [← List.sum_toFinset g Enum.nodup]
  congr 1
  ext a; simp [Enum.complete a]

/-- **The hash of enumerated words is the binary hash.** -/
theorem hashV_enum (f : Wb D → Rg D) (z : Wb D → Bool) :
    SigabaNeo.Tape.RingVM.Hash.hashV (N := D.N) (K := D.K)
        ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v))
        ((Enum.list (α := Wb D)).map z) = f ⬝ᵥ bv z := by
  rw [SigabaNeo.Tape.RingVM.Hash.hashV, List.zipWith_map, List.zipWith_self, sum_map_enum]
  simp only [dotProduct, bv, bitVal, decRM_encRM D.K_pos]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp_all

/-! ### Lists along enumerations -/

theorem range_map_getD {β γ : Type} (l : List β) (d : β) (F : β → γ) :
    (List.range l.length).map (fun j => F (l.getD j d)) = l.map F := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

/-- **The words of a hash phase on enumerated blocks** (a post-map `ψ` independent of the
round). -/
theorem phase_words {α : Type} [Enum α] (ψ : Rg D → Rg D) (f : Wb D → Rg D)
    (g : α → Wb D → Bool) (e : α → Rg D) :
    (List.range (Enum.list (α := α)).length).map (fun j =>
        encRM D.N D.K (ψ (SigabaNeo.Tape.RingVM.Hash.hashV (N := D.N) (K := D.K)
          ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v))
          (((Enum.list (α := α)).map fun a => (Enum.list (α := Wb D)).map (g a)).getD j [])) +
          decRM D.N D.K (((Enum.list (α := α)).map fun a => encRM D.N D.K (e a)).getD j []))) =
      (Enum.list (α := α)).map fun a => encRM D.N D.K (ψ (f ⬝ᵥ bv (g a)) + e a) := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  have hj : j < (Enum.list (α := α)).length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj),
    List.getElem_map, List.getElem_map, hashV_enum, decRM_encRM D.K_pos]

/-! ### The programming bits -/

theorem bitEnc_fun_enc {α : Type} [Enum α] (z : α → Bool) :
    (FixedEnc.fun (α := α) bitEnc).enc z = (Enum.list (α := α)).map z := by
  rw [fun_enc_eq]
  have : ∀ l : List α, (l.map fun a => bitEnc.enc (z a)).flatten = l.map z := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, List.flatten_cons, ih]; rfl
  exact this _

/-- **The programming bits**: one block of `m̄` bits per column. -/
theorem zrEnc_enc (zr : PrI (setting D) Pos → Wb D → Bool) :
    (zrEnc D).enc zr =
      ((Enum.list (α := PrI (setting D) Pos)).map fun i => (Enum.list (α := Wb D)).map (zr i)).flatten := by
  rw [zrEnc, fun_enc_eq]
  congr 1
  exact List.map_congr_left fun i _ => bitEnc_fun_enc (zr i)

/-- The bits of the columns of a part of the programming. -/
def zrBlocks {α : Type} [Enum α] (zr : PrI (setting D) Pos → Wb D → Bool)
    (ι : α → PrI (setting D) Pos) : List (List Bool) :=
  (Enum.list (α := α)).map fun a => (Enum.list (α := Wb D)).map (zr (ι a))

/-- **The four parts of the programming bits**: `Z_t`, `R₀`, `R^in_{t,d}`, `R^aut_{t,d}`. -/
theorem zrEnc_split (zr : PrI (setting D) Pos → Wb D → Bool) :
    (zrEnc D).enc zr =
      (zrBlocks zr fun p : Pos × Col D.K => .inl p).flatten ++
        ((zrBlocks zr fun c : Col D.K => .inr (.inl c)).flatten ++
        ((zrBlocks zr fun p : Pos × Dig D.K × Col D.K => .inr (.inr (.inl p))).flatten ++
          (zrBlocks zr fun p : Fin D.b × Dig D.K × Col D.K => .inr (.inr (.inr p))).flatten)) := by
  rw [zrEnc_enc, enum_sum, enum_sum, enum_sum]
  simp only [List.map_append, List.map_map, List.flatten_append, zrBlocks]
  rfl

/-! ### The flooding errors and the raw secret -/

/-- **The flooding errors, part by part.** -/
theorem floodEnc_split (fl : FloodV (setting D) Pos) :
    (floodEnc D).enc fl =
      (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc fl.1 ++
        ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc fl.2.1 ++
        ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc fl.2.2.1 ++
          (vecE D (Col D.K)).enc fl.2.2.2)) := rfl

/-- **The raw secret, field by field.** -/
theorem rawEnc_split (σ : RawSec D) :
    (rawEnc D).enc σ =
      encAttribute w8 σ.1 ++ ((instEnc D).enc σ.2.1 ++ ((vecE D (BCol (Wb D) D.K)).enc σ.2.2.1 ++
        ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc σ.2.2.2.1 ++
        ((rEnc D).enc σ.2.2.2.2.1 ++ ((floodEnc D).enc σ.2.2.2.2.2.1 ++
          (zrEnc D).enc σ.2.2.2.2.2.2))))) := rfl

/-- The instance as the words of its two row vectors. -/
theorem instEnc_enc (i : CInst D) :
    (instEnc D).enc i = (vecE D (Fin (circParamsD D).rows)).enc (toPair D i).1 ++
      (vecE D (Fin (circParamsD D).rows)).enc (toPair D i).2 := rfl

end AdvancedEncryption.ExpLUT.Prog
