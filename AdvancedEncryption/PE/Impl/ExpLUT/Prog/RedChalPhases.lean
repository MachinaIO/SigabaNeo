import PE.Impl.ExpLUT.Prog.RedChalMath
import PE.Impl.ExpLUT.Prog.DecCoefMath

/-!
# The hash phases of the reduction's challenge (package G2, `chalP`)

The fields `c^aut`, `c^in`, `c₀` of the challenge of `view2` are hash phases
(`RedVM.hashPhase`): for every index `a` (in the order of `Enum`), the word of
`ψ (b̄ ⬝ᵥ bv (zr (ι a))) + e a`, with `ψ = id` (`c^in`, `c₀`) or `ψ = σ_{g_t}` (`c^aut`, the
template `κ_t`):

* `cpPost`, `autPost r`: the post-maps, with their specifications (`hpost_cp`, `hpost_aut`);
* **`exec_hashPhase_enum`**: a hash phase on enumerated columns appends the words
  `encRM (ψ (f ⬝ᵥ bv (g a)) + e a)`;
* `fun2_enc_eq`, `fun3_enc_eq`: nested encodings of families as words along the enumeration of
  the product.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open RedVM

variable {D : Dims}

/-! ### Post-maps -/

/-- `xH := xAcc`. -/
def cpPost : Code := .cp xH xAcc

/-- `xH := σ_{|r|}(xAcc)`. -/
def autPost (r : Fin 200) : Code := .aut xH xAcc r

theorem wr_cpPost : ∀ j ∈ wr cpPost, j = xH ∨ j = xP := by
  intro j hj; simp [cpPost, wr] at hj; exact Or.inl hj

theorem wr_autPost (r : Fin 200) : ∀ j ∈ wr (autPost r), j = xH ∨ j = xP := by
  intro j hj; simp [autPost, wr] at hj; exact Or.inl hj

theorem hpost_cp (w : St) : ∀ i, ∀ w' : St, (w' xAcc).length = D.N * D.K →
    (∀ j, j ∉ phW → w' j = w j) → (fun _ _ => True) i (w' xP) →
    (exec D.N D.K cpPost w' xH).length = D.N * D.K ∧
      decRM D.N D.K (exec D.N D.K cpPost w' xH) = (fun _ x => x) i (decRM D.N D.K (w' xAcc)) ∧
      (fun _ _ => True) (i + 1) (exec D.N D.K cpPost w' xP) := by
  intro i w' hA _ _
  simp only [cpPost, exec, Function.update_self]
  exact ⟨hA, trivial, trivial⟩

/-- `σ_{g_t}` by the template `κ_t` in the register `r` (outside the phase's registers). -/
theorem hpost_aut (t : ℕ) (r : Fin 200) (hr : r ∉ phW) (w : St)
    (hk : w r = List.replicate (κD D t) false) : ∀ i, ∀ w' : St, (w' xAcc).length = D.N * D.K →
    (∀ j, j ∉ phW → w' j = w j) → (fun _ _ => True) i (w' xP) →
    (exec D.N D.K (autPost r) w' xH).length = D.N * D.K ∧
      decRM D.N D.K (exec D.N D.K (autPost r) w' xH) =
        (fun _ x => (setting D).E.σ ((setting D).kf t) x) i (decRM D.N D.K (w' xAcc)) ∧
      (fun _ _ => True) (i + 1) (exec D.N D.K (autPost r) w' xP) := by
  intro i w' hA hfr _
  have hk' : (w' r).length = κD D t := by rw [hfr r hr, hk, List.length_replicate]
  simp only [autPost, exec, Function.update_self, hk', opd_eq hA]
  refine ⟨length_autMW _ _ _ _ D.N_pos, ?_, trivial⟩
  rw [decRM_autMW (κD_pos D t) hA, σ_kf]

/-! ### Hash phases on enumerated columns -/

/-- **A hash phase on enumerated columns** (a post-map `ψ` independent of the round). -/
theorem exec_hashPhase_enum {α : Type} [Enum α] (post : Code) (ψ : Rg D → Rg D)
    (hwp : ∀ j ∈ wr post, j = xH ∨ j = xP) (w : St)
    (hpost : ∀ i, ∀ w' : St, (w' xAcc).length = D.N * D.K → (∀ j, j ∉ phW → w' j = w j) →
      (fun _ _ => True) i (w' xP) → (exec D.N D.K post w' xH).length = D.N * D.K ∧
        decRM D.N D.K (exec D.N D.K post w' xH) = (fun _ x => ψ x) i (decRM D.N D.K (w' xAcc)) ∧
        (fun _ _ => True) (i + 1) (exec D.N D.K post w' xP))
    (f : Wb D → Rg D) (g : α → Wb D → Bool) (e : α → Rg D) (rest restF b₀ : List Bool)
    (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hn : (w xCnt).length = (Enum.list (α := α)).length)
    (hV : w xV = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v)).flatten)
    (hZ : w xZ = ((Enum.list (α := α)).map fun a => (Enum.list (α := Wb D)).map (g a)).flatten ++ rest)
    (hF : w xF = ((Enum.list (α := α)).map fun a => encRM D.N D.K (e a)).flatten ++ restF)
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    exec D.N D.K (hashPhase post) w xOut = bufW (D.N * D.K) b₀ (ys₀ ++
        (Enum.list (α := α)).map fun a => encRM D.N D.K (ψ (f ⬝ᵥ bv (g a)) + e a)) ∧
      exec D.N D.K (hashPhase post) w xZ = rest ∧ exec D.N D.K (hashPhase post) w xF = restF ∧
      (exec D.N D.K (hashPhase post) w xv).length = D.N * D.K ∧
      (exec D.N D.K (hashPhase post) w xBit).length = 1 ∧
      (exec D.N D.K (hashPhase post) w xf).length = D.N * D.K ∧
      ∀ j, j ∉ phW → exec D.N D.K (hashPhase post) w j = w j := by
  have hvs : ∀ v ∈ (Enum.list (α := Wb D)).map (fun v => encRM D.N D.K (f v)),
      v.length = D.N * D.K := by
    intro v hv; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv; exact length_encRM _ _ _
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8⟩ := exec_hashPhase (N := D.N) (K := D.K) D.K_pos post
    (fun _ x => ψ x) (fun _ _ => True) hwp w hpost trivial
    ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v))
    ((Enum.list (α := α)).map fun a => (Enum.list (α := Wb D)).map (g a)) rest
    ((Enum.list (α := α)).map fun a => encRM D.N D.K (e a)) restF b₀ ys₀ hvs
    (fun z hz => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hz; simp)
    (fun z hz => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hz; exact length_encRM _ _ _)
    hys₀ (by rw [hn, List.length_map]) (by simp) hV hZ hF hOut (by rw [hCm, List.length_map])
    hC1 hCNK hZero hv hb hf
  refine ⟨?_, h3, h4, h5, h6, h7, h8⟩
  rw [h1, List.length_map]
  congr 2
  exact phase_words ψ f g e

/-! ### Nested families as words -/

/-- Two levels: words along `Enum (α × β)`. -/
theorem fun2_enc_eq {α β : Type} [Enum α] [Enum β] (F : α → β → Rg D) :
    (FixedEnc.fun (α := α) (vecE D β)).enc F =
      ((Enum.list (α := α × β)).map fun p => encRM D.N D.K (F p.1 p.2)).flatten := by
  rw [fun_enc_eq, enum_prod, map_product, List.flatten_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rw [Function.comp_apply, vecE_enc_eq]

/-- Three levels: words along `Enum (α × β × γ)`. -/
theorem fun3_enc_eq {α β γ : Type} [Enum α] [Enum β] [Enum γ] (F : α → β → γ → Rg D) :
    (FixedEnc.fun (α := α) (FixedEnc.fun (α := β) (vecE D γ))).enc F =
      ((Enum.list (α := α × β × γ)).map fun p => encRM D.N D.K (F p.1 p.2.1 p.2.2)).flatten := by
  rw [fun_enc_eq, enum_prod, map_product, List.flatten_flatten, List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rw [Function.comp_apply, fun2_enc_eq]

/-! ### The fields of the challenge -/

variable (D)

/-- `b̄` of a raw secret: the `Ā` part of `b = v_B + B̄⁽²⁾`. -/
noncomputable def bbarR (σ : RawSec D) : Wb D → Rg D :=
  fun v => (redCore σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1).1 (.inl v)

/-- The challenge of a raw secret for the message `μ`. -/
noncomputable def chalCT (σ : RawSec D) (μ : Bool) : CTt D :=
  shiftCT (half D) (msgR D μ) (redView D (rawF D σ)).2

variable {D}

/-- **`c₀`**: the hash phase over `Col` with `ψ = id`. -/
theorem c0_words (σ : RawSec D) (μ : Bool) :
    ((Enum.list (α := Col (setting D).τ)).map fun c => encRM D.N D.K
        (id (bbarR D σ ⬝ᵥ bv (σ.2.2.2.2.2.2 (.inr (.inl c)))) + σ.2.2.2.2.2.1.2.2.2 c)).flatten =
      (vecE D (Col (setting D).τ)).enc (chalCT D σ μ).c0 :=
  (vecE_enc_eq _).symm

/-- **`c^in`**: the hash phase over `Pos × Dig × Col` with `ψ = id`. -/
theorem cin_words (σ : RawSec D) (μ : Bool) :
    ((Enum.list (α := Pos × Dig (setting D).τ × Col (setting D).τ)).map fun p => encRM D.N D.K
        (id (bbarR D σ ⬝ᵥ bv (σ.2.2.2.2.2.2 (.inr (.inr (.inl p))))) +
          σ.2.2.2.2.2.1.2.2.1 p.1 p.2.1 p.2.2)).flatten =
      (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig (setting D).τ)
        (vecE D (Col (setting D).τ)))).enc (chalCT D σ μ).cin :=
  (fun3_enc_eq (D := D) (chalCT D σ μ).cin).symm

/-- **`c^aut`, the block of `t`**: the hash phase over `Dig × Col` with `ψ = σ_{g_t}`. -/
theorem caut_words (σ : RawSec D) (μ : Bool) (t : Fin D.b) :
    ((Enum.list (α := Dig (setting D).τ × Col (setting D).τ)).map fun p => encRM D.N D.K
        ((setting D).E.σ ((setting D).kf t) (bbarR D σ ⬝ᵥ
          bv (σ.2.2.2.2.2.2 (.inr (.inr (.inr (t, p)))))) + σ.2.2.2.2.2.1.1 t p.1 p.2)).flatten =
      (FixedEnc.fun (α := Dig (setting D).τ) (vecE D (Col (setting D).τ))).enc
        ((chalCT D σ μ).caut t) :=
  (fun2_enc_eq (D := D) ((chalCT D σ μ).caut t)).symm

/-- `c^aut` as the concatenation of its blocks. -/
theorem caut_split (ct : CTt D) :
    (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc ct.caut =
      ((Enum.list (α := Fin D.b)).map fun t =>
        (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K))).enc (ct.caut t)).flatten :=
  fun_enc_eq _ ct.caut

end AdvancedEncryption.ExpLUT.Prog
