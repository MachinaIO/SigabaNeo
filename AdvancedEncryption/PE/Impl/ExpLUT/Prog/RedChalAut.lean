import PE.Impl.ExpLUT.Prog.RedChalH

/-!
# The hash phases of `c^aut` (package G2, `chalP`)

* `exec_ofList_map_inv`: a list of steps by an invariant indexed by the number of steps done;
* **`exec_hashPhase_fin`**: a hash phase over `Fin n` with a post-map depending on the round;
* **`exec_autSteps`**: the `c^aut` blocks of all `t < b` (one hash phase each, `σ_{g_t}` by the
  template `κ_t` in `kR t`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedVM

/-- **A list of steps by an invariant.** -/
theorem exec_ofList_map_inv {N K : ℕ} {α : Type} (l : List α) (step : α → Code)
    (P : ℕ → St → Prop) (w : St) (h0 : P 0 w)
    (hs : ∀ i (hi : i < l.length) w', P i w' → P (i + 1) (exec N K (step l[i]) w')) :
    P l.length (exec N K (ofList (l.map step)) w) := by
  induction l generalizing P w with
  | nil => exact h0
  | cons a l ih =>
    rw [List.map_cons, exec_ofList_cons]
    exact ih (fun i w' => P (i + 1) w') (exec N K (step a) w) (hs 0 (by simp) w h0)
      (fun i hi w' hP => hs (i + 1) (by simp; omega) w' hP)

variable {D : Dims}

/-! ### Hash phases over `Fin n` -/

theorem phase_words_fin (n : ℕ) (φ : ℕ → Rg D → Rg D) (f : Wb D → Rg D)
    (g : Fin n → Wb D → Bool) (e : Fin n → Rg D) :
    (List.range ((List.finRange n).map fun i => (Enum.list (α := Wb D)).map (g i)).length).map
      (fun j => encRM D.N D.K (φ j (hashV (N := D.N) (K := D.K)
        ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v))
        (((List.finRange n).map fun i => (Enum.list (α := Wb D)).map (g i)).getD j [])) +
        decRM D.N D.K (((List.finRange n).map fun i => encRM D.N D.K (e i)).getD j []))) =
      (List.finRange n).map fun i => encRM D.N D.K (φ i.val (f ⬝ᵥ bv (g i)) + e i) := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  have hj : j < n := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj),
    List.getElem_map, List.getElem_map, hashV_enum, decRM_encRM D.K_pos, List.getElem_finRange]
  rfl

/-- **A hash phase over `Fin n`** with a post-map `φ i` and a state `Q i` in `xP`. -/
theorem exec_hashPhase_fin (n : ℕ) (post : Code) (φ : ℕ → Rg D → Rg D)
    (Q : ℕ → List Bool → Prop)
    (hwp : ∀ j ∈ wr post, j = xH ∨ j = xP) (w : St)
    (hpost : ∀ i, ∀ w' : St, (w' xAcc).length = D.N * D.K → (∀ j, j ∉ phW → w' j = w j) →
      Q i (w' xP) → (exec D.N D.K post w' xH).length = D.N * D.K ∧
        decRM D.N D.K (exec D.N D.K post w' xH) = φ i (decRM D.N D.K (w' xAcc)) ∧
        Q (i + 1) (exec D.N D.K post w' xP)) (hQ0 : Q 0 (w xP))
    (f : Wb D → Rg D) (g : Fin n → Wb D → Bool) (e : Fin n → Rg D) (rest restF b₀ : List Bool)
    (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hn : (w xCnt).length = n)
    (hV : w xV = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v)).flatten)
    (hZ : w xZ = ((List.finRange n).map fun i => (Enum.list (α := Wb D)).map (g i)).flatten ++ rest)
    (hF : w xF = ((List.finRange n).map fun i => encRM D.N D.K (e i)).flatten ++ restF)
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    exec D.N D.K (hashPhase post) w xOut = bufW (D.N * D.K) b₀ (ys₀ ++
        (List.finRange n).map fun i => encRM D.N D.K (φ i.val (f ⬝ᵥ bv (g i)) + e i)) ∧
      exec D.N D.K (hashPhase post) w xZ = rest ∧ exec D.N D.K (hashPhase post) w xF = restF ∧
      (exec D.N D.K (hashPhase post) w xv).length = D.N * D.K ∧
      (exec D.N D.K (hashPhase post) w xBit).length = 1 ∧
      (exec D.N D.K (hashPhase post) w xf).length = D.N * D.K ∧
      ∀ j, j ∉ phW → exec D.N D.K (hashPhase post) w j = w j := by
  have hvs : ∀ v ∈ (Enum.list (α := Wb D)).map (fun v => encRM D.N D.K (f v)),
      v.length = D.N * D.K := fun v hv => mem_words hv
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8⟩ := exec_hashPhase (N := D.N) (K := D.K) D.K_pos post
    φ Q hwp w hpost hQ0
    ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (f v))
    ((List.finRange n).map fun i => (Enum.list (α := Wb D)).map (g i)) rest
    ((List.finRange n).map fun i => encRM D.N D.K (e i)) restF b₀ ys₀ hvs
    (fun z hz => by obtain ⟨_, _, rfl⟩ := List.mem_map.mp hz; simp)
    (fun z hz => mem_words hz)
    hys₀ (by rw [hn, List.length_map, List.length_finRange]) (by simp) hV hZ hF hOut
    (by rw [hCm, List.length_map]) hC1 hCNK hZero hv hb hf
  refine ⟨?_, h3, h4, h5, h6, h7, h8⟩
  rw [h1]
  congr 2
  exact phase_words_fin n φ f g e

/-! ### Product enumerations -/

theorem zrBlocks_prod {α β : Type} [Enum α] [Enum β] (zr : PrI (setting D) Pos → Wb D → Bool)
    (ι : α × β → PrI (setting D) Pos) :
    (zrBlocks zr ι).flatten =
      ((Enum.list (α := α)).map fun a => (zrBlocks zr fun b => ι (a, b)).flatten).flatten := by
  rw [zrBlocks, enum_prod, map_product, List.flatten_flatten, List.map_map]
  rfl

theorem fun_vec2_enc {α β γ : Type} [Enum α] [Enum β] [Enum γ] (F : α → β → γ → Rg D) :
    (FixedEnc.fun (α := α) (FixedEnc.fun (α := β) (vecE D γ))).enc F =
      ((Enum.list (α := α)).map fun a =>
        ((Enum.list (α := β × γ)).map fun p => encRM D.N D.K (F a p.1 p.2)).flatten).flatten := by
  rw [fun_enc_eq]
  congr 1
  exact List.map_congr_left fun a _ => fun2_enc_eq (F a)

/-! ### `c^aut` -/

theorem kR_not_mem_phW (t : ℕ) : kR t ∉ phW := by
  simp only [phW, kR, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff, xCnt, xVc, xCc,
    xAcc, xv, xBit, xZ, xF, xf, xS, xO, xOut, xH, xP]
  omega

theorem kR_val {t : ℕ} (ht : t < 32) : kR t = ⟨48 + t, by omega⟩ := by
  simp only [kR, Nat.mod_eq_of_lt ht]

/-- The words of the `c^aut` block of `t`. -/
noncomputable def autWords (σ : RawSec D) (t : Fin D.b) : List (List Bool) :=
  (Enum.list (α := Dig (setting D).τ × Col (setting D).τ)).map fun p => encRM D.N D.K
    ((setting D).E.σ ((setting D).kf t) (bbarR D σ ⬝ᵥ
      bv (σ.2.2.2.2.2.2 (.inr (.inr (.inr (t, p)))))) + σ.2.2.2.2.2.1.1 t p.1 p.2)

theorem mem_autWords {σ : RawSec D} {t : Fin D.b} : ∀ y ∈ autWords σ t, y.length = D.N * D.K :=
  fun _ hy => mem_words hy

/-- **The `c^aut` blocks.** -/
theorem exec_autSteps (σ : RawSec D) (w : St) (restF b₀ : List Bool)
    (ys₀ : List (List Bool)) (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hcnt : (w cAut).length = nE (Dig D.K × Col D.K))
    (hk : ∀ t < D.b, w (kR t) = List.replicate (κD D t) false)
    (hV : w xV = ((Enum.list (α := Wb D)).map fun v => encRM D.N D.K (bbarR D σ v)).flatten)
    (hZ : w xZ = zAutW σ)
    (hF : w xF = (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
      σ.2.2.2.2.2.1.1 ++ restF)
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    exec D.N D.K (ofList ((Enum.list (α := Fin D.b)).map fun t => autStep t.val)) w xOut =
        bufW (D.N * D.K) b₀ (ys₀ ++ ((Enum.list (α := Fin D.b)).map (autWords σ)).flatten) ∧
      exec D.N D.K (ofList ((Enum.list (α := Fin D.b)).map fun t => autStep t.val)) w xF = restF ∧
      (exec D.N D.K (ofList ((Enum.list (α := Fin D.b)).map fun t => autStep t.val)) w xv).length =
        D.N * D.K ∧
      (exec D.N D.K (ofList ((Enum.list (α := Fin D.b)).map fun t => autStep t.val)) w
        xBit).length = 1 ∧
      (exec D.N D.K (ofList ((Enum.list (α := Fin D.b)).map fun t => autStep t.val)) w xf).length =
        D.N * D.K ∧
      ∀ j, j ∉ phW →
        exec D.N D.K (ofList ((Enum.list (α := Fin D.b)).map fun t => autStep t.val)) w j = w j := by
  set zr := σ.2.2.2.2.2.2
  set l := Enum.list (α := Fin D.b)
  let Zt : Fin D.b → List Bool := fun t =>
    (zrBlocks zr fun p : Dig D.K × Col D.K => .inr (.inr (.inr (t, p)))).flatten
  let Ft : Fin D.b → List Bool := fun t =>
    ((Enum.list (α := Dig D.K × Col D.K)).map fun p =>
      encRM D.N D.K (σ.2.2.2.2.2.1.1 t p.1 p.2)).flatten
  have hZ' : w xZ = (l.map Zt).flatten := by rw [hZ, zAutW, zrBlocks_prod]; rfl
  have hF' : w xF = (l.map Ft).flatten ++ restF := by
    rw [hF]; exact congrArg (· ++ restF) (fun_vec2_enc _)
  let P : ℕ → St → Prop := fun i w' =>
    w' xZ = ((l.drop i).map Zt).flatten ∧ w' xF = ((l.drop i).map Ft).flatten ++ restF ∧
    w' xOut = bufW (D.N * D.K) b₀ (ys₀ ++ ((l.take i).map (autWords σ)).flatten) ∧
    (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
    ∀ j, j ∉ phW → w' j = w j
  have key := exec_ofList_map_inv (N := D.N) (K := D.K) l (fun t => autStep t.val) P w
    ⟨by simpa using hZ', by simpa using hF', by simpa using hOut, hv, hb, hf, fun _ _ => rfl⟩
    (fun i hi w' hP => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
      set t := l[i]
      set u := Function.update w' xCnt (w' cAut) with hu
      have huj : ∀ j, j ∉ phW → u j = w j := fun j hj => by
        rw [hu, Function.update_of_ne (show j ≠ xCnt from fun h => hj (by rw [h]; decide)), h7 j hj]
      have hkt : u (kR t.val) = List.replicate (κD D t.val) false := by
        rw [huj _ (kR_not_mem_phW _), hk _ t.isLt]
      have hdz : ((l.drop i).map Zt).flatten = ((zrBlocks zr fun p : Dig D.K × Col D.K =>
          .inr (.inr (.inr (t, p))))).flatten ++ ((l.drop (i + 1)).map Zt).flatten := by
        rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons]
      have hdf : ((l.drop i).map Ft).flatten ++ restF = ((Enum.list (α := Dig D.K × Col D.K)).map
          fun p => encRM D.N D.K (σ.2.2.2.2.2.1.1 t p.1 p.2)).flatten ++
            (((l.drop (i + 1)).map Ft).flatten ++ restF) := by
        rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons, List.append_assoc]
      obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := exec_hashPhase_enum (α := Dig D.K × Col D.K)
        (autPost (kR t.val)) ((setting D).E.σ ((setting D).kf t.val)) (wr_autPost _) u
        (hpost_aut t.val (kR t.val) (kR_not_mem_phW _) u hkt)
        (bbarR D σ) (fun p => zr (.inr (.inr (.inr (t, p))))) (fun p => σ.2.2.2.2.2.1.1 t p.1 p.2)
        ((l.drop (i + 1)).map Zt).flatten (((l.drop (i + 1)).map Ft).flatten ++ restF) b₀
        (ys₀ ++ ((l.take i).map (autWords σ)).flatten)
        (fun y hy => by
          rcases List.mem_append.mp hy with h | h
          · exact hys₀ y h
          · obtain ⟨l', hl, hyl⟩ := List.mem_flatten.mp h
            obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
            exact mem_autWords (t := a) y hyl)
        (by rw [hu, Function.update_self, h7 _ (by decide), hcnt])
        (by rw [huj _ (by decide), hV])
        (by rw [hu, Function.update_of_ne (by decide), h1, hdz]; rfl)
        (by rw [hu, Function.update_of_ne (by decide), h2, hdf])
        (by rw [hu, Function.update_of_ne (by decide), h3])
        (by rw [huj _ (by decide), hCm]) (by rw [huj _ (by decide), hC1])
        (by rw [huj _ (by decide), hCNK]) (by rw [huj _ (by decide), hZero])
        (by rw [hu, Function.update_of_ne (by decide), h4])
        (by rw [hu, Function.update_of_ne (by decide), h5])
        (by rw [hu, Function.update_of_ne (by decide), h6])
      have ex : exec D.N D.K (autStep t.val) w' = exec D.N D.K (hashPhase (autPost (kR t.val))) u :=
        rfl
      rw [ex]
      refine ⟨r2, r3, ?_, r4, r5, r6, fun j hj => by rw [r7 j hj, huj j hj]⟩
      rw [r1, take_succ_of_lt hi, List.map_append, List.flatten_append, List.map_singleton,
        List.flatten_singleton]
      simp only [List.append_assoc]
      rfl)
  obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := key
  refine ⟨?_, ?_, h4, h5, h6, h7⟩
  · rw [h3, List.take_length]
  · rw [h2, List.drop_length]; rfl

end AdvancedEncryption.ExpLUT.Prog.RedChal
