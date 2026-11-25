import PE.Impl.ExpLUT.Prog.RedPubPA0
open SigabaNeo.Tape.RingVM.Buf SigabaNeo.Tape.RingVM.Hash
/-!
# The digit rows of `A^in` and `A^aut` (package G2, `pubP`)

For an entry `a` of the matrix `C` (canonical word in `rCw`) and the digit `i` (the template
`rI` of length `i`), `δ = d_i(a)` (`digit`, **`decRM_digitRW_encRM'`**), then the two rows
`ψ(B̄_ρ ⬝ᵥ bv (g c)) + δ G_{ρ c}` (`ρ = 0, 1`, the same programming block `g`):

* **`exec_dBody`**: one digit;
* **`exec_cBody`**: one entry, its `K` digits;
* **`exec_digRow`**: one row of `C`, its `|Col|` entries.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG AdvancedEncryption.PE
  AdvancedEncryption.PE.BranchingProgram Matrix
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-- **The digits of a canonical word are the binary digits.** -/
theorem decRM_digitRW_encRM' (a : Rg D) (i : ℕ) :
    decRM D.N D.K (digitRW D.N D.K i (encRM D.N D.K a)) = binaryDigit a i := by
  have h := decRM_digitRW_canon (N := D.N) (K := D.K) D.K_pos (length_encRM D.N D.K a) i
  rw [canonW_eq D.K_pos (length_encRM D.N D.K a), decRM_encRM D.K_pos] at h
  exact h

/-- The words of a row of hashes with the digit `δ`. -/
noncomputable def rowW (ψ : Rg D → Rg D) (f : Wb D → Rg D) (g : Col D.K → Wb D → Bool)
    (δ : Rg D) (ρ : Fin 2) : List Bool :=
  ((Enum.list (α := Col D.K)).map fun c =>
    encRM D.N D.K (ψ (f ⬝ᵥ bv (g c)) + δ * (setting D).G ρ c)).flatten

/-- The programming bits of a block. -/
def zBlk (g : Col D.K → Wb D → Bool) : List Bool :=
  ((Enum.list (α := Col D.K)).map fun c => (Enum.list (α := Wb D)).map (g c)).flatten

/-- The specification of a post-map at any state with the templates. -/
def PostSpec (m : Code) (ψ : Rg D → Rg D) : Prop :=
  (∀ j ∈ wr m, j = xH) ∧ ∀ w0 : St, TmplOK D w0 → ∀ w' : St, (w' xAcc).length = D.N * D.K →
    (∀ j, j ∉ xV :: phW → w' j = w0 j) → (exec D.N D.K m w' xH).length = D.N * D.K ∧
      decRM D.N D.K (exec D.N D.K m w' xH) = ψ (decRM D.N D.K (w' xAcc))

theorem postSpec_cp : PostSpec (D := D) cpPost id :=
  ⟨wr_cpPost', fun _ _ w' hA _ => hm_cpPost w' w' hA (fun _ _ => rfl)⟩

/-- The registers of a digit. -/
def dBodyW (zs : Fin 200) : List (Fin 200) := rI :: rRem :: rDel :: zs :: rowPushW

/-- **One digit.** -/
theorem exec_dBody (m : Code) (ψ : Rg D → Rg D) (hm : PostSpec m ψ) (zs : Fin 200)
    (hzs : zs = rRin ∨ zs = ra) (σ : RawSec D) (w : St) (hT : TmplOK D w)
    (hAbar : w rAbar = pwordsOf (abarR D σ)) (hB2bar : w rB2bar = pwordsOf (b2barR D σ))
    (a : Rg D) (hCw : w rCw = encRM D.N D.K a) (i : ℕ) (hi : i < D.K)
    (hRem : (w rRem).length = D.K - i) (g : Col D.K → Wb D → Bool) (rest b₀ acc : List Bool)
    (hZ : w zs = zBlk g ++ rest) (hO : w rOut = pbuf b₀ acc)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K (dBody m zs) w
    w' rOut = pbuf b₀ (acc ++ (rowW ψ (abarR D σ) g (binaryDigit a i) 0 ++
        rowW ψ (b2barR D σ) g (binaryDigit a i) 1)) ∧
      w' zs = rest ∧ (w' rRem).length = D.K - (i + 1) ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ dBodyW zs → w' j = w j := by
  intro w'
  have hz1 : zs ≠ xV := by rcases hzs with h | h <;> subst h <;> decide
  have hzO : zs ≠ rOut := by rcases hzs with h | h <;> subst h <;> decide
  have hzR : zs ≠ rRem := by rcases hzs with h | h <;> subst h <;> decide
  have hzI : zs ≠ rI := by rcases hzs with h | h <;> subst h <;> decide
  have hzD : zs ≠ rDel := by rcases hzs with h | h <;> subst h <;> decide
  have hzp : zs ∉ phW := by rcases hzs with h | h <;> subst h <;> decide
  -- the digit
  set δw := digitRW D.N D.K i (encRM D.N D.K a)
  set w4 := Function.update (Function.update (Function.update w rI ((w cK).drop (w rRem).length))
    rRem (w rRem).tail) rDel δw
  have e4 : exec D.N D.K (ofList [.cp rI cK, .drop rI rRem, .tl rRem, .digit rDel rCw rI]) w = w4 := by
    simp only [exec_ofList_cons, exec_ofList_nil, exec_cp]
    rw [exec_drop_eq (by decide)]
    simp only [exec, Function.update_apply]
    simp only [show (rRem = rI) = False by decide, show (rI = rRem) = False by decide,
      show (rCw = rRem) = False by decide, show (rCw = rI) = False by decide, if_false, if_true]
    have hl : ((w cK).drop (w rRem).length).length = i := by
      rw [List.length_drop, hT.len cK, tm_cK, hRem]; omega
    rw [hl, hCw, opd_eq (length_encRM _ _ _)]
    funext j
    simp only [w4, Function.update_apply]
    split_ifs <;> simp_all <;> rfl
  have hw4 : ∀ j, j ∉ [rI, rRem, rDel] → w4 j = w j := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [w4, Function.update_apply, hj.1, hj.2.1, hj.2.2]
  have hT4 : TmplOK D w4 := tmplOK_frame [rI, rRem, rDel] (by decide) hT hw4
  have hδl : (w4 rDel).length = D.N * D.K := by simp [w4, δw, length_digitRW']
  have hδv : decRM D.N D.K (w4 rDel) = binaryDigit a i := by
    simp [w4, δw, decRM_digitRW_encRM']
  -- the two rows
  obtain ⟨a1, -, a3, a4, a5, a6, a7⟩ := exec_rowPush (D := D) rAbar zs rDel hz1 (by decide)
    (by decide) (by decide) (by decide) m 0 ψ hm.1 w4 hT4 (hm.2 w4 hT4) (abarR D σ)
    (fun v => encRM D.N D.K (abarR D σ v)) (fun _ => length_encRM _ _ _)
    (fun _ => decRM_encRM D.K_pos _) g (binaryDigit a i) rest b₀ acc
    (by rw [hw4 _ (by decide), hAbar]; rfl)
    (by rw [hw4 zs (by simp [hzI, hzR, hzD]), hZ]; rfl) hδl hδv
    (by rw [hw4 _ (by decide), hO]) (by rw [hw4 _ (by decide), hv]) (by rw [hw4 _ (by decide), hb])
    (by rw [hw4 _ (by decide), hf])
  set w5 := exec D.N D.K (ofList (rowPush rAbar zs rDel m 0)) w4
  have hz5 : w5 zs = w zs := by
    rw [a7 zs (by simp [rowPushW, hzO, hz1, hzp]), hw4 zs (by simp [hzI, hzR, hzD])]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := exec_rowPush (D := D) rB2bar zs rDel hz1 (by decide)
    (by decide) (by decide) (by decide) m 1 ψ hm.1 w5 a6 (hm.2 w5 a6) (b2barR D σ)
    (fun v => encRM D.N D.K (b2barR D σ v)) (fun _ => length_encRM _ _ _)
    (fun _ => decRM_encRM D.K_pos _) g (binaryDigit a i) rest b₀ _
    (by rw [a7 _ (by decide), hw4 _ (by decide), hB2bar]; rfl)
    (by rw [hz5, hZ]; rfl) (by rw [a7 _ (by decide), hδl]) (by rw [a7 _ (by decide), hδv]) a1
    a3 a4 a5
  set w6 := exec D.N D.K (ofList (rowPush rB2bar zs rDel m 1)) w5
  have ex : w' = Function.update w6 zs (w6 xZ) := by
    show exec D.N D.K (ofList ([.cp rI cK, .drop rI rRem, .tl rRem, .digit rDel rCw rI] ++
      rowPush rAbar zs rDel m 0 ++ rowPush rB2bar zs rDel m 1 ++ [.cp zs xZ])) w = _
    rw [exec_ofList_append, exec_ofList_append, exec_ofList_append, e4]
    rfl
  have hfr : ∀ j, j ∉ dBodyW zs → w' j = w j := by
    intro j hj
    simp only [dBodyW, List.mem_cons, not_or] at hj
    obtain ⟨j1, j2, j3, j4, j5⟩ := hj
    rw [ex, Function.update_of_ne j4, b7 j (by simpa [rowPushW] using j5),
      a7 j (by simpa [rowPushW] using j5), hw4 j (by simp [j1, j2, j3])]
  refine ⟨?_, by rw [ex, Function.update_self, b2], ?_, ?_, ?_, ?_,
    tmplOK_frame (dBodyW zs) (by rcases hzs with h | h <;> subst h <;> decide) hT hfr, hfr⟩
  · rw [ex, Function.update_of_ne hzO.symm, b1, List.append_assoc]; rfl
  · rw [ex, Function.update_of_ne hzR.symm, b7 _ (by decide), a7 _ (by decide)]
    simp [w4, hRem]; omega
  · rw [ex, Function.update_of_ne (fun h => hzp (by rw [← h]; decide)), b3]
  · rw [ex, Function.update_of_ne (fun h => hzp (by rw [← h]; decide)), b4]
  · rw [ex, Function.update_of_ne (fun h => hzp (by rw [← h]; decide)), b5]

/-! ### Written registers -/

theorem mem_wr_halfC (p : Code) (hp : ∀ j ∈ wr p, j ∈ phW) : ∀ j ∈ wr (halfC p), j ∈ phW := by
  intro j hj
  have e : wr (halfC p) = [xCnt, xCnt] ++ wr hashC ++ (wr p ++ [xf, xF, xS, xO, xOut, xO]) := by
    simp [halfC, hashPhase, phaseBody, wr]
  rw [e] at hj
  simp only [List.mem_append] at hj
  rcases hj with (h | h) | h | h
  · exact mem_of_all (l := [xCnt, xCnt]) (by decide) h
  · rw [wr_hashC] at h; exact mem_of_all (by decide) h
  · exact hp j h
  · exact mem_of_all (l := [xf, xF, xS, xO, xOut, xO]) (by decide) h

theorem mem_wr_rowC (m : Code) (hwm : ∀ j ∈ wr m, j = xH) (ρ : Fin 2) :
    ∀ j ∈ wr (rowC m ρ), j ∈ phW := by
  have hm : ∀ j ∈ wr m, j ∈ phW := fun j h => by rw [hwm j h]; decide
  have hg : ∀ j ∈ wr (gpost m), j ∈ phW := fun j h => by
    rcases wr_gpost m hwm j h with h | h <;> rw [h] <;> decide
  intro j hj
  unfold rowC at hj
  split_ifs at hj
  · simp only [wr, List.mem_append] at hj
    rcases hj with h | h
    · exact mem_wr_halfC _ hg j h
    · exact mem_wr_halfC _ hm j h
  · simp only [wr, List.mem_append] at hj
    rcases hj with h | h
    · exact mem_wr_halfC _ hm j h
    · exact mem_wr_halfC _ hg j h

theorem mem_wr_rowSetC (v z p : Fin 200) : ∀ j ∈ wr (rowSetC v z p), j ∈ xV :: phW := by
  intro j hj
  simp only [rowSetC, wr_ofList, List.flatMap_cons, List.flatMap_nil, wr, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with h | h | h | h | h <;> subst h <;> decide

/-- **The registers a digit writes.** -/
theorem mem_wr_dBody (m : Code) (hwm : ∀ j ∈ wr m, j = xH) (zs : Fin 200) :
    ∀ j ∈ wr (dBody m zs), j ∈ dBodyW zs := by
  intro j hj
  rw [dBody, wr_ofList] at hj
  simp only [List.flatMap_cons, List.flatMap_nil, List.mem_append, List.append_nil] at hj
  have hpw : ∀ j, j ∈ phW → j ∈ dBodyW zs := fun j h => by
    simp only [dBodyW, rowPushW, List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  have hxw : ∀ j, j ∈ xV :: phW → j ∈ dBodyW zs := fun j h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; simp [dBodyW, rowPushW]
    · exact hpw j h
  rcases hj with h | h | h | h | h | h | h | h | h | h | h
  · simp [wr] at h; subst h; simp [dBodyW]
  · simp [wr] at h; subst h; simp [dBodyW]
  · simp [wr] at h; subst h; simp [dBodyW]
  · simp [wr] at h; subst h; simp [dBodyW]
  · exact hxw j (mem_wr_rowSetC _ _ _ j h)
  · exact hpw j (mem_wr_rowC m hwm 0 j h)
  · simp [wr] at h; rcases h with h | h <;> subst h <;> simp [dBodyW, rowPushW, phW]
  · exact hxw j (mem_wr_rowSetC _ _ _ j h)
  · exact hpw j (mem_wr_rowC m hwm 1 j h)
  · simp [wr] at h; rcases h with h | h <;> subst h <;> simp [dBodyW, rowPushW, phW]
  · simp [wr] at h; subst h; simp [dBodyW]

/-! ### One entry -/

/-- The output of an entry `a` of `C`: per digit `i`, the two rows. -/
noncomputable def entW (ψ : Rg D → Rg D) (σ : RawSec D) (G : Fin D.K → Col D.K → Wb D → Bool)
    (a : Rg D) (i : Fin D.K) : List Bool :=
  rowW ψ (abarR D σ) (G i) (binaryDigit a i) 0 ++ rowW ψ (b2barR D σ) (G i) (binaryDigit a i) 1

/-- The registers of an entry. -/
def cBodyW (src zs : Fin 200) : List (Fin 200) := rCw :: src :: cntI :: dBodyW zs

theorem finRange_getElem' {n i : ℕ} (hi : i < (List.finRange n).length) :
    (List.finRange n)[i] = ⟨i, by simpa using hi⟩ := by simp

/-- **One entry of `C`**: its `K` digits. -/
theorem exec_cBody (m : Code) (ψ : Rg D → Rg D) (hm : PostSpec m ψ) (zs : Fin 200)
    (hzs : zs = rRin ∨ zs = ra) (src : Fin 200) (hsrc : src = rCt ∨ src = rCt2) (σ : RawSec D)
    (w : St) (hT : TmplOK D w)
    (hAbar : w rAbar = pwordsOf (abarR D σ)) (hB2bar : w rB2bar = pwordsOf (b2barR D σ))
    (a : Rg D) (restS : List Bool) (hS : w src = encRM D.N D.K a ++ restS)
    (hCw : (w rCw).length = D.N * D.K) (G : Fin D.K → Col D.K → Wb D → Bool)
    (rest b₀ acc : List Bool)
    (hZ : w zs = ((List.finRange D.K).map fun i => zBlk (G i)).flatten ++ rest)
    (hO : w rOut = pbuf b₀ acc)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K (cBody src m zs) w
    w' rOut = pbuf b₀ (acc ++ ((List.finRange D.K).map (entW ψ σ G a)).flatten) ∧
      w' zs = rest ∧ w' src = restS ∧ w' rCw = encRM D.N D.K a ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ cBodyW src zs → w' j = w j := by
  intro w'
  have hsz : src ≠ zs := by
    rcases hsrc with h | h <;> rcases hzs with h' | h' <;> subst h h' <;> decide
  have hsC : src ≠ rCw := by rcases hsrc with h | h <;> subst h <;> decide
  have hsI : src ≠ cntI := by rcases hsrc with h | h <;> subst h <;> decide
  have hsR : src ≠ rRem := by rcases hsrc with h | h <;> subst h <;> decide
  have hzC : zs ≠ rCw := by rcases hzs with h | h <;> subst h <;> decide
  have hzI : zs ≠ cntI := by rcases hzs with h | h <;> subst h <;> decide
  have hzR : zs ≠ rRem := by rcases hzs with h | h <;> subst h <;> decide
  have e1 := exec_mv_pop (N := D.N) (K := D.K) (d := rCw) (s := src) (c := xCNK)
    (by rcases hsrc with h | h <;> subst h <;> decide) (w := w) (v := encRM D.N D.K a) (L := restS)
    (by rw [hCw, hT.len xCNK]; rfl) (by rw [length_encRM, hT.len xCNK]; rfl) hS
  set w1 := Function.update (Function.update w src restS) rCw (encRM D.N D.K a)
  set w0 := Function.update (Function.update w1 cntI (w1 cK)) rRem
    (Function.update w1 cntI (w1 cK) cK)
  have hw0 : ∀ j, j ∉ [rCw, src, cntI, rRem] → w0 j = w j := by
    intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [w0, w1, Function.update_apply, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]
  have hT0 : TmplOK D w0 := tmplOK_frame [rCw, src, cntI, rRem]
    (by rcases hsrc with h | h <;> subst h <;> decide) hT hw0
  have hcK : (w cK).length = D.K := by rw [hT.len cK, tm_cK]
  let P : ℕ → St → Prop := fun i w' =>
    w' rOut = pbuf b₀ (acc ++ (((List.finRange D.K).take i).map (entW ψ σ G a)).flatten) ∧
      w' zs = (((List.finRange D.K).drop i).map fun i => zBlk (G i)).flatten ++ rest ∧
      (w' rRem).length = D.K - i ∧ (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧
      (w' xf).length = D.N * D.K ∧ TmplOK D w' ∧ ∀ j, j ∉ dBodyW zs → j ≠ cntI → w' j = w0 j
  have hcw : cntI ∉ wr (dBody m zs) := fun h => by
    have := mem_wr_dBody m hm.1 zs cntI h
    rcases hzs with h' | h' <;> subst h' <;> revert this <;> decide
  have hsK : src ≠ cK := by rcases hsrc with h | h <;> subst h <;> decide
  have ex : w' = exec D.N D.K (.rep cntI (dBody m zs)) w0 := by
    show exec D.N D.K (ofList [.mv rCw src xCNK, .cp cntI cK, .cp rRem cK, .rep cntI (dBody m zs)]) w = _
    simp only [exec_ofList_cons, exec_ofList_nil, exec_cp]
    rw [e1]
  have hw0K : (w0 cntI).length = D.K := by
    simp [w0, w1, Function.update_apply, hsK, hsK.symm, hcK]
  have h0 : P 0 w0 := by
    have hO0 : w0 rOut = w rOut := hw0 rOut (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨by decide, ?_, by decide, by decide⟩
      rcases hsrc with h | h <;> subst h <;> decide)
    refine ⟨by rw [hO0, hO]; simp, by rw [hw0 zs (by simp [hzC, hsz.symm, hzI, hzR]), hZ]; simp,
      by simp [w0, w1, Function.update_apply, hsK, hsK.symm, hcK], ?_, ?_, ?_, hT0,
      fun _ _ _ => rfl⟩
    · simp [w0, w1, Function.update_apply]
      rcases hsrc with h | h <;> subst h <;> simp [hv]
    · simp [w0, w1, Function.update_apply]
      rcases hsrc with h | h <;> subst h <;> simp [hb]
    · simp [w0, w1, Function.update_apply]
      rcases hsrc with h | h <;> subst h <;> simp [hf]
  have key := exec_rep_inv (N := D.N) (K := D.K) cntI (dBody m zs) hcw P w0 h0 (fun i hi w2 hP _ => by
    rw [hw0K] at hi
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := hP
    set u := Function.update w2 cntI (w2 cntI).tail
    have hu : ∀ j, j ≠ cntI → u j = w2 j := fun j hj => Function.update_of_ne hj _ _
    have hTu : TmplOK D u := tmplOK_frame [cntI] (by decide) p7 fun j hj =>
      hu j (fun h => hj (by simp [h]))
    have hzu : zs ≠ cntI := hzI
    have hfr0 : ∀ j, j ∉ dBodyW zs → j ≠ cntI → j ∉ [rCw, src, cntI, rRem] → u j = w j := fun j h1 h2 h3 => by
      rw [hu j h2, p8 j h1 h2, hw0 j h3]
    have hiF : i < (List.finRange D.K).length := by simpa using hi
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := exec_dBody (D := D) m ψ hm zs hzs σ u hTu
      (by rw [hfr0 _ (by rcases hzs with h | h <;> subst h <;> decide) (by decide) (by
        rcases hsrc with h | h <;> subst h <;> decide), hAbar])
      (by rw [hfr0 _ (by rcases hzs with h | h <;> subst h <;> decide) (by decide) (by
        rcases hsrc with h | h <;> subst h <;> decide), hB2bar])
      a (by rw [hu _ (by decide), p8 _ (by rcases hzs with h | h <;> subst h <;> decide) (by decide)]
            simp [w0, w1, Function.update_apply, hsC, hsC.symm])
      i hi (by rw [hu _ (by decide), p3]) (G ⟨i, hi⟩)
      ((((List.finRange D.K).drop (i + 1)).map fun i => zBlk (G i)).flatten ++ rest) b₀ _
      (by rw [hu _ hzu, p2, List.drop_eq_getElem_cons hiF, finRange_getElem']; simp)
      (by rw [hu _ (by decide), p1]) (by rw [hu _ (by decide), p4]) (by rw [hu _ (by decide), p5])
      (by rw [hu _ (by decide), p6])
    refine ⟨?_, q2, q3, q4, q5, q6, q7, fun j h1 h2 => by rw [q8 j h1, hu j h2, p8 j h1 h2]⟩
    rw [q1, List.take_succ_eq_append_getElem hiF, List.map_append, List.flatten_append,
      finRange_getElem', List.map_singleton, List.flatten_singleton, List.append_assoc]
    rfl)
  rw [hw0K] at key
  obtain ⟨k1, k2, -, k4, k5, k6, k7, k8⟩ := key
  rw [List.take_of_length_le (by simp)] at k1
  rw [List.drop_of_length_le (by simp)] at k2
  have hfr : ∀ j, j ∉ cBodyW src zs → w' j = w j := by
    intro j hj
    simp only [cBodyW, List.mem_cons, not_or] at hj
    rw [ex, k8 j hj.2.2.2 hj.2.2.1, hw0 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hj.1, hj.2.1, hj.2.2.1, fun h => hj.2.2.2 (by simp [dBodyW, h])⟩)]
  refine ⟨by rw [ex, k1], by rw [ex, k2]; simp, ?_, ?_, by rw [ex]; exact k4, by rw [ex]; exact k5,
    by rw [ex]; exact k6, by rw [ex]; exact k7, hfr⟩
  swap
  · rw [ex, k8 rCw (by rcases hzs with h | h <;> subst h <;> decide) (by decide)]
    simp [w0, w1, Function.update_apply]
  rw [ex, k8 src (by
      simp only [dBodyW, rowPushW, List.mem_cons, not_or]
      rcases hsrc with h | h <;> rcases hzs with h' | h' <;> subst h h' <;> decide) hsI]
  simp [w0, w1, Function.update_apply, hsI, hsR, hsC]

/-! ### One row of `C` -/

/-- The registers of a row of `C`. -/
def digRowW (src zs : Fin 200) : List (Fin 200) := cntC :: cBodyW src zs

theorem mem_wr_cBody (m : Code) (hwm : ∀ j ∈ wr m, j = xH) (src zs : Fin 200) :
    ∀ j ∈ wr (cBody src m zs), j ∈ cBodyW src zs := by
  intro j hj
  simp only [cBody, wr_ofList, List.flatMap_cons, List.flatMap_nil, List.mem_append,
    List.append_nil, wr, List.mem_cons, List.not_mem_nil, or_false] at hj
  simp only [cBodyW, List.mem_cons]
  rcases hj with (h | h) | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by simp [dBodyW, h])))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (mem_wr_dBody m hwm zs j h)))

/-- **One row of `C`**: its `|Col|` entries `A c'`, the programming blocks `G c' i`. -/
theorem exec_digRow (m : Code) (ψ : Rg D → Rg D) (hm : PostSpec m ψ) (zs : Fin 200)
    (hzs : zs = rRin ∨ zs = ra) (src : Fin 200) (hsrc : src = rCt ∨ src = rCt2) (σ : RawSec D)
    (w : St) (hT : TmplOK D w)
    (hAbar : w rAbar = pwordsOf (abarR D σ)) (hB2bar : w rB2bar = pwordsOf (b2barR D σ))
    (A : Col D.K → Rg D) (hS : w src = ((Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (A c)).flatten)
    (hCw : (w rCw).length = D.N * D.K) (G : Col D.K → Fin D.K → Col D.K → Wb D → Bool)
    (rest b₀ acc : List Bool)
    (hZ : w zs = ((Enum.list (α := Col D.K)).map fun c' =>
      ((List.finRange D.K).map fun i => zBlk (G c' i)).flatten).flatten ++ rest)
    (hO : w rOut = pbuf b₀ acc)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    let w' := exec D.N D.K (digRow src m zs) w
    w' rOut = pbuf b₀ (acc ++ ((Enum.list (α := Col D.K)).map fun c' =>
        ((List.finRange D.K).map (entW ψ σ (G c') (A c'))).flatten).flatten) ∧
      w' zs = rest ∧ (w' rCw).length = D.N * D.K ∧
      (w' xv).length = D.N * D.K ∧ (w' xBit).length = 1 ∧ (w' xf).length = D.N * D.K ∧
      TmplOK D w' ∧ ∀ j, j ∉ digRowW src zs → w' j = w j := by
  intro w'
  have hsz : src ≠ zs := by
    rcases hsrc with h | h <;> rcases hzs with h' | h' <;> subst h h' <;> decide
  set w0 := Function.update w cntC (w cCol)
  have hw0 : ∀ j, j ≠ cntC → w0 j = w j := fun j hj => Function.update_of_ne hj _ _
  have hT0 : TmplOK D w0 := tmplOK_frame [cntC] (by decide) hT fun j hj =>
    hw0 j (fun h => hj (by simp [h]))
  have hcw : cntC ∉ wr (cBody src m zs) := fun h => by
    have := mem_wr_cBody m hm.1 src zs cntC h
    rcases hsrc with h' | h' <;> rcases hzs with h'' | h'' <;> subst h' h'' <;> revert this <;> decide
  set CL := (Enum.list (α := Col D.K)).map fun c => encRM D.N D.K (A c)
  set ZL := (Enum.list (α := Col D.K)).map fun c' =>
      ((List.finRange D.K).map fun i => zBlk (G c' i)).flatten
  set OL := (Enum.list (α := Col D.K)).map fun c' =>
      ((List.finRange D.K).map (entW ψ σ (G c') (A c'))).flatten
  let P : ℕ → St → Prop := fun k w2 =>
    w2 rOut = pbuf b₀ (acc ++ (OL.take k).flatten) ∧ w2 src = (CL.drop k).flatten ∧
      w2 zs = (ZL.drop k).flatten ++ rest ∧ (w2 rCw).length = D.N * D.K ∧
      (w2 xv).length = D.N * D.K ∧ (w2 xBit).length = 1 ∧
      (w2 xf).length = D.N * D.K ∧ TmplOK D w2 ∧ ∀ j, j ∉ cBodyW src zs → j ≠ cntC → w2 j = w0 j
  have hsC : src ≠ cntC := by rcases hsrc with h | h <;> subst h <;> decide
  have hzC : zs ≠ cntC := by rcases hzs with h | h <;> subst h <;> decide
  have h0 : P 0 w0 := ⟨by rw [hw0 _ (by decide), hO]; simp, by rw [hw0 _ hsC, hS]; simp,
    by rw [hw0 _ hzC, hZ]; simp, by rw [hw0 _ (by decide), hCw], by rw [hw0 _ (by decide), hv],
    by rw [hw0 _ (by decide), hb], by rw [hw0 _ (by decide), hf], hT0, fun _ _ _ => rfl⟩
  have hlen : (w0 cntC).length = pnE (Col D.K) := by simp [w0, hT.len cCol]
  have key := exec_rep_inv (N := D.N) (K := D.K) cntC (cBody src m zs) hcw P w0 h0
    (fun k hk w2 hP _ => by
    rw [hlen] at hk
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hP
    set u := Function.update w2 cntC (w2 cntC).tail
    have hu : ∀ j, j ≠ cntC → u j = w2 j := fun j hj => Function.update_of_ne hj _ _
    have hTu : TmplOK D u := tmplOK_frame [cntC] (by decide) p8 fun j hj =>
      hu j (fun h => hj (by simp [h]))
    have hkC : k < CL.length := by simpa [CL] using hk
    have hkZ : k < ZL.length := by simpa [ZL] using hk
    have hkO : k < OL.length := by simpa [OL] using hk
    have hnot : ∀ r, r = rAbar ∨ r = rB2bar → r ∉ cBodyW src zs := by
      intro r hr
      rcases hr with h | h <;> rcases hsrc with h' | h' <;> rcases hzs with h'' | h'' <;>
        subst h h' h'' <;> decide
    obtain ⟨q1, q2, q3, q3', q4, q5, q6, q7, q8⟩ := exec_cBody (D := D) m ψ hm zs hzs src hsrc σ u hTu
      (by rw [hu _ (by decide), p9 _ (hnot _ (Or.inl rfl)) (by decide), hw0 _ (by decide), hAbar])
      (by rw [hu _ (by decide), p9 _ (hnot _ (Or.inr rfl)) (by decide), hw0 _ (by decide), hB2bar])
      (A (Enum.list (α := Col D.K))[k]) (CL.drop (k + 1)).flatten
      (by rw [hu _ hsC, p2, flatten_drop_cons hkC]; simp [CL])
      (by rw [hu _ (by decide), p4]) (G (Enum.list (α := Col D.K))[k])
      ((ZL.drop (k + 1)).flatten ++ rest) b₀ _
      (by rw [hu _ hzC, p3, flatten_drop_cons hkZ, List.append_assoc]; simp [ZL])
      (by rw [hu _ (by decide), p1]) (by rw [hu _ (by decide), p5]) (by rw [hu _ (by decide), p6])
      (by rw [hu _ (by decide), p7])
    set u1 := exec D.N D.K (cBody src m zs) u
    refine ⟨?_, q3, q2, ?_, q4, q5, q6, q7, fun j h1 h2 => by rw [q8 j h1, hu j h2, p9 j h1 h2]⟩
    · rw [q1, List.take_succ_eq_append_getElem hkO, List.flatten_append, List.flatten_singleton,
        List.append_assoc]
      simp [OL]
    · rw [q3']; exact length_encRM _ _ _)
  rw [hlen] at key
  obtain ⟨k1, -, k3, k4, k5, k6, k7, k8, k9⟩ := key
  rw [List.take_of_length_le (by simp [OL])] at k1
  rw [List.drop_of_length_le (by simp [ZL])] at k3
  have ex : w' = exec D.N D.K (.rep cntC (cBody src m zs)) w0 := rfl
  rw [ex]
  refine ⟨k1, by rw [k3]; simp, k4, k5, k6, k7, k8, fun j hj => ?_⟩
  simp only [digRowW, List.mem_cons, not_or] at hj
  rw [k9 j hj.2 hj.1, hw0 j hj.1]

end AdvancedEncryption.ExpLUT.Prog.RedPubP