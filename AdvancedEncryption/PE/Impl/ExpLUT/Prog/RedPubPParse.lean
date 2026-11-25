import PE.Impl.ExpLUT.Prog.RedPubPWords
set_option linter.unusedSimpArgs false

/-!
# The templates and the parse (package G2, `pubP`)

* `isT r`: the template registers (never written by `pubC`); **`TmplOK D w`**: they hold their
  templates (`tm D`), `r1` the word of `1`; `tmplOK_initW1`, `tmplOK_exec` (a code writing no
  template register keeps it);
* `exec_mv_popF`, `exec_drop_popF`: popping the `k`-th field of a list of fields;
* **`exec_parseC`**: `parseC` splits the raw secret into the registers.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open AdvancedEncryption.ExpLUT.Prog.RedVM

/-! ### Templates -/

/-- The template registers. -/
def isT (r : Fin 200) : Bool :=
  r.val = 2 || (4 ≤ r.val && r.val ≤ 22) || (72 ≤ r.val && r.val < 112) || r.val = 152 ||
    r.val = 158 || r.val = 159 || r.val = 160

variable (D : Dims)

/-- **The templates are in place.** -/
def TmplOK (w : St) : Prop :=
  (∀ r : Fin 200, isT r = true → r ≠ r1 → w r = List.replicate (tm D r) false) ∧
    w r1 = true :: List.replicate (D.N * D.K - 1) false

variable {D}

theorem TmplOK.get {w : St} (h : TmplOK D w) (r : Fin 200) (hr : isT r = true := by decide)
    (hr1 : r ≠ r1 := by decide) : w r = List.replicate (tm D r) false := h.1 r hr hr1

theorem TmplOK.len {w : St} (h : TmplOK D w) (r : Fin 200) (hr : isT r = true := by decide)
    (hr1 : r ≠ r1 := by decide) : (w r).length = tm D r := by rw [h.get r hr hr1, List.length_replicate]

theorem tmplOK_initW1 (a b : List Bool) :
    TmplOK D (RedIO.initW1 ra rb r1 (tm D) a b) := by
  refine ⟨fun r hr hr1 => ?_, ?_⟩
  · have ha : r ≠ ra := fun h => by subst h; revert hr; decide
    have hb : r ≠ rb := fun h => by subst h; revert hr; decide
    simp [RedIO.initW1, RedIO.initW, Function.update_of_ne hr1, ha, hb]
  · simp [RedIO.initW1]; rfl

theorem tmplOK_exec (c : Code) (hc : (wr c).all (fun r => !isT r) = true) {w : St}
    (h : TmplOK D w) : TmplOK D (exec D.N D.K c w) := by
  have hn : ∀ r, isT r = true → exec D.N D.K c w r = w r := fun r hr =>
    exec_not_mem c w r fun hm => by
      have := List.all_eq_true.mp hc r hm
      simp [hr] at this
  exact ⟨fun r hr hr1 => by rw [hn r hr, h.get r hr hr1],
    by rw [hn r1 (by decide), h.2]⟩

/-! ### The template lengths -/

@[simp] theorem tm_r1 : tm D r1 = D.N * D.K - 1 := rfl
@[simp] theorem tm_rOut : tm D rOut = pencLen (mpkEnc D) := rfl
@[simp] theorem tm_c128 : tm D c128 = 128 := rfl
@[simp] theorem tm_rAttr : tm D rAttr = 128 := rfl
@[simp] theorem tm_cBC : tm D cBC = pnE (BCol (Wb D) D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_rAB : tm D rAB = pnE (BCol (Wb D) D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_rVB : tm D rVB = pnE (BCol (Wb D) D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_rB2 : tm D rB2 = pnE (BCol (Wb D) D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_cJK : tm D cJK = D.K * pnE (Jh D) * (D.N * D.K) := rfl
@[simp] theorem tm_rAHp : tm D rAHp = D.K * pnE (Jh D) * (D.N * D.K) := rfl
@[simp] theorem tm_rAHk : tm D rAHk = D.K * pnE (Jh D) * (D.N * D.K) := rfl
@[simp] theorem tm_rVHp : tm D rVHp = D.K * pnE (Jh D) * (D.N * D.K) := rfl
@[simp] theorem tm_rVHk : tm D rVHk = D.K * pnE (Jh D) * (D.N * D.K) := rfl
@[simp] theorem tm_cH2 : tm D cH2 = pnE (Jh D) * (pnE (Col D.K) * (D.N * D.K)) := rfl
@[simp] theorem tm_rH2 : tm D rH2 = pnE (Jh D) * (pnE (Col D.K) * (D.N * D.K)) := rfl
@[simp] theorem tm_cFl1 : tm D cFl1 = pnE (Fin D.b) * (pnE (Dig D.K) * (pnE (Col D.K) * (D.N * D.K))) := rfl
@[simp] theorem tm_cK : tm D cK = D.K := rfl
@[simp] theorem tm_cJ : tm D cJ = pnE (Jh D) := rfl
@[simp] theorem tm_cSkip : tm D cSkip = (pnE (Jh D) - 1) * (D.N * D.K) := rfl
@[simp] theorem tm_cMb : tm D cMb = pnE (Wb D) * (D.N * D.K) := rfl
@[simp] theorem tm_rAbar : tm D rAbar = pnE (Wb D) * (D.N * D.K) := rfl
@[simp] theorem tm_rB2bar : tm D rB2bar = pnE (Wb D) * (D.N * D.K) := rfl
@[simp] theorem tm_rNV : tm D rNV = pnE (Wb D) * (D.N * D.K) := rfl
@[simp] theorem tm_cColW : tm D cColW = pnE (Col D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_rZcol : tm D rZcol = pnE (Col D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_rCt : tm D rCt = pnE (Col D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_rCt2 : tm D rCt2 = pnE (Col D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_cPos : tm D cPos = pnE Pos := rfl
@[simp] theorem tm_cZ : tm D cZ = pnE (Pos × Col D.K) * pnE (Wb D) := rfl
@[simp] theorem tm_rZ : tm D rZ = pnE (Pos × Col D.K) * pnE (Wb D) := rfl
@[simp] theorem tm_cPC : tm D cPC = pnE Pos * (pnE (Col D.K) * (D.N * D.K)) := rfl
@[simp] theorem tm_rFe : tm D rFe = pnE Pos * (pnE (Col D.K) * (D.N * D.K)) := rfl
@[simp] theorem tm_rKA : tm D rKA = pnE Pos * (pnE (Col D.K) * (D.N * D.K)) := rfl
@[simp] theorem tm_rKC : tm D rKC = pnE Pos * (pnE (Col D.K) * (D.N * D.K)) := rfl
@[simp] theorem tm_cFl3 : tm D cFl3 =
    pnE Pos * (pnE (Dig D.K) * (pnE (Col D.K) * (D.N * D.K))) + pnE (Col D.K) * (D.N * D.K) := rfl
@[simp] theorem tm_cZblk : tm D cZblk = pnE (Col D.K) * pnE (Wb D) := rfl
@[simp] theorem tm_rR0 : tm D rR0 = pnE (Col D.K) * pnE (Wb D) := rfl
@[simp] theorem tm_cRin : tm D cRin = pnE (Pos × Dig D.K × Col D.K) * pnE (Wb D) := rfl
@[simp] theorem tm_rRin : tm D rRin = pnE (Pos × Dig D.K × Col D.K) * pnE (Wb D) := rfl
@[simp] theorem tm_cCol : tm D cCol = pnE (Col D.K) := rfl
@[simp] theorem tm_cNK2 : tm D cNK2 = 2 * (D.N * D.K) := rfl
@[simp] theorem tm_rAd : tm D rAd = D.N * D.K := rfl
@[simp] theorem tm_rD2 : tm D rD2 = D.N * D.K := rfl
@[simp] theorem tm_rCw : tm D rCw = D.N * D.K := rfl
@[simp] theorem tm_rBit : tm D rBit = 1 := rfl
@[simp] theorem tm_xCm : tm D xCm = pnE (Wb D) := rfl
@[simp] theorem tm_xv : tm D xv = D.N * D.K := rfl
@[simp] theorem tm_xBit : tm D xBit = 1 := rfl
@[simp] theorem tm_xC1 : tm D xC1 = 1 := rfl
@[simp] theorem tm_xCNK : tm D xCNK = D.N * D.K := rfl
@[simp] theorem tm_xZero : tm D xZero = D.N * D.K := rfl
@[simp] theorem tm_xf : tm D xf = D.N * D.K := rfl

theorem tm_rhoR (j : ℕ) (hj : j < 8) : tm D (rhoR j) = 2 * D.N - wSt * 2 ^ (7 - j) := by
  simp only [tm, rhoR, Nat.mod_eq_of_lt hj]
  rw [if_pos (by omega)]
  congr 3; omega

theorem tm_kR (t : ℕ) (ht : t < 32) : tm D (kR t) = κD D t := by
  simp only [tm, kR, Nat.mod_eq_of_lt ht]
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1; omega

/-! ### Popping fields -/

/-- Pop the field `k` of a list of fields. -/
theorem exec_mv_popF {N K : ℕ} {d s c : Fin 200} (h : ¬(d = s ∨ d = c ∨ s = c)) {w : St}
    (F : List (List Bool)) (k : ℕ) (hk : k < F.length) (rest : List Bool)
    (hd : (w d).length = F[k].length) (hc : (w c).length = F[k].length)
    (hs : w s = (F.drop k).flatten ++ rest) :
    exec N K (.mv d s c) w =
      Function.update (Function.update w s ((F.drop (k + 1)).flatten ++ rest)) d F[k] := by
  refine exec_mv_pop h (by rw [hd, hc]) hc.symm ?_
  rw [hs, flatten_drop_cons hk, List.append_assoc]

/-- Drop the field `k` of a list of fields. -/
theorem exec_drop_popF {N K : ℕ} {t c : Fin 200} (h : t ≠ c) {w : St}
    (F : List (List Bool)) (k : ℕ) (hk : k < F.length) (rest : List Bool)
    (hc : (w c).length = F[k].length) (hs : w t = (F.drop k).flatten ++ rest) :
    exec N K (.drop t c) w = Function.update w t ((F.drop (k + 1)).flatten ++ rest) := by
  refine exec_drop_blk h hc ?_
  rw [hs, flatten_drop_cons hk, List.append_assoc]

/-! ### The parse -/

/-- The registers `parseC` writes. -/
def parseW : List (Fin 200) :=
  [rAttr, ra, rAB, rAd, rAHp, rAHk, rVB, rVHp, rVHk, rB2, rH2, rD2, rFe, rZ, rR0, rRin]

/-- The destination registers of the parse: their templates are in place. -/
def parseD : List (Fin 200) :=
  [rAttr, rAB, rAd, rAHp, rAHk, rVB, rVHp, rVHk, rB2, rH2, rD2, rFe, rZ, rR0, rRin]

/-- **The parse.** -/
theorem exec_parseC (σ : RawSec D) (w : St) (hT : TmplOK D w) (hra : w ra = (rawEnc D).enc σ)
    (hD : ∀ r ∈ parseD, w r = List.replicate (tm D r) false) :
    let w' := exec D.N D.K parseC w
    w' rAttr = encAttribute w8 σ.1 ∧ w' rAB = pwordsOf σ.2.1.aB ∧
      w' rAd = encRM D.N D.K σ.2.1.ad ∧ w' rAHp = ringWords (plainHL D σ.2.1.aH) ∧
      w' rAHk = ringWords (keyHL D σ.2.1.aH) ∧ w' rVB = pwordsOf σ.2.1.vB ∧
      w' rVHp = ringWords (plainHL D σ.2.1.vH) ∧ w' rVHk = ringWords (keyHL D σ.2.1.vH) ∧
      w' rB2 = pwordsOf σ.2.2.1 ∧ w' rH2 = ph2W σ ∧ w' rD2 = encRM D.N D.K σ.2.2.2.2.1 ∧
      w' rFe = pfl2W σ ∧ w' rZ = pzZW σ ∧ w' rR0 = pzR0W σ ∧ w' rRin = pzRinW σ ∧
      w' ra = pzAutW σ ∧ ∀ j, j ∉ parseW → w' j = w j := by
  intro w'
  have hF := prawEnc_fields σ
  set F := pfields σ with hFdef
  have hl : F.length = 18 := rfl
  have hD' : ∀ r ∈ parseD, (w r).length = tm D r := fun r hr => by rw [hD r hr, List.length_replicate]
  have L0 : F[0].length = 128 := length_encAttribute _ _
  have L1 : F[1].length = pnE (BCol (Wb D) D.K) * (D.N * D.K) := length_pwordsOf _
  have L2 : F[2].length = D.N * D.K := length_encRM _ _ _
  have L3 : F[3].length = D.K * pnE (Jh D) * (D.N * D.K) := by
    show (ringWords _).length = _; rw [length_ringWords]; exact congrArg (· * (D.N * D.K)) (length_plainHL _)
  have L4 : F[4].length = D.K * pnE (Jh D) * (D.N * D.K) := by
    show (ringWords _).length = _; rw [length_ringWords]; exact congrArg (· * (D.N * D.K)) (length_keyHL _)
  have L5 : F[5].length = pnE (BCol (Wb D) D.K) * (D.N * D.K) := length_pwordsOf _
  have L6 : F[6].length = D.N * D.K := length_encRM _ _ _
  have L7 : F[7].length = D.K * pnE (Jh D) * (D.N * D.K) := by
    show (ringWords _).length = _; rw [length_ringWords]; exact congrArg (· * (D.N * D.K)) (length_plainHL _)
  have L8 : F[8].length = D.K * pnE (Jh D) * (D.N * D.K) := by
    show (ringWords _).length = _; rw [length_ringWords]; exact congrArg (· * (D.N * D.K)) (length_keyHL _)
  have L9 : F[9].length = pnE (BCol (Wb D) D.K) * (D.N * D.K) := length_pwordsOf _
  have L10 : F[10].length = pnE (Jh D) * (pnE (Col D.K) * (D.N * D.K)) := by
    show (ph2W σ).length = _; exact FixedEnc.length _ _
  have L11 : F[11].length = D.N * D.K := length_encRM _ _ _
  have L12 : F[12].length = pnE (Fin D.b) * (pnE (Dig D.K) * (pnE (Col D.K) * (D.N * D.K))) := by
    show (pfl1W σ).length = _; exact FixedEnc.length _ _
  have L13 : F[13].length = pnE Pos * (pnE (Col D.K) * (D.N * D.K)) := by
    show (pfl2W σ).length = _; exact FixedEnc.length _ _
  have L14 : F[14].length =
      pnE Pos * (pnE (Dig D.K) * (pnE (Col D.K) * (D.N * D.K))) + pnE (Col D.K) * (D.N * D.K) := by
    show (pfl3W σ).length = _
    rw [pfl3W, List.length_append]
    exact congrArg₂ (· + ·) (FixedEnc.length _ _) (FixedEnc.length _ _)
  have L15 : F[15].length = pnE (Pos × Col D.K) * pnE (Wb D) := by
    show (pzZW σ).length = _; exact plength_zrBlocks _ _
  have L16 : F[16].length = pnE (Col D.K) * pnE (Wb D) := by
    show (pzR0W σ).length = _; exact plength_zrBlocks _ _
  have L17 : F[17].length = pnE (Pos × Dig D.K × Col D.K) * pnE (Wb D) := by
    show (pzRinW σ).length = _; exact plength_zrBlocks _ _
  have h0 : w ra = (F.drop 0).flatten ++ pzAutW σ := by rw [hra, hF]; rfl
  simp only [w', parseC, exec_ofList_cons, exec_ofList_nil]
  rw [exec_mv_popF (by decide) F 0 (by omega) (pzAutW σ) (by rw [hD' _ (by decide), L0]; rfl)
    (by rw [hT.len c128, L0]; rfl) h0]
  rw [exec_mv_popF (d := rAB) (s := ra) (c := cBC) (by decide) F 1 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rAB (by decide), L1])
    (by simp [Function.update_apply, hT.len cBC, L1]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rAd) (s := ra) (c := xCNK) (by decide) F 2 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rAd (by decide), L2])
    (by simp [Function.update_apply, hT.len xCNK, L2]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rAHp) (s := ra) (c := cJK) (by decide) F 3 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rAHp (by decide), L3])
    (by simp [Function.update_apply, hT.len cJK, L3]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rAHk) (s := ra) (c := cJK) (by decide) F 4 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rAHk (by decide), L4])
    (by simp [Function.update_apply, hT.len cJK, L4]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rVB) (s := ra) (c := cBC) (by decide) F 5 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rVB (by decide), L5])
    (by simp [Function.update_apply, hT.len cBC, L5]) (by simp [Function.update_apply])]
  rw [exec_drop_popF (t := ra) (c := xCNK) (by decide) F 6 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hT.len xCNK, L6]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rVHp) (s := ra) (c := cJK) (by decide) F 7 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rVHp (by decide), L7])
    (by simp [Function.update_apply, hT.len cJK, L7]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rVHk) (s := ra) (c := cJK) (by decide) F 8 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rVHk (by decide), L8])
    (by simp [Function.update_apply, hT.len cJK, L8]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rB2) (s := ra) (c := cBC) (by decide) F 9 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rB2 (by decide), L9])
    (by simp [Function.update_apply, hT.len cBC, L9]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rH2) (s := ra) (c := cH2) (by decide) F 10 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rH2 (by decide), L10])
    (by simp [Function.update_apply, hT.len cH2, L10]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rD2) (s := ra) (c := xCNK) (by decide) F 11 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rD2 (by decide), L11])
    (by simp [Function.update_apply, hT.len xCNK, L11]) (by simp [Function.update_apply])]
  rw [exec_drop_popF (t := ra) (c := cFl1) (by decide) F 12 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hT.len cFl1, L12]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rFe) (s := ra) (c := cPC) (by decide) F 13 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rFe (by decide), L13])
    (by simp [Function.update_apply, hT.len cPC, L13]) (by simp [Function.update_apply])]
  rw [exec_drop_popF (t := ra) (c := cFl3) (by decide) F 14 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hT.len cFl3, L14]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rZ) (s := ra) (c := cZ) (by decide) F 15 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rZ (by decide), L15])
    (by simp [Function.update_apply, hT.len cZ, L15]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rR0) (s := ra) (c := cZblk) (by decide) F 16 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rR0 (by decide), L16])
    (by simp [Function.update_apply, hT.len cZblk, L16]) (by simp [Function.update_apply])]
  rw [exec_mv_popF (d := rRin) (s := ra) (c := cRin) (by decide) F 17 (by omega) (pzAutW σ)
    (by simp [Function.update_apply, hD' rRin (by decide), L17])
    (by simp [Function.update_apply, hT.len cRin, L17]) (by simp [Function.update_apply])]
  refine ⟨by simp [Function.update_apply, hFdef, pfields], by simp [Function.update_apply, hFdef, pfields],
    by simp [Function.update_apply, hFdef, pfields], by simp [Function.update_apply, hFdef, pfields],
    by simp [Function.update_apply, hFdef, pfields], by simp [Function.update_apply, hFdef, pfields],
    by simp [Function.update_apply, hFdef, pfields], by simp [Function.update_apply, hFdef, pfields],
    by simp [Function.update_apply, hFdef, pfields], by simp [Function.update_apply, hFdef, pfields],
    by simp [Function.update_apply, hFdef, pfields], by simp [Function.update_apply, hFdef, pfields],
    by simp [Function.update_apply, hFdef, pfields], by simp [Function.update_apply, hFdef, pfields],
    by simp [Function.update_apply, hFdef, pfields], by simp [Function.update_apply, hFdef, pfields], ?_⟩
  intro j hj
  simp only [parseW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hj
  simp [Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

end AdvancedEncryption.ExpLUT.Prog.RedPubP
