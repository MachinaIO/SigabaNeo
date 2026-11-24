import PE.Impl.ExpLUT.AH.RedCompsR
import PE.Impl.ExpLUT.Prog.UnifCanon
import PE.Impl.ExpLUT.Prog.EncSamplers
import PE.Impl.DualUse.Prog.SetupTime

/-!
# The setup component of the reduction (package G2b)

`redSetupP D e : XProg 40` maps the handlers' state word `dwR D (enc D i)` (tape `0`) and the
attribute bits `encAttribute w8 x` (tape `1`) to the word `rawEnc D σ` of a raw secret
`σ ← rawSetup D (floodR D e) i x` (tape `0`, every other tape blank):

1. drop the marker bit of the state word (the rest is `instEnc D i`, `instEnc_eq`), prepend the
   `128` attribute bits;
2. append `nU D` canonical "uniform" ring words (`unifCanonP`, package F: `B̄⁽²⁾`, `H⁽²⁾`, `d₂`),
   the `nFl D` flooding ring elements (`N` coefficients of `e` fair bits each, as `floodP`), and the
   `nZ D` programming bits (fair coins).

* **`law_redSetupP`**: the law of the program is the law of the encoded raw secret
  (`rawSetupW_eq`: the words of `rawSetup` are three independent blocks);
* `redSetupX hR : XProg (R + 2)` for `38 ≤ R` (the lift), `law_redSetupX`, `wf_redSetupX`.

At the concrete parameters `χfl = floodR Dc eFl` (`rfl`), so this is the `setupP` field of
`RawComps Dc kb L impl χfl`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Cslib Cslib.Probability
open AdvancedEncryption.DualUse.Prog AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable (D : Dims)

/-! ### Counts -/

/-- The "uniform" ring elements of the raw secret: `B̄⁽²⁾` (with its gadget columns), `H⁽²⁾`, `d₂`. -/
abbrev nU : ℕ := (Enum.list (α := BCol (Wb D) D.K)).length +
  ((Enum.list (α := Jh D)).length * (Enum.list (α := Col D.K)).length + 1)

/-- The flooding ring elements. -/
abbrev nFl : ℕ := (Enum.list (α := Fin D.b × Dig D.K)).length * (Enum.list (α := Col D.K)).length +
  ((Enum.list (α := Pos)).length * (Enum.list (α := Col D.K)).length +
  ((Enum.list (α := Pos × Dig D.K)).length * (Enum.list (α := Col D.K)).length +
    (Enum.list (α := Col D.K)).length))

/-- The programming bits. -/
noncomputable abbrev nZ : ℕ := (Enum.list (α := PrI (setting D) Pos)).length * (Enum.list (α := Wb D)).length

/-! ### Words of the raw secret -/

theorem len_prodE {α β : Type} [Enum α] [Enum β] :
    (Enum.list (α := α × β)).length = (Enum.list (α := α)).length * (Enum.list (α := β)).length :=
  List.length_product _ _

theorem flatMap_product {α β : Type} (l1 : List α) (l2 : List β) (g : α × β → List Bool) :
    (l1.product l2).flatMap g = l1.flatMap fun a => l2.flatMap fun b => g (a, b) := by
  induction l1 with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, ← ih]
    simp [List.product, List.flatMap_map, Function.comp_def]

/-- Functions on a product, encoded curried. -/
theorem fun_prod_enc {α β γ : Type} [Enum α] [Enum β] {n : ℕ} (e : FixedEnc γ n) (f : α × β → γ) :
    (FixedEnc.fun (α := α × β) e).enc f =
      (FixedEnc.fun (α := α) (FixedEnc.fun (α := β) e)).enc fun a b => f (a, b) := by
  show e.encList ((Enum.list (α := α)).product (Enum.list (α := β)) |>.map f) =
    (FixedEnc.fun (α := β) e).encList ((Enum.list (α := α)).map fun a b => f (a, b))
  simp only [FixedEnc.encList, List.flatMap_map, flatMap_product]
  congr 1
  funext a
  show _ = e.encList _
  simp [FixedEnc.encList, List.flatMap_map, Function.comp_def]

/-- The instance part of the raw secret's word is the state word without its marker. -/
theorem instEnc_eq (i : CInst D) : (instEnc D).enc i = (dwR D (enc D i)).tail := by
  rw [dwR_enc, List.tail_cons]
  show (vecE D (Fin (circParamsD D).rows)).enc (toPair D i).1 ++
    (vecE D (Fin (circParamsD D).rows)).enc (toPair D i).2 = _
  congr 1 <;>
  · show (rEnc D).encList ((List.finRange _).map _) = _
    rw [wordsOf, FixedEnc.encList, List.flatMap_map, flatMap_finRange_concatN]
    refine concatN_congr fun r hr => ?_
    simp [hr, rEnc_enc]

/-- `μ.bind (a ↦ ν.map (e a ++ ·))` is the concatenation of independent words. -/
theorem bind_map_append (μ : PMF α) (e : α → List Bool) (ν : PMF (List Bool)) :
    (μ.bind fun a => ν.map (e a ++ ·)) = cat (μ.map e) ν := by
  rw [cat, PMF.bind_map]; rfl

variable {D}

/-- The law of one flooding element as `N` coefficient words. -/
theorem floodR_enc {e : ℕ} (he : e < D.K) :
    (floodR D e).map (rEnc D).enc = catPow (μF D.K e) D.N := by
  rw [floodR_eq, ringLawD_enc, PMF.map_comp]
  have h : (encM D.K ∘ flC D e) = gF D.K e := funext (encM_flood D he)
  rw [h, coefF_eq]

/-- The flooding errors' words. -/
theorem floodLaw_enc {e : ℕ} (he : e < D.K) :
    (floodLaw (setting D) Pos (floodR D e)).map (floodEnc D).enc =
      catPow ((floodR D e).map (rEnc D).enc) (nFl D) := by
  set μ := (floodR D e).map (rEnc D).enc
  have hF : ∀ (κ ι : Type) [Enum κ] [Fintype κ] [DecidableEq κ] [Enum ι] [Fintype ι]
      [DecidableEq ι], (iidFam (floodR D e) κ ι).map
        (FixedEnc.fun (α := κ) (vecE D ι)).enc =
        catPow μ ((Enum.list (α := κ)).length * (Enum.list (α := ι)).length) := by
    intro κ ι _ _ _ _ _ _
    exact lawMat (floodR D e) κ ι
  have h1 : (floodLaw (setting D) Pos (floodR D e)).map (floodEnc D).enc =
      cat ((iidFam (floodR D e) (Fin D.b × Dig D.K) (Col D.K)).map fun eaut =>
            (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
              (fun t d => eaut (t, d)))
          (cat ((iidFam (floodR D e) Pos (Col D.K)).map
            (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc)
          (cat ((iidFam (floodR D e) (Pos × Dig D.K) (Col D.K)).map fun edin =>
            (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
              (fun t d => edin (t, d)))
          ((iidLaw (floodR D e) (Col D.K)).map (vecE D (Col D.K)).enc))) := by
    show PMF.map (floodEnc D).enc ((iidFam (floodR D e) (Fin D.b × Dig D.K) (Col D.K)).bind
      fun eaut => (iidFam (floodR D e) Pos (Col D.K)).bind fun ein =>
        (iidFam (floodR D e) (Pos × Dig D.K) (Col D.K)).bind fun edin =>
          PMF.map (fun e0 => ((fun t d => eaut (t, d), ein, fun t d => edin (t, d), e0) :
            (Fin D.b → Dig D.K → Col D.K → Rg D) × (Pos → Col D.K → Rg D) ×
              (Pos → Dig D.K → Col D.K → Rg D) × (Col D.K → Rg D)))
            (iidLaw (floodR D e) (Col D.K))) = _
    simp only [cat, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
    rfl
  rw [h1]
  have e1 : (fun eaut : Fin D.b × Dig D.K → Col D.K → Rg D =>
      (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
        (fun t d => eaut (t, d))) =
      (FixedEnc.fun (α := Fin D.b × Dig D.K) (vecE D (Col D.K))).enc :=
    funext fun eaut => (fun_prod_enc _ eaut).symm
  have e3 : (fun edin : Pos × Dig D.K → Col D.K → Rg D =>
      (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
        (fun t d => edin (t, d))) =
      (FixedEnc.fun (α := Pos × Dig D.K) (vecE D (Col D.K))).enc :=
    funext fun edin => (fun_prod_enc _ edin).symm
  rw [e1, e3, hF, hF, hF, lawVec, ← catPow_add, ← catPow_add, ← catPow_add]

/-- The programming bits' words. -/
theorem zrLaw_enc : (zrLaw (setting D) (Wb D) Pos).map (zrEnc D).enc =
    BitString.uniformList (nZ D) := by
  unfold zrLaw zrEnc
  rw [fun_enc_pi, uniform_map_enc _ (by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, len_fin, mul_one]),
    catPow_uniformList, mul_one]

/-! ### The law of the raw secret's words -/

variable (D) in
/-- The words of the sampled part of the raw secret: `nU` "uniform" words, `nFl` flooding words,
`nZ` fair bits. -/
noncomputable def smpLaw (e : ℕ) : PMF (List Bool) :=
  cat (catPow (υW D.N D.K) (nU D))
    (cat (catPow ((floodR D e).map (rEnc D).enc) (nFl D)) (BitString.uniformList (nZ D)))

/-- Five independent draws, encoded as a prefix and five words. -/
theorem map_bind5 {A B C Dd Ee X : Type} (μ1 : PMF A) (μ2 : PMF B) (μ3 : PMF C) (μ4 : PMF Dd)
    (μ5 : PMF Ee) (f : A → B → C → Dd → Ee → X) (E : X → List Bool) (g : List Bool → List Bool)
    (e1 : A → List Bool) (e2 : B → List Bool) (e3 : C → List Bool) (e4 : Dd → List Bool)
    (e5 : Ee → List Bool)
    (hE : ∀ a b c d z, E (f a b c d z) = g (e1 a ++ (e2 b ++ (e3 c ++ (e4 d ++ e5 z))))) :
    (μ1.bind fun a => μ2.bind fun b => μ3.bind fun c => μ4.bind fun d =>
        μ5.map fun z => f a b c d z).map E =
      (cat (μ1.map e1) (cat (μ2.map e2) (cat (μ3.map e3) (cat (μ4.map e4) (μ5.map e5))))).map
        g := by
  simp only [cat, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, hE]

/-- **The words of `rawSetup`**: the attribute, the instance, then the sampled part. -/
theorem rawSetup_words {e : ℕ} (he : e < D.K) (i : CInst D) (x : Attribute w8) :
    (rawSetup D (floodR D e) i x).map (rawEnc D).enc =
      (smpLaw D e).map fun u => attrEnc.enc x ++ ((instEnc D).enc i ++ u) := by
  have h1 : (rawSetup D (floodR D e) i x).map (rawEnc D).enc =
      (cat ((iidLaw (unifW D) (BCol (Wb D) D.K)).map (vecE D (BCol (Wb D) D.K)).enc)
        (cat ((iidFam (unifW D) (Jh D) (Col D.K)).map
          (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc)
        (cat ((unifW D).map (rEnc D).enc)
        (cat ((floodLaw (setting D) Pos (floodR D e)).map (floodEnc D).enc)
          ((zrLaw (setting D) (Wb D) Pos).map (zrEnc D).enc))))).map
        fun u => attrEnc.enc x ++ ((instEnc D).enc i ++ u) :=
    map_bind5 (iidLaw (unifW D) (BCol (Wb D) D.K)) (iidFam (unifW D) (Jh D) (Col D.K)) (unifW D)
      (floodLaw (setting D) Pos (floodR D e)) (zrLaw (setting D) (Wb D) Pos)
      (fun B2 H2 d2 fl zr => ((x, i, B2, H2, d2, fl, zr) : RawSec D)) (rawEnc D).enc
      (fun u => attrEnc.enc x ++ ((instEnc D).enc i ++ u)) (vecE D (BCol (Wb D) D.K)).enc
      (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc (rEnc D).enc (floodEnc D).enc (zrEnc D).enc
      fun _ _ _ _ _ => rfl
  rw [h1, floodLaw_enc he, zrLaw_enc, ← hμVec, lawMat, υW_eq, smpLaw]
  congr 1
  rw [← cat_assoc, ← cat_assoc, ← catPow_add, ← catPow_succ_cat, Nat.add_assoc]

/-! ### The program -/

/-- The 7-tape samplers inside `40` tapes. -/
def e7 : Fin 7 ↪ Fin 40 := Fin.castLEEmb (by decide)

/-- The deterministic prefix: drop the marker, prepend the attribute bits. -/
def rsPre : SigabaNeo.Tape.Prog 40 :=
  .seq (.prim (.tail 0)) (SigabaNeo.Tape.Prog.prependN 128 1 0 2 3)

variable (D) in
/-- The samplers: "uniform" words, flooding words, programming bits. -/
noncomputable def rsSmp (e : ℕ) : XProg 40 :=
  seq (unifCanonP D.N D.K (nU D))
    (seq (frame e7 (repF (nFl D * D.N) (entF D.K e))) (frame e7 (coinsF (nZ D))))

variable (D) in
/-- **The setup component of the reduction** (`40` tapes). -/
noncomputable def redSetupP (e : ℕ) : XProg 40 := seq (prog rsPre) (rsSmp D e)

theorem ucpre_upd0 (s : Store 40) (w : List Bool) (h : UCPre s) : UCPre (Function.update s 0 w) :=
  fun j hj => by rw [Function.update_of_ne (fun h => by subst h; simp at hj)]; exact h j hj

theorem p5_of_ucpre (s : Store 40) (h : UCPre s) : P5 fun j => s (e7 j) :=
  ⟨⟨h 2 (by decide), h 3 (by decide), h 4 (by decide)⟩, h 5 (by decide), h 6 (by decide)⟩

theorem p3_of_ucpre (s : Store 40) (h : UCPre s) : P3 fun j => s (e7 j) :=
  (p5_of_ucpre s h).1

/-- **The samplers append the sampled part.** -/
theorem appendLaw_rsSmp {e : ℕ} (he : e < D.K) : AppendLaw (rsSmp D e) 0 UCPre (smpLaw D e) := by
  have h1 := appendLaw_unifCanonP D.K_pos (N := D.N) (nU D)
  have h2 : AppendLaw (frame e7 (repF (nFl D * D.N) (entF D.K e))) 0 UCPre
      (catPow ((floodR D e).map (rEnc D).enc) (nFl D)) :=
    (appendLaw_frame e7 (law_repF (law_entF e) (nFl D * D.N))).mono
      (fun s hs => p5_of_ucpre s hs) (by rw [floodR_enc he, catPow_mul])
  have h3 : AppendLaw (frame e7 (coinsF (nZ D))) 0 UCPre (BitString.uniformList (nZ D)) :=
    (appendLaw_frame e7 (law_coinsF (nZ D))).mono (fun s hs => p3_of_ucpre s hs) rfl
  exact h1.seq (h2.seq h3 ucpre_upd0) ucpre_upd0

theorem law_rsPre (w a : List Bool) (ha : a.length = 128) :
    (prog rsPre).law (io2 (R := 38) w a []) = PMF.pure (io2 (R := 38) (a ++ w.tail) [] []) := by
  rw [law_prog, rsPre, SigabaNeo.Tape.Prog.law_seq_pure (SigabaNeo.Tape.Prog.law_prim _ _),
    SigabaNeo.Tape.Prog.law_prependN 128 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ (by simp [Prim.apply, io2, ha]) (by simp [Prim.apply, io2])
      (by simp [Prim.apply, io2])]
  congr 1
  funext j
  simp only [Function.update_apply, Prim.apply, io2]
  split_ifs <;> simp_all <;> omega

theorem ucpre_io2 (u : List Bool) : UCPre (io2 (R := 38) u [] []) := fun j hj => by
  simp only [io2]; split_ifs <;> first | rfl | omega

/-- **The law of the setup component**: from the state word of an instance and the attribute
bits, the word of a raw secret `rawSetup D (floodR D e) i x`. -/
theorem law_redSetupP {e : ℕ} (he : e < D.K) (i : CInst D) (x : Attribute w8) :
    (redSetupP D e).law (io2 (R := 38) (dwR D (enc D i)) (encAttribute w8 x) []) =
      (rawSetup D (floodR D e) i x).map fun σ => io2 (R := 38) ((rawEnc D).enc σ) [] [] := by
  have hR : (rawSetup D (floodR D e) i x).map (fun σ => io2 (R := 38) ((rawEnc D).enc σ) [] []) =
      ((rawSetup D (floodR D e) i x).map (rawEnc D).enc).map fun w => io2 (R := 38) w [] [] :=
    (PMF.map_comp (rawEnc D).enc (rawSetup D (floodR D e) i x)
      (fun w => io2 (R := 38) w [] [])).symm
  rw [redSetupP, law_seq, law_rsPre _ _ (length_encAttribute w8 x), PMF.pure_bind,
    appendLaw_rsSmp he _ (ucpre_io2 _), hR, rawSetup_words he, PMF.map_comp]
  congr 1
  funext u
  simp only [Function.comp_apply, ← instEnc_eq]
  funext j
  simp only [Function.update_apply, io2]
  split_ifs <;> first | rfl | (subst_vars; simp_all) | omega

theorem wf_redSetupP (e : ℕ) : (redSetupP D e).WF := by
  unfold redSetupP rsSmp
  exact ⟨SigabaNeo.Tape.Prog.wf_of_wfB (by decide), wf_unifCanonP _ _ _,
    wf_repF (by unfold entF; exact ⟨wf_coinsF _, wf_zerosF _⟩) (preserves6_entF _ _) _, wf_coinsF _⟩

/-! ### The component at the handlers' width -/

variable (D) in
/-- **The setup component** on `R + 2` tapes (`38 ≤ R`). -/
noncomputable def redSetupX {R : ℕ} (hR : 38 ≤ R) (e : ℕ) : XProg (R + 2) :=
  liftP hR (redSetupP D e)

/-- **The law of the setup component** (the `law_setup` field of `RawComps` at
`χfl = floodR D e`). -/
theorem law_redSetupX {R : ℕ} (hR : 38 ≤ R) {e : ℕ} (he : e < D.K) (w : List Bool)
    (x : Attribute w8) (hw : IWR D w) :
    (redSetupX D hR e).law (io2 (R := R) w (encAttribute w8 x) []) =
      (setupR D (rawSetup D (floodR D e)) (instR D) w x).map
        fun σ => io2 (R := R) ((rawEnc D).enc σ) [] [] := by
  obtain ⟨i, rfl⟩ := hw
  rw [setupR, instR_dwR]
  exact law_liftP_map hR (law_redSetupP he i x)

theorem wf_redSetupX {R : ℕ} (hR : 38 ≤ R) (e : ℕ) : (redSetupX D hR e).WF :=
  wf_liftP hR (wf_redSetupP e)

end AdvancedEncryption.ExpLUT.Prog
