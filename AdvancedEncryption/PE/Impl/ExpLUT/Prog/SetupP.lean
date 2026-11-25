import PE.Impl.ExpLUT.Prog.SetupGad
import SigabaNeoStd.Machines.Prog.FrameOut

/-!
# `Setup` of the ExpLUT scheme as a tape program

`setupP X : XProg 128` realizes **exactly** the law `setupLawW D χT` (`law_setupP`), the scheme's
`Setup` with the public matrices drawn from `unifW D` and the trapdoor `T` from `χT` (sampled by the
explicit sampler `X : RingSampler D χT`), and outputs `encodeTuple [mpkEnc mpk, mskEnc msk]`:

1. **sampling**, in the order of `setupCoinsLawW`: `Ā` (`unifCanonP`, tape `82`), `T` (`repF` of
   `X.P`, tape `83`), `B⁽²⁾`, `H`, `a`, `A₀`, `A^in`, `A^aut`, `d` (`unifCanonP`, tapes `84 … 90`);
   scratch `1 … 39`;
2. **templates** (`natP`, tapes `40 … 48`: `K`, `N`, `N K`, `1`, `m̄`, `K`, `K · N K`, `K − 1`, the
   word of `1`);
3. **the gadget columns** (`detCore`): `P = Ā T` (`matMulMP`, tape `49`), `g − P` canonicalized
   (`gadRowP`, tape `50`), so `Ā ++ (g − Ā T)` is the word of `B⁽¹⁾ = trapRow Ā T`
   (`gadRowW_matMulMW`);
4. **the output** (tape `124`): the frame of `mpk = B⁽¹⁾ ++ B⁽²⁾ ++ H ++ a ++ A₀ ++ A^in ++ A^aut ++ d`,
   then of `msk = mpk ++ T` (`appC`, `frameApP`; helpers `121 … 123`).

The input word sits on tape `126` and is never read. `setupMP X`: the machine (`toMachineT`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix Cslib Cslib.Probability
open AdvancedEncryption.RingBTVW.Prog AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-- **An explicit sampler** of a law `χ` of ring elements: a 7-tape program appending the canonical
word of a sample to tape `0` (scratch `2 … 4`), leaving tape `6` alone, with a shape bound. -/
structure RingSampler (D : Dims) (χ : PMF (Rg D)) where
  /-- The program. -/
  P : XProg 7
  /-- Its law. -/
  law : AppendLaw P 0 P3 (χ.map (rEnc D).enc)
  /-- It is well formed. -/
  wf : P.WF
  /-- It leaves tape `6` alone. -/
  pres6 : P.Preserves 6
  /-- Its shape bound. -/
  B : Bnd
  /-- The shape bound holds. -/
  atb : ATBb P B

variable (D : Dims)

/-! ### Counts and frames -/

/-- The numbers of ring elements of the uniform fields. -/
abbrev nB2 : ℕ := (Enum.list (α := BCol (Wb D) D.K)).length
abbrev nH : ℕ := (Enum.list (α := Jh D)).length * ((Enum.list (α := Fin 2)).length *
  (Enum.list (α := Col D.K)).length)
abbrev nA : ℕ := (Enum.list (α := Pos)).length * (Enum.list (α := Col D.K)).length
abbrev nA0 : ℕ := (Enum.list (α := Fin 2)).length * (Enum.list (α := Col D.K)).length
abbrev nAin : ℕ := (Enum.list (α := Pos)).length * ((Enum.list (α := Dig D.K)).length *
  ((Enum.list (α := Fin 2)).length * (Enum.list (α := Col D.K)).length))
abbrev nAaut : ℕ := (Enum.list (α := Fin D.b)).length * ((Enum.list (α := Dig D.K)).length *
  ((Enum.list (α := Fin 2)).length * (Enum.list (α := Col D.K)).length))

/-- A canonical uniform sampler appending to tape `F` (scratch `1 … 39`). -/
def eUC (F : Fin 128) (hF : 40 ≤ F.val) : Fin 40 ↪ Fin 128 :=
  ⟨fun j => if j.val = 0 then F else ⟨j.val, by omega⟩, by
    intro i j h
    simp only at h
    split_ifs at h with hi hj hj
    · exact Fin.ext (hi.trans hj.symm)
    · exfalso; have := congrArg Fin.val h; simp at this; omega
    · exfalso; have := congrArg Fin.val h; simp at this; omega
    · exact Fin.ext (by simpa using congrArg Fin.val h)⟩

/-- The sampler of `T`, appending to tape `83` (its tape `1` is `127`). -/
def eT : Fin 7 ↪ Fin 128 := ⟨![83, 127, 2, 3, 4, 5, 6], by decide⟩

/-- `r := r ++ a` (copy `121`, stream `122`, counter `123`). -/
def appC (r a : Fin 128) : XProg 128 :=
  seq (prog (.prim (.copy 121 a))) (appendTapeP r 121 122 123)

theorem law_appC {r a : Fin 128} (hr1 : r ≠ 121) (hr2 : r ≠ 122) (hr3 : r ≠ 123) (s : Store 128)
    (h1 : s 121 = []) (h2 : s 122 = []) (h3 : s 123 = []) :
    (appC r a).law s = PMF.pure (Function.update s r (s r ++ s a)) := by
  rw [appC, law_seq, law_prim, PMF.pure_bind, law_appendTapeP hr1 hr2 hr3 (by decide) (by decide)
    (by decide) _ (by simp [Prim.apply, h2]) (by simp [Prim.apply, h3])]
  congr 1
  funext t
  simp only [Prim.apply, Function.update_apply]
  by_cases ht : t = 121
  · subst ht; simp [hr1.symm, h1]
  · by_cases h2 : t = r
    · subst h2; simp [ht]
    · simp [ht, h2]

/-! ### The deterministic core -/

/-- `matMulMP`: `49 := Ā T` (inputs `82`, `83`, templates `40 … 46`, scratch `1 … 39`, `51 … 60`). -/
def uM : Fin 59 → Fin 128 := ![49, 82, 83, 40, 41, 42, 43, 44, 45, 46, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
  11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
  35, 36, 37, 38, 39, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60]

/-- `gadRowP`: `50 := g − P` (templates `40`, `41`, `42`, `47`, the word of `1` on `48`). -/
def uG : Fin 42 → Fin 128 := ![50, 49, 40, 41, 42, 47, 48, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
  14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]

theorem uM_inj : Function.Injective uM := by decide
theorem uG_inj : Function.Injective uG := by decide

/-- The gadget columns. -/
def detCore : Prog 128 := Prog.seq (.prim (.copy 50 46)) (Prog.seq (Prog.map uM Prog.matMulMP)
  (Prog.map uG Prog.gadRowP))

theorem noGrow_detCore : detCore.NoGrow := rfl

/-- The templates: `40 … 48`. -/
def tmplP : XProg 128 :=
  seq (natP 40 125 D.K) <| seq (natP 41 125 D.N) <| seq (natP 42 125 (D.N * D.K)) <|
  seq (natP 43 125 1) <| seq (natP 44 125 D.mb) <| seq (natP 45 125 D.K) <|
  seq (natP 46 125 (D.K * (D.N * D.K))) <| seq (natP 47 125 (D.K - 1)) <|
  seq (natP 48 125 (D.N * D.K - 1)) (prog (.prim (.cons 48 true)))

/-- The output: the frames of `mpk` and `msk`. -/
def outP : XProg 128 :=
  seq (prog (.prim (.copy 0 82))) <| seq (appC 0 50) <| seq (appC 0 84) <| seq (appC 0 85) <|
  seq (appC 0 86) <| seq (appC 0 87) <| seq (appC 0 88) <| seq (appC 0 89) <| seq (appC 0 90) <|
  seq (frameApP 124 0 122 123) <| seq (appC 0 83) (frameApP 124 0 122 123)

variable {D} {χT : PMF (Rg D)}

/-- **`Setup` as a tape program.** -/
def setupP (X : RingSampler D χT) : XProg 128 :=
  seq (frame (eUC 82 (by decide)) (unifCanonP D.N D.K D.mb)) <|
  seq (frame eT (repF (D.mb * D.K) X.P)) <|
  seq (frame (eUC 84 (by decide)) (unifCanonP D.N D.K (nB2 D))) <|
  seq (frame (eUC 85 (by decide)) (unifCanonP D.N D.K (nH D))) <|
  seq (frame (eUC 86 (by decide)) (unifCanonP D.N D.K (nA D))) <|
  seq (frame (eUC 87 (by decide)) (unifCanonP D.N D.K (nA0 D))) <|
  seq (frame (eUC 88 (by decide)) (unifCanonP D.N D.K (nAin D))) <|
  seq (frame (eUC 89 (by decide)) (unifCanonP D.N D.K (nAaut D))) <|
  seq (frame (eUC 90 (by decide)) (unifCanonP D.N D.K 2)) <|
  seq (tmplP D) (seq (prog detCore) (outP))

end AdvancedEncryption.ExpLUT.Prog

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.XProg Matrix Cslib Cslib.Probability
open AdvancedEncryption.RingBTVW.Prog AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable {D : Dims}

/-! ### The deterministic tail -/

theorem run_matMulMP_map {k : ℕ} {u : Fin 59 → Fin k} (hu : Function.Injective u) {K N m n l : ℕ}
    (s : Store k) (hs : ∀ i : Fin 59, 10 ≤ i.val → s (u i) = []) (hK : (s (u 3)).length = K)
    (hN : (s (u 4)).length = N) (hNK : (s (u 5)).length = N * K) (hm : (s (u 6)).length = m)
    (hn : (s (u 7)).length = n) (hl : (s (u 8)).length = l)
    (hO : (s (u 9)).length = m * l * (N * K)) (hx : (s (u 1)).length = m * n * (N * K))
    (hy : (s (u 2)).length = n * l * (N * K)) :
    Prog.run (Prog.map u Prog.matMulMP) s =
      Function.update s (u 0) (matMulMW N K m n l (s (u 1)) (s (u 2))) :=
  Prog.run_map_eq_update hu _ s 0 _ (Prog.run_matMulMP (s ∘ u) hs hK hN hNK hm hn hl hO hx hy)

theorem run_gadRowP_map {k : ℕ} {u : Fin 42 → Fin k} (hu : Function.Injective u) {K N : ℕ}
    (hK : 0 < K) (s : Store k) (hs : ∀ i : Fin 42, 7 ≤ i.val → s (u i) = [])
    (hK' : (s (u 2)).length = K) (hN : (s (u 3)).length = N) (hNK : (s (u 4)).length = N * K)
    (hj : (s (u 5)).length = K - 1) (hone : (s (u 6)).length = N * K)
    (hO : (s (u 0)).length = K * (N * K)) :
    Prog.run (Prog.map u Prog.gadRowP) s =
      Function.update s (u 0) (gadRowW N K (s (u 6)) (s (u 1))) :=
  Prog.run_map_eq_update hu _ s 0 _ (Prog.run_gadRowP hK (s ∘ u) hs hK' hN hNK hj hone hO)

variable (D) in
/-- The store after the templates. -/
def tmplS (s : Store 128) : Store 128 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update s
      40 (List.replicate D.K false)) 41 (List.replicate D.N false))
      42 (List.replicate (D.N * D.K) false)) 43 (List.replicate 1 false))
      44 (List.replicate D.mb false)) 45 (List.replicate D.K false))
      46 (List.replicate (D.K * (D.N * D.K)) false)) 47 (List.replicate (D.K - 1) false))
      48 (true :: List.replicate (D.N * D.K - 1) false)

theorem law_tmplP (s : Store 128) (h125 : s 125 = []) :
    (tmplP D).law s = PMF.pure (tmplS D s) := by
  unfold tmplP
  repeat (rw [law_seq, law_natP (by decide) _ _ (by simp [h125]), PMF.pure_bind])
  rw [law_prim]
  congr 1
  simp only [Prim.apply, tmplS, Function.update_self, Function.update_idem]

/-- **The output**: the frames of `mpk` and of `mpk ++ T`. -/
theorem law_outP (S : Store 128) (h121 : S 121 = []) (h122 : S 122 = []) (h123 : S 123 = [])
    (h124 : S 124 = []) :
    (outP.law S).map (fun s => s 124) = PMF.pure (Turing.MultiTapeTM.frame
      (S 82 ++ S 50 ++ S 84 ++ S 85 ++ S 86 ++ S 87 ++ S 88 ++ S 89 ++ S 90) ++
        Turing.MultiTapeTM.frame
          (S 82 ++ S 50 ++ S 84 ++ S 85 ++ S 86 ++ S 87 ++ S 88 ++ S 89 ++ S 90 ++ S 83)) := by
  unfold outP
  rw [law_seq, law_prim, PMF.pure_bind]
  simp only [Prim.apply]
  repeat (rw [law_seq, law_appC (by decide) (by decide) (by decide) _ (by simp [h121])
    (by simp [h122]) (by simp [h123]), PMF.pure_bind])
  rw [law_seq, law_frameApP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [h122]) (by simp [h123]), PMF.pure_bind]
  rw [law_seq, law_appC (by decide) (by decide) (by decide) _ (by simp [h121])
    (by simp [h122]) (by simp [h123]), PMF.pure_bind]
  rw [law_frameApP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [h122]) (by simp [h123]), PMF.pure_map]
  congr 1
  simp [Function.update_apply, h124, List.append_assoc]

set_option maxHeartbeats 4000000 in
/-- **The gadget columns**, from the words of `Ā` and `T`. -/
theorem run_detCore (s : Store 128) (hb : ∀ j : Fin 128, j.val < 82 → s j = [])
    (Abar : Fin D.mb → Rg D) (T : Fin D.mb → Fin D.K → Rg D)
    (h82 : s 82 = (vecE D (Fin D.mb)).enc Abar) (h83 : s 83 = (matE D (Fin D.mb) (Fin D.K)).enc T) :
    Prog.run detCore (tmplS D s) = Function.update (Function.update (Function.update (tmplS D s) 50
      (List.replicate (D.K * (D.N * D.K)) false)) 49
        (matMulMW D.N D.K 1 D.mb D.K (s 82) (s 83))) 50
      ((vecE D (Fin D.K)).enc (fun c => (setting D).D.g c - ∑ w, Abar w * T w c)) := by
  have hNK : 1 ≤ D.N * D.K := Nat.one_le_iff_ne_zero.mpr (by have := D.K_pos; positivity)
  simp only [detCore, Prog.run_seq, Prog.run_copy]
  have e46 : tmplS D s 46 = List.replicate (D.K * (D.N * D.K)) false := by simp [tmplS]
  rw [e46]
  rw [run_matMulMP_map uM_inj (K := D.K) (N := D.N) (m := 1) (n := D.mb) (l := D.K) _ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [uM, tmplS, hb] at hi ⊢
  all_goals try (simp [uM, tmplS, hb]; done)
  · simp [uM, tmplS, h82, length_vecE_fin]
  · simp [uM, tmplS, h83, length_matE_fin]; ring
  rw [run_gadRowP_map uG_inj (K := D.K) (N := D.N) D.K_pos _ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [uG, uM, tmplS, hb] at hi ⊢
  all_goals try (simp [uG, uM, tmplS, hb]; done)
  · simp [uG, uM, tmplS]; omega
  have hA : Function.update (tmplS D s) 50 (List.replicate (D.K * (D.N * D.K)) false) (uM 1) =
      s 82 := by simp [uM, tmplS]
  have hB : Function.update (tmplS D s) 50 (List.replicate (D.K * (D.N * D.K)) false) (uM 2) =
      s 83 := by simp [uM, tmplS]
  rw [hA, hB]
  have hC : Function.update (Function.update (tmplS D s) 50
      (List.replicate (D.K * (D.N * D.K)) false)) (uM 0)
        (matMulMW D.N D.K 1 D.mb D.K (s 82) (s 83)) (uG 6) =
      true :: List.replicate (D.N * D.K - 1) false := by simp [uG, uM, tmplS]
  have hD : Function.update (Function.update (tmplS D s) 50
      (List.replicate (D.K * (D.N * D.K)) false)) (uM 0)
        (matMulMW D.N D.K 1 D.mb D.K (s 82) (s 83)) (uG 1) =
      matMulMW D.N D.K 1 D.mb D.K (s 82) (s 83) := by simp [uG, uM, tmplS]
  rw [hC, hD]
  conv_lhs => rw [h82, h83]
  rw [gadRowW_matMulMW, ← h82, ← h83]
  rfl

/-! ### Words of the keys -/

theorem fun_fin2_enc {β : Type} {n : ℕ} (e : FixedEnc β n) (f : Fin 2 → β) :
    (FixedEnc.fun (α := Fin 2) e).enc f = e.enc (f 0) ++ e.enc (f 1) := by
  show (([0, 1] : List (Fin 2)).map f).flatMap e.enc = _
  simp

theorem fun_sum_enc {α β γ : Type} [Enum α] [Enum β] {n : ℕ} (e : FixedEnc γ n) (f : α ⊕ β → γ) :
    (FixedEnc.fun (α := α ⊕ β) e).enc f =
      (FixedEnc.fun (α := α) e).enc (f ∘ Sum.inl) ++ (FixedEnc.fun (α := β) e).enc (f ∘ Sum.inr) := by
  show (((Enum.list (α := α)).map Sum.inl ++ (Enum.list (α := β)).map Sum.inr).map f).flatMap e.enc =
    ((Enum.list (α := α)).map (f ∘ Sum.inl)).flatMap e.enc ++
      ((Enum.list (α := β)).map (f ∘ Sum.inr)).flatMap e.enc
  rw [List.map_append, List.flatMap_append, List.map_map, List.map_map]

theorem B_word (A : Fin D.mb → Rg D) (G : Fin D.K → Rg D) (B2 : Fin D.mb ⊕ Fin D.K → Rg D) :
    (matE D (Fin 2) (Fin D.mb ⊕ Fin D.K)).enc
      (![Sum.elim A G, B2] : Fin 2 → Fin D.mb ⊕ Fin D.K → Rg D) =
      (vecE D (Fin D.mb)).enc A ++ (vecE D (Fin D.K)).enc G ++ (vecE D (Fin D.mb ⊕ Fin D.K)).enc B2 := by
  rw [matE, fun_fin2_enc]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [fun_sum_enc]
  rfl

/-- **The word of the public key** of `Setup` on coins `r`. -/
theorem mpk_word (r : SetupCoins (setting D) (Wb D) (Jh D) Pos) :
    (mpkEnc D).enc (setup r).1 = (vecE D (Fin D.mb)).enc r.Abar ++
      (vecE D (Fin D.K)).enc (fun c => (setting D).D.g c - ∑ w, r.Abar w * r.T w c) ++
      (vecE D (BCol (Wb D) D.K)).enc r.B2 ++
      (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc r.H ++
      (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.a ++ (matE D (Fin 2) (Col D.K)).enc r.A0 ++
      (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc r.Ain ++
      (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
        (matE D (Fin 2) (Col D.K)))).enc r.Aaut ++ (vecE D (Fin 2)).enc r.d := by
  show (matE D (Fin 2) (Fin D.mb ⊕ Fin D.K)).enc (![Sum.elim r.Abar
    (fun c => (setting D).D.g c - ∑ w, r.Abar w * r.T w c), r.B2] :
      Fin 2 → Fin D.mb ⊕ Fin D.K → Rg D) ++ _ = _
  have hb := B_word r.Abar (fun c : Fin D.K => (setting D).D.g c - ∑ w, r.Abar w * r.T w c) r.B2
  refine (congrArg (· ++ _) hb).trans ?_
  simp only [List.append_assoc]
  rfl

/-! ### The law -/

/-- A framed sampler followed by a program: the law binds the sampled value. -/
theorem law_seq_app {m : ℕ} (e : Fin m ↪ Fin 128) {p : XProg m} {r : Fin m}
    {P : Store m → Prop} {μ : PMF (List Bool)} (hp : AppendLaw p r P μ) {α : Type} (ν : PMF α)
    (g : α → List Bool) (hμ : μ = ν.map g) (q : XProg 128) (s : Store 128)
    (hs : P fun j => s (e j)) :
    (seq (frame e p) q).law s = ν.bind fun v => q.law (Function.update s (e r) (s (e r) ++ g v)) := by
  rw [law_seq, appendLaw_frame e hp s hs, hμ, PMF.map_comp, PMF.bind_map]
  rfl

theorem hμVec (α : Type) [Enum α] [Fintype α] [DecidableEq α] :
    catPow (υW D.N D.K) (Enum.list (α := α)).length = (iidLaw (unifW D) α).map (vecE D α).enc := by
  rw [lawVec, υW_eq]

@[simp] theorem eUC_zero (F : Fin 128) (hF : 40 ≤ F.val) : eUC F hF 0 = F := rfl
@[simp] theorem eT_zero : eT 0 = 83 := rfl

theorem ucpre_of (F : Fin 128) (hF : 40 ≤ F.val) (s : Store 128)
    (h : ∀ t : Fin 128, 1 ≤ t.val → t.val < 40 → s t = []) : UCPre (fun j => s (eUC F hF j)) := by
  intro j hj
  have e : eUC F hF j = ⟨j.val, by omega⟩ := by
    have : j ≠ 0 := fun h => by subst h; simp at hj
    simp [eUC, this]
  show s (eUC F hF j) = []
  rw [e]
  exact h _ hj j.isLt

theorem p5_of (s : Store 128) (h : ∀ t : Fin 128, 1 ≤ t.val → t.val < 40 → s t = []) :
    P5 (fun j => s (eT j)) :=
  ⟨⟨h 2 (by decide) (by decide), h 3 (by decide) (by decide), h 4 (by decide) (by decide)⟩,
    h 5 (by decide) (by decide), h 6 (by decide) (by decide)⟩

theorem upd_low (s : Store 128) (F : Fin 128) (hF : 40 ≤ F.val) (w : List Bool) (t : Fin 128)
    (ht : t.val < 40) : Function.update s F w t = s t :=
  Function.update_of_ne (fun h => by subst h; omega) _ _

theorem input_low (x : List Bool) (t : Fin 128) (ht : t.val < 40) : inputStore 126 x t = [] := by
  rw [inputStore, Function.update_of_ne (fun h => by subst h; simp at ht)]

/-- The blank tapes `1 … 39` of the input store after the fields are written. -/
macro "blank_tac" : tactic => `(tactic| (
  first
  | (apply ucpre_of; intro t h1 h2
     try simp only [eUC_zero, eT_zero]
     repeat rw [upd_low _ _ (by decide) _ _ h2]
     exact input_low _ _ h2)
  | (apply p5_of; intro t h1 h2
     try simp only [eUC_zero, eT_zero]
     repeat rw [upd_low _ _ (by decide) _ _ h2]
     exact input_low _ _ h2)))

theorem encodeTuple_two (a b : List Bool) :
    encodeTuple [a, b] = Turing.MultiTapeTM.frame a ++ Turing.MultiTapeTM.frame b := by
  show Turing.MultiTapeTM.frame a ++ (Turing.MultiTapeTM.frame b ++ []) = _
  rw [List.append_nil]

set_option maxHeartbeats 4000000 in
/-- **The deterministic part**: templates, gadget columns, output. -/
theorem law_detAll (r : SetupCoins (setting D) (Wb D) (Jh D) Pos) (S : Store 128)
    (h82 : S 82 = (vecE D (Fin D.mb)).enc r.Abar) (h83 : S 83 = (matE D (Fin D.mb) (Fin D.K)).enc r.T)
    (h84 : S 84 = (vecE D (BCol (Wb D) D.K)).enc r.B2)
    (h85 : S 85 = (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc r.H)
    (h86 : S 86 = (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.a)
    (h87 : S 87 = (matE D (Fin 2) (Col D.K)).enc r.A0)
    (h88 : S 88 = (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc r.Ain)
    (h89 : S 89 = (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
      (matE D (Fin 2) (Col D.K)))).enc r.Aaut)
    (h90 : S 90 = (vecE D (Fin 2)).enc r.d)
    (hb : ∀ t : Fin 128, t.val < 82 → S t = []) (h121 : S 121 = []) (h122 : S 122 = [])
    (h123 : S 123 = []) (h124 : S 124 = []) (h125 : S 125 = []) :
    ((seq (tmplP D) (seq (prog detCore) outP)).law S).map (fun s => s 124) =
      PMF.pure (encodeTuple [(mpkEnc D).enc (setup r).1, (mskEnc D).enc (setup r).2]) := by
  rw [law_seq, law_tmplP S h125, PMF.pure_bind, law_seq, law_prog,
    Prog.law_eq_run _ noGrow_detCore, PMF.pure_bind,
    run_detCore S hb r.Abar r.T h82 h83, law_outP _ (by simp [tmplS, h121]) (by simp [tmplS, h122])
      (by simp [tmplS, h123]) (by simp [tmplS, h124])]
  congr 1
  rw [encodeTuple_two]
  have e2 : (mskEnc D).enc (setup r).2 = (mpkEnc D).enc (setup r).1 ++
      (matE D (Fin D.mb) (Fin D.K)).enc r.T := rfl
  rw [e2, mpk_word]
  simp only [Function.update_apply, tmplS]
  simp [h82, h83, h84, h85, h86, h87, h88, h89, h90, List.append_assoc]


set_option maxHeartbeats 8000000 in
/-- **The law of `Setup`**: on any input word, the output tape `124` has the law of the encoded
`(mpk, msk) ← setupLawW D χT`. -/
theorem law_setupP (X : RingSampler D χT) (x : List Bool) :
    ((setupP X).law (inputStore 126 x)).map (fun s => s 124) =
      (setupLawW D χT).map fun v => encodeTuple [(mpkEnc D).enc v.1, (mskEnc D).enc v.2] := by
  rw [setupLawW, PMF.map_comp, setupCoinsLawW]
  simp only [PMF.map_bind]
  unfold setupP
  rw [law_seq_app (eUC 82 (by decide)) (appendLaw_unifCanonP D.K_pos D.mb)
    (iidLaw (unifW D) (Wb D)) (vecE D (Wb D)).enc (by rw [← hμVec, len_fin]) _ _ (by blank_tac),
    PMF.map_bind]
  refine congrArg _ (funext fun Abar => ?_)
  rw [law_seq_app eT (law_repF X.law (D.mb * D.K)) (iidFam χT (Wb D) (Fin D.K))
    (matE D (Wb D) (Fin D.K)).enc (by rw [lawMat, len_fin, len_fin]) _ _ (by blank_tac),
    PMF.map_bind]
  refine congrArg _ (funext fun T => ?_)
  rw [law_seq_app (eUC 84 (by decide)) (appendLaw_unifCanonP D.K_pos (nB2 D))
    (iidLaw (unifW D) (BCol (Wb D) D.K)) (vecE D (BCol (Wb D) D.K)).enc (by rw [← hμVec]) _ _
    (by blank_tac), PMF.map_bind]
  refine congrArg _ (funext fun B2 => ?_)
  rw [law_seq_app (eUC 85 (by decide)) (appendLaw_unifCanonP D.K_pos (nH D))
    (Cslib.Probability.PMF.pi fun _ : Jh D => iidFam (unifW D) (Fin 2) (Col D.K))
    (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc (by rw [lawFunMat, υW_eq]) _ _
    (by blank_tac), PMF.map_bind]
  refine congrArg _ (funext fun H => ?_)
  rw [law_seq_app (eUC 86 (by decide)) (appendLaw_unifCanonP D.K_pos (nA D))
    (iidFam (unifW D) Pos (Col D.K)) (matE D Pos (Col D.K)).enc (by rw [lawMat, υW_eq]) _ _
    (by blank_tac), PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [law_seq_app (eUC 87 (by decide)) (appendLaw_unifCanonP D.K_pos (nA0 D))
    (iidFam (unifW D) (Fin 2) (Col D.K)) (matE D (Fin 2) (Col D.K)).enc (by rw [lawMat, υW_eq])
    _ _ (by blank_tac), PMF.map_bind]
  refine congrArg _ (funext fun A0 => ?_)
  rw [law_seq_app (eUC 88 (by decide)) (appendLaw_unifCanonP D.K_pos (nAin D))
    (Cslib.Probability.PMF.pi fun _ : Pos => Cslib.Probability.PMF.pi fun _ : Dig D.K =>
      iidFam (unifW D) (Fin 2) (Col D.K))
    (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
    (by rw [lawFunFunMat, υW_eq]) _ _ (by blank_tac), PMF.map_bind]
  refine congrArg _ (funext fun Ain => ?_)
  rw [law_seq_app (eUC 89 (by decide)) (appendLaw_unifCanonP D.K_pos (nAaut D))
    (Cslib.Probability.PMF.pi fun _ : Fin D.b => Cslib.Probability.PMF.pi fun _ : Dig D.K =>
      iidFam (unifW D) (Fin 2) (Col D.K))
    (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc
    (by rw [lawFunFunMat, υW_eq]) _ _ (by blank_tac), PMF.map_bind]
  refine congrArg _ (funext fun Aaut => ?_)
  rw [law_seq_app (eUC 90 (by decide)) (appendLaw_unifCanonP D.K_pos 2)
    (iidLaw (unifW D) (Fin 2)) (vecE D (Fin 2)).enc (by rw [← hμVec, len_fin]) _ _
    (by blank_tac), PMF.map_bind, PMF.map_comp, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun d => ?_)
  simp only [Function.comp_apply]
  refine law_detAll ⟨Abar, T, B2, H, a, A0, Ain, Aaut, d⟩ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals first
    | (intro t ht
       have n82 : t ≠ 82 := fun h => by subst h; simp at ht
       have n83 : t ≠ 83 := fun h => by subst h; simp at ht
       have n84 : t ≠ 84 := fun h => by subst h; simp at ht
       have n85 : t ≠ 85 := fun h => by subst h; simp at ht
       have n86 : t ≠ 86 := fun h => by subst h; simp at ht
       have n87 : t ≠ 87 := fun h => by subst h; simp at ht
       have n88 : t ≠ 88 := fun h => by subst h; simp at ht
       have n89 : t ≠ 89 := fun h => by subst h; simp at ht
       have n90 : t ≠ 90 := fun h => by subst h; simp at ht
       have n126 : t ≠ 126 := fun h => by subst h; simp at ht
       simp [Function.update_apply, inputStore, n82, n83, n84, n85, n86, n87, n88, n89, n90, n126])
    | (simp [Function.update_apply, inputStore]; done)

/-! ### Well-formedness and the machine -/

theorem wf_appC (r a : Fin 128) (hr : r ≠ 123) : (appC r a).WF :=
  ⟨trivial, wf_appendTapeP hr (by decide)⟩

theorem wf_tmplP : (tmplP D).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, trivial⟩

theorem wf_detCore : detCore.WF :=
  ⟨trivial, Prog.WF.map uM_inj Prog.wf_matMulMP, Prog.WF.map uG_inj Prog.wf_gadRowP⟩

theorem wf_outP : outP.WF :=
  ⟨trivial, wf_appC _ _ (by decide), wf_appC _ _ (by decide), wf_appC _ _ (by decide),
    wf_appC _ _ (by decide), wf_appC _ _ (by decide), wf_appC _ _ (by decide),
    wf_appC _ _ (by decide), wf_appC _ _ (by decide),
    wf_frameApP (by decide) (by decide), wf_appC _ _ (by decide), wf_frameApP (by decide) (by decide)⟩

theorem wf_setupP (X : RingSampler D χT) : (setupP X).WF :=
  ⟨wf_unifCanonP _ _ _, wf_repF X.wf X.pres6 _, wf_unifCanonP _ _ _, wf_unifCanonP _ _ _,
    wf_unifCanonP _ _ _, wf_unifCanonP _ _ _, wf_unifCanonP _ _ _, wf_unifCanonP _ _ _,
    wf_unifCanonP _ _ _, wf_tmplP, wf_detCore, wf_outP⟩

/-- The length of the input word of `Setup`. -/
def nInS : ℕ := (encodeTuple [pwW]).length

/-- **The machine of `Setup`**: the compiled `setupP`, input on tape `126`, output tape `124`. -/
noncomputable def setupMP (X : RingSampler D χT) : Machine := (setupP X).toMachineT 126 124 nInS

/-- **The machine of `Setup` realizes its law** (`SetupSpec`). -/
theorem setupSpec_setupMP (X : RingSampler D χT) : SetupSpec D χT (setupMP X) := by
  unfold SetupSpec setupMP
  rw [XProg.run_toMachineT _ (wf_setupP X) 126 124 nInS _ le_rfl, law_setupP]

end AdvancedEncryption.ExpLUT.Prog
