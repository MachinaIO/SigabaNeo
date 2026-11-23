import PE.Impl.DualUse.Prog.SetupTime3
import PE.Impl.DualUse.Prog.ChalI

/-!
# Lifting the small components to the handlers' width

The handlers (`PE.Impl.Game.HandlersP`) take components `XProg (R + 2)`, two inputs on the tapes
`0`, `1`, `R` blank scratch tapes, the output on tape `0`. The reductions use **`R = 80`**
(`XProg 82`). The setup programs (`setup3P`, `setup5P`, `setupIP`), the χ sampler `chiP` and the
challenge component of the ideal side `chalIP` are `XProg 7` (`R = 5`); they are lifted by a
frame on the first tapes (`liftP`, `Fin.castLE`).

* `law_liftP`, `law_liftP_map`, `law_liftP_pure`: the law of a lifted program on `ioS a b d`;
* `timeBoundT_liftP`, `lenBoundT_liftP_le`: its per-tape time and length bounds on `io2 a b 0`
  are those of the program;
* `appendLaw_frame`: append laws are carried by frames (`appendLaw_chiL`);
* the lifted components with their laws, well-formedness and time bounds: `setup3L`, `setup5L`,
  `setupIL`, `chiL`, `chalIL`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

/-! ### The lift -/

/-- The first `R + 2` tapes among `R' + 2`. -/
def liftE {R R' : ℕ} (h : R ≤ R') : Fin (R + 2) ↪ Fin (R' + 2) := Fin.castLEEmb (by omega)

@[simp] theorem liftE_val {R R' : ℕ} (h : R ≤ R') (j : Fin (R + 2)) : (liftE h j).val = j.val := rfl

/-- **The lift of a program** to more scratch tapes. -/
def liftP {R R' : ℕ} (h : R ≤ R') (p : XProg (R + 2)) : XProg (R' + 2) := frame (liftE h) p

theorem ioS_val_congr {R : ℕ} {α : Type} (a b d : α) {j j' : Fin (R + 2)} (h : j.val = j'.val) :
    ioS (R := R) a b d j = ioS (R := R) a b d j' := by
  unfold ioS; rw [h]

theorem ioS_lift_apply {R R' : ℕ} {α : Type} (h : R ≤ R') (a b d : α) (j : Fin (R + 2)) :
    ioS (R := R') a b d (liftE h j) = ioS (R := R) a b d j := by
  unfold ioS; rw [liftE_val]

theorem ioS_comp_liftE {R R' : ℕ} {α : Type} (h : R ≤ R') (a b d : α) :
    (fun j => ioS (R := R') a b d (liftE h j)) = ioS (R := R) a b d := by
  funext j; exact ioS_lift_apply h a b d j

theorem io2_comp_liftE {R R' : ℕ} {α : Type} (h : R ≤ R') (a b d : α) :
    (fun j => io2 (R := R') a b d (liftE h j)) = io2 (R := R) a b d := by
  funext j; exact ioS_lift_apply h a b d j

/-- Embedding an `ioS` store in an `ioS` store with the same default. -/
theorem embedF_ioS {R R' : ℕ} {α : Type} (h : R ≤ R') (a b a' b' d : α) :
    embedF (liftE h) (ioS (R := R') a b d) (ioS (R := R) a' b' d) = ioS (R := R') a' b' d := by
  funext l
  rcases embedF_cases (liftE h) (ioS (R := R') a b d) (ioS (R := R) a' b' d) l with
    ⟨hl, e⟩ | ⟨i, rfl, e⟩
  · rw [e]
    have h0 : l.val ≠ 0 := by
      intro h0
      have : l = liftE h ⟨0, by omega⟩ := Fin.ext (by simp [h0])
      rw [this, partialInv_self] at hl
      exact Option.some_ne_none _ hl
    have h1 : l.val ≠ 1 := by
      intro h1
      have : l = liftE h ⟨1, by omega⟩ := Fin.ext (by simp [h1])
      rw [this, partialInv_self] at hl
      exact Option.some_ne_none _ hl
    simp [ioS, h0, h1]
  · rw [e]; exact (ioS_lift_apply h a' b' d i).symm

theorem embedF_io2 {R R' : ℕ} {α : Type} (h : R ≤ R') (a b a' b' d : α) :
    embedF (liftE h) (io2 (R := R') a b d) (io2 (R := R) a' b' d) = io2 (R := R') a' b' d :=
  embedF_ioS h a b a' b' d

theorem ioS_eq_io2 {R : ℕ} {α : Type} (a b d : α) : ioS (R := R) a b d = io2 a b d := rfl

/-- **The law of a lifted program.** -/
theorem law_liftP {R R' : ℕ} (h : R ≤ R') (p : XProg (R + 2)) (a b d : List Bool) :
    (liftP h p).law (ioS (R := R') a b d) =
      (p.law (ioS (R := R) a b d)).map (embedF (liftE h) (ioS (R := R') a b d)) := by
  rw [liftP, law_frame, ioS_comp_liftE]

/-- The lift of a law with the output alone on tape `0`. -/
theorem law_liftP_map {R R' : ℕ} (h : R ≤ R') {p : XProg (R + 2)} {a b : List Bool} {β : Type}
    {μ : PMF β} {f : β → List Bool}
    (hp : p.law (ioS (R := R) a b []) = μ.map fun x => ioS (R := R) (f x) [] []) :
    (liftP h p).law (ioS (R := R') a b []) = μ.map fun x => ioS (R := R') (f x) [] [] := by
  rw [law_liftP, hp, PMF.map_comp]
  congr 1
  funext x
  exact embedF_ioS h a b (f x) [] []

theorem law_liftP_pure {R R' : ℕ} (h : R ≤ R') {p : XProg (R + 2)} {a b w : List Bool}
    (hp : p.law (ioS (R := R) a b []) = PMF.pure (ioS (R := R) w [] [])) :
    (liftP h p).law (ioS (R := R') a b []) = PMF.pure (ioS (R := R') w [] []) := by
  rw [law_liftP, hp, PMF.pure_map, embedF_ioS]

theorem wf_liftP {R R' : ℕ} (h : R ≤ R') {p : XProg (R + 2)} (hp : p.WF) : (liftP h p).WF := hp

/-- **The time bound of a lifted program** is that of the program. -/
theorem timeBoundT_liftP {R R' : ℕ} (h : R ≤ R') (p : XProg (R + 2)) (a b : ℕ) :
    timeBoundT (liftP h p) (io2 (R := R') a b 0) = timeBoundT p (io2 (R := R) a b 0) := by
  rw [liftP, timeBoundT_frame, io2_comp_liftE]

/-- **The length bound of a lifted program**: an output bound `io2 L 0 0` carries over. -/
theorem lenBoundT_liftP_le {R R' : ℕ} (h : R ≤ R') (p : XProg (R + 2)) {a b L : ℕ}
    (hp : lenBoundT p (io2 (R := R) a b 0) ≤ io2 L 0 0) :
    lenBoundT (liftP h p) (io2 (R := R') a b 0) ≤ io2 L 0 0 := by
  show embedF (liftE h) _ (lenBoundT p fun j => io2 (R := R') a b 0 (liftE h j)) ≤ _
  rw [io2_comp_liftE, ← embedF_io2 h a b L 0 0]
  exact embedF_mono _ le_rfl hp

/-! ### Append laws through frames -/

theorem appendLaw_frame {m k : ℕ} (e : Fin m ↪ Fin k) {p : XProg m} {r : Fin m}
    {P : Store m → Prop} {μ : PMF (List Bool)} (hp : AppendLaw p r P μ) :
    AppendLaw (frame e p) (e r) (fun s => P fun j => s (e j)) μ := by
  intro s hs
  rw [law_frame, hp _ hs, PMF.map_comp]
  congr 1
  funext u
  simp only [Function.comp_apply]
  funext l
  rcases embedF_cases e s (Function.update (fun j => s (e j)) r (s (e r) ++ u)) l with
    ⟨hl, h⟩ | ⟨i, rfl, h⟩
  · rw [h, Function.update_of_ne]
    rintro rfl
    rw [partialInv_self] at hl
    exact Option.some_ne_none _ hl
  · rw [h]
    by_cases hi : i = r
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne (e.injective.ne hi)]

/-! ### The lifted components (`R = 80`) -/

theorem five_le_eighty : (5 : ℕ) ≤ 80 := by norm_num

/-- Lift an `XProg 7` to `XProg 82`. -/
abbrev lift82 (p : XProg 7) : XProg 82 := liftP five_le_eighty p

theorem time_lift82 (p : XProg 7) (a b : ℕ) :
    timeBoundT (lift82 p) (io2 (R := 80) a b 0) = timeBoundT p (io2 (R := 5) a b 0) :=
  timeBoundT_liftP _ p a b

/-- **The χ sampler, lifted.** -/
def chiL : XProg 82 := lift82 chiP

/-- The blank scratch tapes `2, 3, 4` (those of `P3`). -/
def P3L (s : Store 82) : Prop := s 2 = [] ∧ s 3 = [] ∧ s 4 = []

theorem appendLaw_chiL : AppendLaw chiL 0 P3L (μχ Params.confP) :=
  (appendLaw_frame (liftE five_le_eighty) law_chiP).mono (fun _ h => h) rfl

theorem wf_chiL : chiL.WF := wf_chiP

theorem atb_chiL : ATB chiL 0 bChi.S₀ bChi.a bChi.s bChi.T := by
  intro x S hS
  obtain ⟨h1, h2⟩ := atbb_chiP x S hS
  have hshp : (fun j => shp (0 : Fin 82) x S (liftE five_le_eighty j)) = shp (0 : Fin 7) x S := by
    funext j; simp only [shp]
    congr 1
    exact propext ⟨fun h => Fin.ext (by simpa using congrArg Fin.val h),
      fun h => Fin.ext (by rw [h]; rfl)⟩
  refine ⟨?_, ?_⟩
  · show timeBoundT chiP (fun j => shp (0 : Fin 82) x S (liftE five_le_eighty j)) ≤ _
    rw [hshp]; exact h1
  · show embedF (liftE five_le_eighty) _ (lenBoundT chiP fun j => shp (0 : Fin 82) x S
      (liftE five_le_eighty j)) ≤ _
    rw [hshp]
    intro l
    rcases embedF_cases (liftE five_le_eighty) (shp (0 : Fin 82) x S)
      (lenBoundT chiP (shp (0 : Fin 7) x S)) l with ⟨hl, e⟩ | ⟨i, rfl, e⟩
    · rw [e]
      have h0 : l ≠ 0 := by
        rintro rfl
        rw [show (0 : Fin 82) = liftE five_le_eighty 0 from rfl, partialInv_self] at hl
        exact Option.some_ne_none _ hl
      simp only [shp, if_neg h0]; omega
    · rw [e]
      refine (h2 i).trans ?_
      simp only [shp]
      by_cases hi : i = 0
      · subst hi
        rw [if_pos rfl, if_pos (show liftE five_le_eighty (0 : Fin 7) = (0 : Fin 82) from rfl)]
      · rw [if_neg hi, if_neg (fun h => hi (Fin.ext (by
          have := congrArg Fin.val h; rw [liftE_val] at this; exact this)))]

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-! #### The setups -/

/-- **The setup of hybrid 3, lifted.** -/
def setup3L (Pχ : XProg 7) : XProg 82 := lift82 (setup3P hk c Pχ)

theorem law_setup3L {Pχ : XProg 7} (hχ : AppendLaw Pχ 0 P3 (μχ c)) [NeZero c.d] (hN : 0 < N)
    (hK : 0 < K) (ab : Inst3T N K k) (x : PUniv.Attr) :
    (setup3L hk c Pχ).law (ioS (R := 80) ((inst3Enc (N := N) (K := K) (k := k)).enc ab)
      (encAttr x) []) =
      (setup3 hk c x).map fun σ =>
        ioS (R := 80) (((inst3Enc (N := N) (K := K) (k := k)).prod (sec3Enc hk c)).enc (ab, σ))
          [] [] :=
  law_liftP_map _ (law_setup3P hk c Pχ hχ hN hK ab x)

theorem wf_setup3L {Pχ : XProg 7} (hwf : Pχ.WF) (h6 : Pχ.Preserves 6) : (setup3L hk c Pχ).WF :=
  wf_setup3P hk c Pχ hwf h6

theorem time_setup3L (Bχ : Bnd) {Pχ : XProg 7} (hχ : ATBb Pχ Bχ) (h6 : Pχ.Preserves 6) (a b : ℕ) :
    timeBoundT (setup3L hk c Pχ) (io2 (R := 80) a b 0) ≤ time3 hk c Bχ a b := by
  rw [setup3L, time_lift82]; exact time_setup3P hk c Bχ hχ h6 a b

/-- **The setup of hybrid 5, lifted.** -/
def setup5L : XProg 82 := lift82 (setup5P hk c)

theorem law_setup5L [NeZero c.d] (hN : 0 < N) (hK : 0 < K)
    (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) (x : PUniv.Attr) :
    (setup5L hk c).law (ioS (R := 80) ((inst5Enc (N := N) (K := K) (k := k) c.d).enc i)
      (encAttr x) []) =
      (setup5 hk c x).map fun σ =>
        ioS (R := 80) (((inst5Enc (N := N) (K := K) (k := k) c.d).prod (sec5Enc hk c)).enc (i, σ))
          [] [] :=
  law_liftP_map _ (law_setup5P hk c hN hK i x)

theorem wf_setup5L : (setup5L hk c).WF := wf_setup5P hk c

theorem time_setup5L (a b : ℕ) :
    timeBoundT (setup5L hk c) (io2 (R := 80) a b 0) ≤ time5 hk c a b := by
  rw [setup5L, time_lift82]; exact time_setup5P hk c a b

/-- **The setup of the ideal side, lifted.** -/
def setupIL (Pχ : XProg 7) : XProg 82 := lift82 (setupIP hk c Pχ)

theorem law_setupIL {Pχ : XProg 7} (hχ : AppendLaw Pχ 0 P3 (μχ c)) [NeZero c.d] (hN : 0 < N)
    (hK : 0 < K) (ab : Inst3T N K k) (x : PUniv.Attr) :
    (setupIL hk c Pχ).law (ioS (R := 80) ((inst3Enc (N := N) (K := K) (k := k)).enc ab)
      (encAttr x) []) =
      (setupI hk c x).map fun σ =>
        ioS (R := 80) (((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc (ab, σ))
          [] [] :=
  law_liftP_map _ (law_setupIP hk c Pχ hχ hN hK ab x)

theorem wf_setupIL {Pχ : XProg 7} (hwf : Pχ.WF) (h6 : Pχ.Preserves 6) : (setupIL hk c Pχ).WF :=
  wf_setupIP hk c Pχ hwf h6

theorem time_setupIL (Bχ : Bnd) {Pχ : XProg 7} (hχ : ATBb Pχ Bχ) (h6 : Pχ.Preserves 6) (a b : ℕ) :
    timeBoundT (setupIL hk c Pχ) (io2 (R := 80) a b 0) ≤ timeI hk c Bχ a b := by
  rw [setupIL, time_lift82]; exact time_setupIP hk c Bχ hχ h6 a b

/-! #### The challenge of the ideal side -/

/-- **The challenge component of the ideal side, lifted.** -/
def chalIL : XProg 82 := lift82 (chalIP hk c)

theorem law_chalIL (hN : 0 < N) (hK : 1 ≤ K) (ab : Inst3T N K k) (σ : SecI hk c) (μ : Bool) :
    (chalIL hk c).law (ioS (R := 80)
      (((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc (ab, σ)) (encMsg μ) []) =
      PMF.pure (ioS (R := 80) ((ctEnc hk c).enc (shiftCT hk c μ (viewI hk c ab σ).2)) [] []) :=
  law_liftP_pure _ (law_chalIP hk c hN hK ab σ μ)

theorem wf_chalIL : (chalIL hk c).WF := wf_chalIP hk c

end AdvancedEncryption.DualUse.Prog
