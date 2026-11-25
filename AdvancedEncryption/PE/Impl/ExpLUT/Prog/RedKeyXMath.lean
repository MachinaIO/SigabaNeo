import PE.Impl.ExpLUT.Prog.RedKeyXDrive
import PE.Impl.ExpLUT.Prog.RedKeyMath
import PE.Impl.ExpLUT.Prog.RedKeyTry

/-!
# `KGsim` on the VM (module 5b): the rows of `V_j` are the rows of the VM kernel

At the dimensions `D`, the rows of Lemma 11's matrices `V_j` (`vRounds`) are the rows `xRow` of
the generic kernel `xRowC` (`RedKeyXRow`), for

* the helper `xHs mpk t = H_{(t, 0)}` of round `t` (only its row `0` matters, `h1Of`), the
  automorphism count `g = gD D` (`σ_{idx j} = σ_g^j`), binary digits (`G̃⁻¹`);
* a row `ℓ` of `V.1` (`LCol`): the start `−R̂_ℓ`; the tag `0^{s} 1 0^{i}` and the unit row
  `e_{c'}` for `ℓ = η_{i,(s,0)}`'s row `c'` (the only rows the correction `J̃_η` touches,
  `jη_row`); the tag `11` (never met) otherwise;
* a row `r` of `V.2` (`Col τ`): the start `e_r` and the tag `11`.

Headlines: `vRounds_fst_row`, `vRounds_snd_row`, and **`simX_row`**: the row `q` of `X = simX …`
(in `ZIdx` order) is `xOut … (xParams q)`.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib Matrix

variable (D : Dims)

/-- The rows of `V.1`. -/
abbrev LColS := LCol (Wb D) (Jh D) (setting D).τ (setting D).E.W

theorem curW_inj {t j t' j' : ℕ} : curW t j = curW t' j' ↔ t = t' ∧ j = j' := by
  constructor
  · intro h
    induction t generalizing t' with
    | zero =>
      rcases t' with _ | t'
      · simp only [curW, List.replicate_zero, List.nil_append, List.cons.injEq, true_and] at h
        exact ⟨rfl, by simpa using congrArg List.length h⟩
      · simp [curW, List.replicate_succ] at h
    | succ t ih =>
      rcases t' with _ | t'
      · simp [curW, List.replicate_succ] at h
      · simp only [curW, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
        obtain ⟨h1, h2⟩ := ih h
        exact ⟨by omega, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The unit row `e_{c'}`. -/
def unitRow (c' : Fin 2 × Fin D.K) : Fin 2 × Fin D.K → Rg D := fun c => if c' = c then 1 else 0

/-- The tag of a row of `V.1`. -/
def xTag : LColS D → List Bool
  | .inl _ => ttW
  | .inr (i, k, _) => if k.2 = 0 then curW k.1 i else ttW

theorem xTag_inr0 (i : Fin (setting D).E.W) (s : Fin D.b) (c' : Col (setting D).τ) :
    xTag D (.inr (i, (s, 0), c')) = curW s i := rfl

theorem xTag_inr1 (i : Fin (setting D).E.W) (s : Fin D.b) (c' : Col (setting D).τ) :
    xTag D (.inr (i, (s, 1), c')) = ttW := rfl

/-- The correction row of a row of `V.1`. -/
def xE : LColS D → Fin 2 × Fin D.K → Rg D
  | .inl _ => 0
  | .inr (_, _, c') => unitRow D c'

theorem xE_inr (i : Fin (setting D).E.W) (k : Jh D) (c' : Col (setting D).τ) :
    xE D (.inr (i, k, c')) = unitRow D c' := rfl

/-- The helper of round `t`: `H_{(t, 0)}`. -/
noncomputable def xHs (mpk : MPKt D) (t : ℕ) : Fin 2 → Fin 2 × Fin D.K → Rg D :=
  if h : t < D.b then fun a c => mpk.H (⟨t, h⟩, 0) a c else 0

/-- The skipped helper of round `t`: `H_{(t, 1)}`. -/
noncomputable def xHi (mpk : MPKt D) (t : ℕ) : Fin 2 → Fin 2 × Fin D.K → Rg D :=
  if h : t < D.b then fun a c => mpk.H (⟨t, h⟩, 1) a c else 0

theorem setting_d (y : Rg D) (i : Fin D.K) : (setting D).D.d y i = binaryDigit y i := rfl

theorem aut_iterate_idx (j : ℕ) (x : Rg D) :
    (aut D.N (gD D))^[j] x = (setting D).E.σ ((setting D).idx j) x := by
  rw [aut_iterate D (odd_gD D)]
  show _ = autσ D.N (gD D ^ j) x
  rw [autσ_of_odd ((odd_gD D).pow)]

/-- **The product with `G̃⁻¹`, row by row**: the row `ℓ` of `V · G̃⁻¹(σ_{idx j}(H1 (fwd t)))` is
row `0` of `mask(V_ℓ) · G⁻¹(σ_g^j(H_{(t,0)}))`. -/
theorem mul_ginvTop_row (mpk : MPKt D) {ι : Type*} (V : Matrix ι (Col (setting D).τ) (Rg D))
    (ℓ : ι) {t : ℕ} (ht : t < D.b) {j : ℕ} (hj : j < (setting D).E.W) :
    (V * ginvTop ((setting D).E.σ ((setting D).idx (Fin.ofNat (setting D).E.W j : ℕ)) ∘
        h1Of mpk ((helperMap D).fwd ⟨t, ht⟩))) ℓ =
      ginvMulm (maskM (V ℓ)) (xY (gD D) (xHs D mpk t) j) 0 := by
  funext col
  have hj' : ((Fin.ofNat (setting D).E.W j : Fin _) : ℕ) = j := by
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt hj]
  simp only [Matrix.mul_apply, ginvTop, Matrix.of_apply, ginvMulm, digRow, maskM,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [hj', Function.comp_apply, h1Of, xY, xHs, ht, ↓reduceDIte]
  simp only [helperMap, ← aut_iterate_idx]
  congr 1
  all_goals (refine Finset.sum_congr rfl fun x _ => ?_)
  all_goals (try simp)
  all_goals (exact (zero_mul _).symm)

/-- **The correction row**: `(J̃_{η_{j,(t,0)}})_ℓ` is `e_ℓ` exactly when the tag of `ℓ` is
`0^t 1 0^j`. -/
theorem jη_row (ℓ : LColS D) {t : ℕ} (ht : t < D.b) {j : ℕ} (hj : j < (setting D).E.W) :
    (jη (S := setting D) (Wb := Wb D) (Fin.ofNat (setting D).E.W j) ((helperMap D).fwd ⟨t, ht⟩)) ℓ =
      if curW t j = xTag D ℓ then xE D ℓ else 0 := by
  have hj' : ((Fin.ofNat (setting D).E.W j : Fin _) : ℕ) = j := by
    simp only [Fin.val_ofNat]; exact Nat.mod_eq_of_lt hj
  funext col
  rcases ℓ with _ | ⟨i, ⟨s, d⟩, c'⟩
  · simp only [jη, Matrix.of_apply, xTag, xE, curW_ne_ttW, ↓reduceIte, Pi.zero_apply]
    rfl
  · by_cases hd : d = 0
    · subst hd
      have key : (i = Fin.ofNat (setting D).E.W j ∧ ((s, 0) : Jh D) = (⟨t, ht⟩, 0)) ↔
          curW t j = curW s i := by
        rw [curW_inj]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_⟩
          · have := congrArg (fun k : Jh D => (k.1 : ℕ)) h2; simp at this; omega
          · rw [h1, hj']
        · rintro ⟨h1, h2⟩
          refine ⟨Fin.ext (by rw [hj']; omega), ?_⟩
          ext <;> simp [h1]
      rw [xTag_inr0, xE_inr]
      simp only [jη, Matrix.of_apply, helperMap]
      by_cases hc : curW t j = curW s i
      · rw [if_pos hc]
        obtain ⟨h1, h2⟩ := key.mpr hc
        have hs : s = ⟨t, ht⟩ := (Prod.mk.inj h2).1
        subst h1 hs
        by_cases hcc : c' = col
        · exact (if_pos ⟨rfl, rfl, hcc⟩).trans (if_pos hcc).symm
        · exact (if_neg (fun h => hcc h.2.2)).trans (if_neg hcc).symm
      · rw [if_neg hc]
        exact if_neg (fun h => hc (key.mp ⟨h.1, h.2.1⟩))
    · have hd1 : d = 1 := by omega
      subst hd1
      rw [xTag_inr1, if_neg (curW_ne_ttW t j)]
      simp only [jη, Matrix.of_apply, helperMap]
      exact if_neg (fun h => by have := congrArg Prod.snd h.2.1; simp at this)

/-- **The rows of `V.1`.** -/
theorem vRounds_fst_row (mpk : MPKt D) (AF : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Rh : SimMat (Wb D) (Jh D) (setting D)) (ℓ : LColS D) :
    ∀ (t : ℕ) (ht : t ≤ (setting D).b) (j : ℕ), j < 2 ^ t →
      (vRounds (helperMap D) (h1Of mpk) AF Rh t ht j).1 ℓ =
        xRow (gD D) (xHs D mpk) (xTag D ℓ) (xE D ℓ) (fun c => -Rh ℓ c) t j := by
  intro t
  induction t with
  | zero => intro _ j _; funext c; simp [vRounds, xRow, vOne]
  | succ t ih =>
    intro ht j hj
    simp only [vRounds, xRow]
    split_ifs with h
    · exact ih _ j h
    · have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      have hW : j - 2 ^ t < (setting D).E.W := by
        have : 2 ^ (t + 1) ≤ 2 ^ D.b := Nat.pow_le_pow_right (by norm_num) ht
        rw [setting_W]; rw [pow_succ] at this; omega
      have htb : t < D.b := ht
      simp only [vStep, Matrix.sub_apply]
      rw [show (vRounds (helperMap D) (h1Of mpk) AF Rh t (Nat.le_of_succ_le ht) (j - 2 ^ t)).1 *
          ginvTop _ - jη _ _ = _ from rfl]
      funext col
      have hA := congrFun (mul_ginvTop_row D mpk
        (vRounds (helperMap D) (h1Of mpk) AF Rh t (Nat.le_of_succ_le ht) (j - 2 ^ t)).1 ℓ htb hW) col
      have hB := congrFun (jη_row D ℓ htb hW) col
      rw [Matrix.sub_apply, hA, hB, ih _ _ hj']
      unfold xStep
      split_ifs <;> simp <;> rfl

/-- **The rows of `V.2`.** -/
theorem vRounds_snd_row (mpk : MPKt D) (AF : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Rh : SimMat (Wb D) (Jh D) (setting D)) (r : Col (setting D).τ) :
    ∀ (t : ℕ) (ht : t ≤ (setting D).b) (j : ℕ), j < 2 ^ t →
      (vRounds (helperMap D) (h1Of mpk) AF Rh t ht j).2 r =
        xRow (gD D) (xHs D mpk) ttW 0 (unitRow D r) t j := by
  intro t
  induction t with
  | zero =>
    intro _ j _; funext c
    simp only [vRounds, xRow, vOne, unitRow, Matrix.one_apply]
    by_cases h : r = c
    · subst h; exact (if_pos rfl).trans (if_pos rfl).symm
    · exact (if_neg h).trans (if_neg h).symm
  | succ t ih =>
    intro ht j hj
    simp only [vRounds, xRow]
    split_ifs with h
    · exact ih _ j h
    · have hj' : j - 2 ^ t < 2 ^ t := by rw [pow_succ] at hj; omega
      have hW : j - 2 ^ t < (setting D).E.W := by
        have : 2 ^ (t + 1) ≤ 2 ^ D.b := Nat.pow_le_pow_right (by norm_num) ht
        rw [setting_W]; rw [pow_succ] at this; omega
      have htb : t < D.b := ht
      simp only [vStep]
      rw [mul_ginvTop_row D mpk _ r htb hW, ih _ _ hj']
      unfold xStep
      simp [curW_ne_ttW]

/-! ### The rows of `X` -/

/-- The tag of the row `q` of `X`. -/
def xTagP : PIdxS D → List Bool
  | .inl q => xTag D (.inl q)
  | .inr (.inl q) => xTag D (.inr q)
  | .inr (.inr _) => ttW

/-- The correction row of the row `q` of `X`. -/
def xEP : PIdxS D → Fin 2 × Fin D.K → Rg D
  | .inl q => xE D (.inl q)
  | .inr (.inl q) => xE D (.inr q)
  | .inr (.inr _) => 0

/-- The start row of the row `q` of `X`. -/
def xV0P (Rh : SimMat (Wb D) (Jh D) (setting D)) : PIdxS D → Fin 2 × Fin D.K → Rg D
  | .inl q => fun c => -Rh (.inl q) c
  | .inr (.inl q) => fun c => -Rh (.inr q) c
  | .inr (.inr r) => unitRow D r

theorem flatMap_finRange_val {α : Type} (n : ℕ) (f : ℕ → List α) :
    (List.finRange n).flatMap (fun i => f i.val) = (List.range n).flatMap f := by
  rw [List.flatMap, List.flatMap, map_finRange_val]

theorem take_vecL (v : Fin 2 × Fin D.K → Rg D) :
    (vecL v).take D.K = (List.finRange D.K).map fun i => v (0, i) := by
  rw [vecL_eq, List.take_left' (by simp)]

theorem enum_prod_map {α : Type} {n m : ℕ} (F : Fin n × Fin m → α) :
    (Enum.list (α := Fin n × Fin m)).map F =
      (List.finRange n).flatMap fun j => (List.finRange m).map fun c => F (j, c) := by
  show ((Enum.list (α := Fin n)).product (Enum.list (α := Fin m))).map F = _
  rw [product_map]; rfl

/-- **The row `q` of `X = simX …`** (in the order of `ZIdx`) is the output of the row kernel. -/
theorem simX_row (mpk : MPKt D) (AF : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Rh : SimMat (Wb D) (Jh D) (setting D)) (q : PIdxS D) :
    (Enum.list (α := ZIdxS D)).map (simX (helperMap D) (h1Of mpk) AF Rh q) =
      xOut (gD D) (xHs D mpk) (xTagP D q) (xEP D q) (xV0P D Rh q) D.b := by
  refine (enum_prod_map (fun ic => simX (helperMap D) (h1Of mpk) AF Rh q ic)).trans ?_
  unfold xOut
  simp only [take_vecL]
  rw [← flatMap_finRange_val]
  refine List.flatMap_congr fun j _ => List.map_congr_left fun c _ => ?_
  have hj : (j : ℕ) < 2 ^ D.b := j.2
  simp only [simX, Matrix.of_apply]
  rcases q with q | q | r
  · simp only [pOf, xTagP, xEP, xV0P]
    exact congrFun (vRounds_fst_row D mpk AF Rh _ D.b le_rfl j hj) (0, c)
  · simp only [pOf, xTagP, xEP, xV0P]
    exact congrFun (vRounds_fst_row D mpk AF Rh _ D.b le_rfl j hj) (0, c)
  · simp only [pOf, xTagP, xEP, xV0P]
    exact congrFun (vRounds_snd_row D mpk AF Rh _ D.b le_rfl j hj) (0, c)

/-- **The rows of `X`**: `rowsWord X` is the concatenation of the row kernel's outputs. -/
theorem rowsWord_simX (mpk : MPKt D) (AF : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Rh : SimMat (Wb D) (Jh D) (setting D)) :
    rowsWord (N := D.N) (K := D.K) (α := PIdxS D) (β := ZIdxS D)
        (simX (helperMap D) (h1Of mpk) AF Rh) =
      (Enum.list (α := PIdxS D)).flatMap fun q =>
        xOut (gD D) (xHs D mpk) (xTagP D q) (xEP D q) (xV0P D Rh q) D.b := by
  unfold rowsWord
  rw [List.flatMap]
  congr 1
  exact List.map_congr_left fun q _ => simX_row D mpk AF Rh q

end AdvancedEncryption.ExpLUT.Prog
