import PE.Impl.ExpLUT.Prog.EncPhaseTime
/-! # Length-preserving bounds for the repeated encryption phases -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.Prog
open AdvancedEncryption.ExpLUT.Params

/-- A phase keeps every tape below the common encryption bound and has the stated clock. -/
def PhaseBound {k : ℕ} (p : SigabaNeo.Tape.Prog k) (T : ℕ) : Prop :=
  ∀ ℓ : Fin k → ℕ, (∀ i, ℓ i ≤ 2 ^ 99) →
    timeBoundT p ℓ ≤ T ∧ ∀ i, lenBoundT p ℓ i ≤ 2 ^ 99

theorem PhaseBound.seq {k : ℕ} {p q : SigabaNeo.Tape.Prog k} {T U : ℕ}
    (hp : PhaseBound p T) (hq : PhaseBound q U) : PhaseBound (.seq p q) (T + U) := by
  intro ℓ hℓ
  exact ⟨Nat.add_le_add (hp ℓ hℓ).1 (hq _ (hp ℓ hℓ).2).1, (hq _ (hp ℓ hℓ).2).2⟩

theorem PhaseBound.mono {k : ℕ} {p : SigabaNeo.Tape.Prog k} {T U : ℕ}
    (hp : PhaseBound p T) (h : T ≤ U) : PhaseBound p U :=
  fun ℓ hℓ => ⟨(hp ℓ hℓ).1.trans h, (hp ℓ hℓ).2⟩

theorem PhaseBound.noGrow {k : ℕ} {p : SigabaNeo.Tape.Prog k} {T : ℕ}
    (hp : p.NoGrow) (ht : ∀ ℓ, (∀ i, ℓ i ≤ 2 ^ 99) → timeBoundT p ℓ ≤ T) :
    PhaseBound p T := fun ℓ hℓ => ⟨ht ℓ hℓ, Sym.lenBoundT_le_const p hp hℓ⟩

set_option exponentiation.threshold 2000 in
theorem phase_putW {k : ℕ} (i : Fin k) (w : List Bool) (hw : w.length ≤ 2 ^ 99) :
    PhaseBound (putW i w) (2 ^ 202) := by
  intro ℓ hℓ
  constructor
  · have h := timeBoundT_le_pcount (putW i w) (loopFree_putW _ _) ℓ hℓ
    rw [pcount_putW] at h
    refine h.trans (le_trans (b := (2 ^ 99 + 1) * (2 * (2 ^ 99 + (2 ^ 99 + 1)) + 5))
      (Nat.mul_le_mul (Nat.add_le_add_right hw 1) ?_) ?_)
    · omega
    · norm_num
  · rw [lenBoundT_putW]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hw
    · simpa [Function.update_of_ne hj] using hℓ j

set_option exponentiation.threshold 2000 in
theorem phase_prim {k : ℕ} (p : Prim k) (hp : p.noGrowB = true) :
    PhaseBound (.prim p) (2 ^ 102) := by
  apply PhaseBound.noGrow (p := .prim p) hp
  intro ℓ hℓ
  have h := time_noGrow_le (.prim p) hp hℓ
  exact h.trans (by norm_num [tbC, tbD])

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem phase_helperRound {t : ℕ} (ht : t ≤ 22) :
    PhaseBound (helperRoundP Dc t) (2 ^ 610) := by
  have he : 2 ^ t ≤ (2 : ℕ) ^ 99 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : 2 ^ Dc.b - 2 ^ t ≤ (2 : ℕ) ^ 99 :=
    (Nat.sub_le _ _).trans (by change 2 ^ 22 ≤ (2 : ℕ) ^ 99; norm_num)
  have h1 := phase_putW (5 : Fin 69) (List.replicate (2 ^ t) false) (by simpa using he)
  have h2 := phase_putW (6 : Fin 69) (List.replicate (2 ^ Dc.b - 2 ^ t) false) (by simpa using hd)
  have h3 : PhaseBound hBlkP (2 ^ 609) := PhaseBound.noGrow noGrow_hBlkP (fun _ => time_helper_uniform)
  exact (h1.seq (h2.seq (h3.seq ((phase_prim (.clear 5) rfl).seq
    (phase_prim (.clear 6) rfl))))).mono (by norm_num)

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem phase_autRound {t : ℕ} (ht : t ≤ 22) :
    PhaseBound (autRoundP Dc t) (2 ^ 808) := by
  have he : 2 ^ t ≤ (2 : ℕ) ^ 99 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : 2 ^ Dc.b - 2 ^ t ≤ (2 : ℕ) ^ 99 :=
    (Nat.sub_le _ _).trans (by change 2 ^ 22 ≤ (2 : ℕ) ^ 99; norm_num)
  have h1 := phase_putW (7 : Fin 85) (List.replicate (2 ^ t) false) (by simpa using he)
  have h2 := phase_putW (8 : Fin 85) (List.replicate (2 ^ Dc.b - 2 ^ t) false) (by simpa using hd)
  have h3 : PhaseBound autBlkP (2 ^ 807) := PhaseBound.noGrow noGrow_autBlkP (fun _ => time_aut_uniform)
  exact (h1.seq (h2.seq (h3.seq ((phase_prim (.clear 7) rfl).seq
    (phase_prim (.clear 8) rfl))))).mono (by norm_num)

set_option exponentiation.threshold 2000 in
theorem phase_helperPairs (j n : ℕ) (hn : j + n ≤ 22) :
    PhaseBound (helperPairsP Dc j n) (n * 2 ^ 610 + 2 ^ 102) := by
  induction n generalizing j with
  | zero => simpa [helperPairsP] using phase_prim (.copy (0 : Fin 69) 0) rfl
  | succ n ih =>
    exact ((phase_helperRound (by omega)).seq (ih (j + 1) (by omega))).mono (by omega)

set_option exponentiation.threshold 2000 in
theorem phase_autBlocks (j n : ℕ) (hn : j + n ≤ 22) :
    PhaseBound (autBlocksP Dc j n) (n * 2 ^ 808 + 2 ^ 102) := by
  induction n generalizing j with
  | zero => simpa [autBlocksP] using phase_prim (.copy (0 : Fin 85) 0) rfl
  | succ n ih =>
    exact ((phase_autRound (by omega)).seq (ih (j + 1) (by omega))).mono (by omega)

/-- A bound stable under the actual placement of the phase in the full tape bank. -/
def MappedPhaseBound {n : ℕ} (p : SigabaNeo.Tape.Prog n) (T : ℕ) : Prop :=
  ∀ (k : ℕ) (u : Fin n → Fin k), PhaseBound (map u p) T

theorem MappedPhaseBound.seq {n : ℕ} {p q : SigabaNeo.Tape.Prog n} {T U : ℕ}
    (hp : MappedPhaseBound p T) (hq : MappedPhaseBound q U) :
    MappedPhaseBound (.seq p q) (T + U) := fun k u => (hp k u).seq (hq k u)

theorem MappedPhaseBound.mono {n : ℕ} {p : SigabaNeo.Tape.Prog n} {T U : ℕ}
    (hp : MappedPhaseBound p T) (h : T ≤ U) : MappedPhaseBound p U := fun k u => (hp k u).mono h

theorem mapped_poly {n : ℕ} (p : SigabaNeo.Tape.Prog n) (hp : p.NoGrow) {T : ℕ}
    (ht : p.tbC * (2 ^ 99 + 1) ^ p.tbD ≤ T) : MappedPhaseBound p T := by
  intro k u
  apply PhaseBound.noGrow (hp.map u)
  intro ℓ hℓ
  have h := time_noGrow_le (map u p) (hp.map u) hℓ
  rw [tbC_map, tbD_map] at h
  exact h.trans ht

theorem map_putW_enc {n k : ℕ} (u : Fin n → Fin k) (i : Fin n) (w : List Bool) :
    map u (putW i w) = putW (u i) w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change SigabaNeo.Tape.Prog.seq (map u (putW i w)) (.prim (.cons (u i) b)) = _
    rw [ih]; rfl

theorem mapped_putW {n : ℕ} (i : Fin n) (w : List Bool) (hw : w.length ≤ 2 ^ 99) :
    MappedPhaseBound (putW i w) (2 ^ 202) := by
  intro k u
  rw [map_putW_enc]
  exact phase_putW _ _ hw

set_option exponentiation.threshold 2000 in
theorem mapped_prim {n : ℕ} (p : Prim n) (hp : p.noGrowB = true) :
    MappedPhaseBound (.prim p) (2 ^ 102) :=
  mapped_poly (.prim p) hp (by norm_num [tbC, tbD])

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem mapped_helperRound {t : ℕ} (ht : t ≤ 22) :
    MappedPhaseBound (helperRoundP Dc t) (2 ^ 610) := by
  have he : 2 ^ t ≤ (2 : ℕ) ^ 99 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : 2 ^ Dc.b - 2 ^ t ≤ (2 : ℕ) ^ 99 :=
    (Nat.sub_le _ _).trans (by change 2 ^ 22 ≤ (2 : ℕ) ^ 99; norm_num)
  have h1 := mapped_putW (5 : Fin 69) (List.replicate (2 ^ t) false) (by simpa using he)
  have h2 := mapped_putW (6 : Fin 69) (List.replicate (2 ^ Dc.b - 2 ^ t) false) (by simpa using hd)
  have hc : hBlkP.tbC = 9791 := congrArg Prod.fst degrees_helper
  have hd' : hBlkP.tbD = 6 := congrArg Prod.snd degrees_helper
  have h3 : MappedPhaseBound hBlkP (2 ^ 609) := mapped_poly _ noGrow_hBlkP (by rw [hc, hd']; norm_num)
  exact (h1.seq (h2.seq (h3.seq ((mapped_prim (.clear 5) rfl).seq
    (mapped_prim (.clear 6) rfl))))).mono (by norm_num)

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 2000 in
theorem mapped_autRound {t : ℕ} (ht : t ≤ 22) :
    MappedPhaseBound (autRoundP Dc t) (2 ^ 808) := by
  have he : 2 ^ t ≤ (2 : ℕ) ^ 99 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : 2 ^ Dc.b - 2 ^ t ≤ (2 : ℕ) ^ 99 :=
    (Nat.sub_le _ _).trans (by change 2 ^ 22 ≤ (2 : ℕ) ^ 99; norm_num)
  have h1 := mapped_putW (7 : Fin 85) (List.replicate (2 ^ t) false) (by simpa using he)
  have h2 := mapped_putW (8 : Fin 85) (List.replicate (2 ^ Dc.b - 2 ^ t) false) (by simpa using hd)
  have hc : autBlkP.tbC = 12766 := congrArg Prod.fst degrees_aut
  have hd' : autBlkP.tbD = 8 := congrArg Prod.snd degrees_aut
  have h3 : MappedPhaseBound autBlkP (2 ^ 807) := mapped_poly _ noGrow_autBlkP (by rw [hc, hd']; norm_num)
  exact (h1.seq (h2.seq (h3.seq ((mapped_prim (.clear 7) rfl).seq
    (mapped_prim (.clear 8) rfl))))).mono (by norm_num)

set_option exponentiation.threshold 2000 in
theorem mapped_helperPairs (j n : ℕ) (hn : j + n ≤ 22) :
    MappedPhaseBound (helperPairsP Dc j n) (n * 2 ^ 610 + 2 ^ 102) := by
  induction n generalizing j with
  | zero => simpa [helperPairsP] using mapped_prim (.copy (0 : Fin 69) 0) rfl
  | succ n ih =>
    exact ((mapped_helperRound (by omega)).seq (ih (j + 1) (by omega))).mono (by omega)

set_option exponentiation.threshold 2000 in
theorem mapped_autBlocks (j n : ℕ) (hn : j + n ≤ 22) :
    MappedPhaseBound (autBlocksP Dc j n) (n * 2 ^ 808 + 2 ^ 102) := by
  induction n generalizing j with
  | zero => simpa [autBlocksP] using mapped_prim (.copy (0 : Fin 85) 0) rfl
  | succ n ih =>
    exact ((mapped_autRound (by omega)).seq (ih (j + 1) (by omega))).mono (by omega)

end AdvancedEncryption.ExpLUT.Prog.EncW
