import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenBase

/-!
# Generating gate tapes: loops over lists of wires

`zipB G` runs a gadget `G` over two lists of wires with a carried wire. Its register code
`zipBody` pops one wire of each list, runs the gadget's code, pushes its output and carries its
carry; `iter_zipBody` is the loop of `|as|` rounds. The ripple adder, the bitwise mux, `andL` and
`notL` are instances.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-- A zip of two lists of wires with a carried wire, by a gadget `G p a b c = (p', out, c')`. -/
def zipB (G : SLP ι → Wire ι → Wire ι → Wire ι → SLP ι × Wire ι × Wire ι) :
    SLP ι → List (Wire ι) → List (Wire ι) → Wire ι → SLP ι × List (Wire ι) × Wire ι
  | p, a :: as, b :: bs, c =>
    let r := G p a b c
    let r' := zipB G r.1 as bs r.2.2
    (r'.1, r.2.1 :: r'.2.1, r'.2.2)
  | p, _, _, c => (p, [], c)

/-- The loop body: pop `rA` from `lA`, `rB` from `lB`, run `g`, push `rO` to `lR`, `rC := rC'`. -/
def zipBody (g : Code) (rA rB rO rC rC' : SR) (lA lB lR : LR) : Code :=
  .seq (.lpop rA lA) (.seq (.lpop rB lB) (.seq g (.seq (.lpush lR rO) (.mov rC rC'))))

variable (E ix) in
/-- The specification of a gadget's code. -/
def GSpec (g : Code) (G : SLP ι → Wire ι → Wire ι → Wire ι → SLP ι × Wire ι × Wire ι)
    (S : List SR) (rA rB rO rC rC' rs : SR) (vs : ℕ) : Prop :=
  ∀ (P : SLP ι) (σ : St) (a b c : Wire ι), Consts E σ → σ.sc rs = vs → σ.sc rA = pos E ix a →
    σ.sc rB = pos E ix b → σ.sc rC = pos E ix c → E.n + (exec E g (mk E ix P σ)).t ≤ E.M →
    ∃ sc', exec E g (mk E ix P σ) = mk E ix (G P a b c).1 { σ with sc := sc' } ∧
      sc' rO = pos E ix (G P a b c).2.1 ∧ sc' rC' = pos E ix (G P a b c).2.2 ∧ Fr S σ.sc sc'

/-- Empty `lA`, `lB`; set `lR`. -/
def ls3 (f : LR → List ℕ) (lA lB lR : LR) (L : List ℕ) : LR → List ℕ :=
  Function.update (Function.update (Function.update f lA []) lB []) lR L

theorem exec_mk_lpop (P : SLP ι) (σ : St) (d : SR) (l : LR) :
    exec E (.lpop d l) (mk E ix P σ) = mk E ix P (exec E (.lpop d l) σ) := rfl
theorem exec_mk_lpush (P : SLP ι) (σ : St) (l : LR) (a : SR) :
    exec E (.lpush l a) (mk E ix P σ) = mk E ix P (exec E (.lpush l a) σ) := rfl
theorem exec_mk_mov (P : SLP ι) (σ : St) (d a : SR) :
    exec E (.mov d a) (mk E ix P σ) = mk E ix P (exec E (.mov d a) σ) := rfl

theorem inv_mk {P : SLP ι} {σ : St} : Inv E (mk E ix P σ) ↔ Inv E σ := Iff.rfl
theorem scOK_mk {P : SLP ι} {σ : St} : ScOK E (mk E ix P σ) ↔ ScOK E σ := Iff.rfl

/-- **The zip loop.** -/
theorem iter_zipBody (hnM : E.n ≤ E.M) (hWM : E.W ≤ E.M) {g : Code}
    {G : SLP ι → Wire ι → Wire ι → Wire ι → SLP ι × Wire ι × Wire ι} {S : List SR}
    {rA rB rO rC rC' rs : SR} {vs : ℕ} {lA lB lR : LR} (hG : GSpec E ix g G S rA rB rO rC rC' rs vs)
    (hAB : lA ≠ lB) (hAR : lA ≠ lR) (hBR : lB ≠ lR) (hrAB : rA ≠ rB) (hrAC : rA ≠ rC)
    (hrBC : rB ≠ rC) (h0 : rONE ∉ rA :: rB :: rC :: S) (h1 : rZ ∉ rA :: rB :: rC :: S)
    (hs : rs ∉ rA :: rB :: rC :: S) :
    ∀ (as bs : List (Wire ι)) (P : SLP ι) (σ : St) (c : Wire ι) (L0 : List ℕ),
      as.length = bs.length → Consts E σ → σ.sc rs = vs → Inv E σ → ScOK E σ →
      σ.ls lA = as.map (pos E ix) → σ.ls lB = bs.map (pos E ix) → σ.ls lR = L0 →
      σ.sc rC = pos E ix c → L0.length + as.length ≤ E.C →
      E.n + ((exec E (zipBody g rA rB rO rC rC' lA lB lR))^[as.length] (mk E ix P σ)).t ≤ E.M →
      ∃ sc', (exec E (zipBody g rA rB rO rC rC' lA lB lR))^[as.length] (mk E ix P σ) =
        mk E ix (zipB G P as bs c).1
          { σ with sc := sc', ls := ls3 σ.ls lA lB lR (L0 ++ (zipB G P as bs c).2.1.map (pos E ix)) } ∧
        sc' rC = pos E ix (zipB G P as bs c).2.2 ∧ Fr (rA :: rB :: rC :: S) σ.sc sc'
  | [], bs, P, σ, c, L0, hl, _, _, _, _, hA, hB, hR, hc, _, _ => by
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    refine ⟨σ.sc, ?_, hc, Fr.refl _ _⟩
    simp only [List.length_nil, Function.iterate_zero, id, zipB, List.map_nil, List.append_nil]
    have e : ls3 σ.ls lA lB lR L0 = σ.ls := by
      funext l; simp only [ls3, Function.update_apply]
      split_ifs with h1 h2 h3 <;> subst_vars <;> simp_all
    rw [e]
  | a :: as, [], _, _, _, _, hl, _, _, _, _, _, _, _, _, _, _ => by simp at hl
  | a :: as, b :: bs, P, σ, c, L0, hl, hc, hvs, hI, hS, hA, hB, hR, hC, hcap, hM => by
    simp only [List.length_cons] at hl hcap hM ⊢
    rw [Function.iterate_succ_apply] at hM ⊢
    -- the first round
    set sc1 := Function.update (Function.update σ.sc rA (pos E ix a)) rB (pos E ix b) with hsc1
    set ls1 := Function.update (Function.update σ.ls lA (as.map (pos E ix))) lB
      (bs.map (pos E ix)) with hls1
    set σ1 : St := { σ with sc := sc1, ls := ls1 } with hσ1
    have e1 : exec E (.lpop rB lB) (exec E (.lpop rA lA) (mk E ix P σ)) = mk E ix P σ1 := by
      simp only [exec_mk_lpop]
      simp only [exec, hA, hB, Function.update_of_ne hAB.symm, List.map_cons, List.headD_cons,
        List.tail_cons, σ1, sc1, ls1]
    have h0' := h0; have h1' := h1; have hs' := hs
    simp only [List.mem_cons, not_or] at h0' h1' hs'
    have hc1 : Consts E σ1 := ⟨by simp [σ1, sc1, Function.update_of_ne h0'.1,
        Function.update_of_ne h0'.2.1, hc.1], by simp [σ1, sc1, Function.update_of_ne h1'.1,
        Function.update_of_ne h1'.2.1, hc.2]⟩
    have hb1 : ∀ τ, exec E (zipBody g rA rB rO rC rC' lA lB lR) τ =
        exec E (.seq (.lpush lR rO) (.mov rC rC'))
          (exec E g (exec E (.lpop rB lB) (exec E (.lpop rA lA) τ))) := fun τ => rfl
    have hM1 : E.n + (exec E g (mk E ix P σ1)).t ≤ E.M := by
      refine le_trans ?_ hM
      have := t_le_iter E (zipBody g rA rB rO rC rC' lA lB lR) as.length
        (exec E (zipBody g rA rB rO rC rC' lA lB lR) (mk E ix P σ))
      have h2 := t_le_exec E (.seq (.lpush lR rO) (.mov rC rC')) (exec E g (mk E ix P σ1))
      have e := hb1 (mk E ix P σ)
      rw [e1] at e
      rw [← e] at h2
      omega
    obtain ⟨sc2, h2, d2, c2, f2⟩ := hG P σ1 a b c hc1 (by simp [σ1, sc1,
        Function.update_of_ne hs'.1, Function.update_of_ne hs'.2.1, hvs])
      (by simp [σ1, sc1, Function.update_of_ne hrAB])
      (by simp [σ1, sc1]) (by simp [σ1, sc1, Function.update_of_ne hrAC.symm,
        Function.update_of_ne hrBC.symm, hC]) hM1
    have hIS1 : Inv E σ1 ∧ ScOK E σ1 := by
      have hi := inv_exec E (.seq (.lpop rA lA) (.lpop rB lB)) (mk E ix P σ) hI
      have hs := scOK_exec E hnM hWM (.seq (.lpop rA lA) (.lpop rB lB)) (mk E ix P σ) hI hS
      rw [exec_seq, e1] at hi hs; exact ⟨hi, hs⟩
    have hIS2 : Inv E { σ1 with sc := sc2 } ∧ ScOK E { σ1 with sc := sc2 } := by
      have hi := inv_exec E g (mk E ix P σ1) hIS1.1
      have hs := scOK_exec E hnM hWM g (mk E ix P σ1) hIS1.1 hIS1.2
      rw [h2] at hi hs; exact ⟨hi, hs⟩
    set P1 := (G P a b c).1
    set sc3 := Function.update sc2 rC (sc2 rC') with hsc3
    set ls3 := Function.update ls1 lR (L0 ++ [pos E ix (G P a b c).2.1]) with hls3
    set σ3 : St := { σ with sc := sc3, ls := ls3 } with hσ3
    have hR1 : σ1.ls lR = L0 := by
      simp [σ1, ls1, Function.update_of_ne hAR.symm, Function.update_of_ne hBR.symm, hR]
    have e3 : exec E (.seq (.lpush lR rO) (.mov rC rC')) (mk E ix P1 { σ1 with sc := sc2 }) =
        mk E ix P1 σ3 := by
      simp only [exec_seq, exec_mk_lpush, exec_mk_mov]
      have hO : pos E ix (G P a b c).2.1 ≤ E.M := d2 ▸ hIS2.2 rO
      simp only [exec, hR1, show L0.length < E.C by omega, ite_true, d2, min_eq_left hO]
      rfl
    have e4 : exec E (zipBody g rA rB rO rC rC' lA lB lR) (mk E ix P σ) = mk E ix P1 σ3 := by
      rw [hb1, e1, h2]; exact e3
    rw [e4] at hM ⊢
    have hIS3 : Inv E σ3 ∧ ScOK E σ3 := by
      have hi := inv_exec E (zipBody g rA rB rO rC rC' lA lB lR) (mk E ix P σ) hI
      have hs := scOK_exec E hnM hWM (zipBody g rA rB rO rC rC' lA lB lR) (mk E ix P σ) hI hS
      rw [e4] at hi hs; exact ⟨hi, hs⟩
    have fr3 : ∀ r, r ∉ rA :: rB :: rC :: S → sc3 r = σ.sc r := by
      intro r hr
      simp only [List.mem_cons, not_or] at hr
      simp only [sc3, Function.update_of_ne hr.2.2.1]
      rw [f2 r hr.2.2.2]
      simp [σ1, sc1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1]
    have hc3 : Consts E σ3 := ⟨by rw [← hc.1]; exact fr3 _ h0, by rw [← hc.2]; exact fr3 _ h1⟩
    obtain ⟨sc4, h4, d4, f4⟩ := iter_zipBody hnM hWM hG hAB hAR hBR hrAB hrAC hrBC h0 h1 hs as bs P1
      σ3 (G P a b c).2.2 (L0 ++ [pos E ix (G P a b c).2.1]) (by omega) hc3
      (by rw [← hvs]; exact fr3 _ hs) hIS3.1 hIS3.2
      (by simp [σ3, ls3, ls1, Function.update_of_ne hAR, Function.update_of_ne hAB])
      (by simp [σ3, ls3, ls1, Function.update_of_ne hBR])
      (by simp [σ3, ls3]) (by simp [σ3, sc3, c2]) (by simp; omega) hM
    refine ⟨sc4, ?_, d4, fun r hr => (f4 r hr).trans (fr3 r hr)⟩
    rw [h4]
    simp only [zipB, List.map_cons, List.append_assoc, List.singleton_append]
    congr 2
    funext l
    simp only [FhatGen.ls3, σ3, ls3, ls1, Function.update_apply]
    split_ifs <;> rfl

/-! ### Instances of `zipB` -/

/-- The full adder as a zip gadget. -/
def faG (p : SLP ι) (a b c : Wire ι) : SLP ι × Wire ι × Wire ι := fullAdd p a b c

/-- The mux as a zip gadget (the carry is unchanged). -/
def muxG (s : Wire ι) (p : SLP ι) (a b c : Wire ι) : SLP ι × Wire ι × Wire ι :=
  ((muxW p s a b).1, (muxW p s a b).2, c)

/-- `d ∧ ·` as a zip gadget (the second list and the carry are ignored). -/
def andG (d : Wire ι) (p : SLP ι) (a _b c : Wire ι) : SLP ι × Wire ι × Wire ι :=
  ((andW p d a).1, (andW p d a).2, c)

/-- `¬ ·` as a zip gadget. -/
def notG (p : SLP ι) (a _b c : Wire ι) : SLP ι × Wire ι × Wire ι :=
  ((notW p a).1, (notW p a).2, c)

theorem rippleAdd_eq : ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι),
    as.length = bs.length → rippleAdd p as bs c =
      ((zipB faG p as bs c).1, (zipB faG p as bs c).2.1 ++ [(zipB faG p as bs c).2.2])
  | p, [], [], c, _ => rfl
  | p, a :: as, b :: bs, c, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [rippleAdd, zipB, faG, rippleAdd_eq _ as bs _ h, List.cons_append]
  | p, [], _ :: _, c, h => by simp at h
  | p, _ :: _, [], c, h => by simp at h

theorem muxL_eq (s : Wire ι) : ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι),
    as.length = bs.length → muxL s p as bs = ((zipB (muxG s) p as bs c).1, (zipB (muxG s) p as bs c).2.1)
  | p, [], [], c, _ => rfl
  | p, a :: as, b :: bs, c, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [muxL, zipB, muxG, muxL_eq s _ as bs c h]
  | p, [], _ :: _, c, h => by simp at h
  | p, _ :: _, [], c, h => by simp at h

theorem andL_eq (d : Wire ι) : ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι),
    as.length = bs.length → andL d p as = ((zipB (andG d) p as bs c).1, (zipB (andG d) p as bs c).2.1)
  | p, [], [], c, _ => rfl
  | p, a :: as, b :: bs, c, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [andL, zipB, andG, andL_eq d _ as bs c h]
  | p, [], _ :: _, c, h => by simp at h
  | p, _ :: _, [], c, h => by simp at h

theorem notL_eq : ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι),
    as.length = bs.length → notL p as = ((zipB notG p as bs c).1, (zipB notG p as bs c).2.1)
  | p, [], [], c, _ => rfl
  | p, a :: as, b :: bs, c, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [notL, zipB, notG, notL_eq _ as bs c h]
  | p, [], _ :: _, c, h => by simp at h
  | p, _ :: _, [], c, h => by simp at h

theorem length_zipB (G : SLP ι → Wire ι → Wire ι → Wire ι → SLP ι × Wire ι × Wire ι) :
    ∀ (p : SLP ι) (as bs : List (Wire ι)) (c : Wire ι), as.length = bs.length →
      (zipB G p as bs c).2.1.length = as.length
  | p, [], [], c, _ => rfl
  | p, a :: as, b :: bs, c, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [zipB, length_zipB G _ as bs _ h]
  | p, [], _ :: _, c, h => by simp at h
  | p, _ :: _, [], c, h => by simp at h

theorem t_exec_nand (d a b : SR) (σ : St) : (exec E (.nand d a b) σ).t = σ.t + 1 := rfl

theorem t_fullAddC (σ : St) : (exec E fullAddC σ).t = σ.t + 14 := by
  simp only [fullAddC, xorC, orC, notC, exec_seq, t_exec_nand]

theorem gspec_fullAddC (hix : ∀ i, ix i < E.n) :
    GSpec E ix fullAddC (faG (ι := ι)) faRegs 16 17 19 18 20 rONE E.n := by
  intro P σ a b c hc _ ha hb hcc hM
  rw [t_fullAddC] at hM
  have hM' : E.n + P.length + 14 ≤ E.M := by simp at hM; omega
  exact exec_fullAddC hix hc P a b c ha hb hcc hM'

theorem t_muxC (d s a b m u v : SR) (σ : St) : (exec E (muxC d s a b m u v) σ).t = σ.t + 4 := by
  simp only [muxC, notC, exec_seq, t_exec_nand]

theorem t_andC (d a b u : SR) (σ : St) : (exec E (andC d a b u) σ).t = σ.t + 2 := by
  simp only [andC, notC, exec_seq, t_exec_nand]

theorem gspec_muxC (hix : ∀ i, ix i < E.n) (ws : Wire ι) :
    GSpec E ix (muxC 35 36 33 34 37 38 39) (muxG ws) [35, 37, 38, 39] 33 34 35 40 40 36
      (pos E ix ws) := by
  intro P σ a b c hc hs ha hb hcc hM
  rw [t_muxC] at hM
  obtain ⟨sc', h, d, f⟩ := exec_muxC (E := E) (ix := ix) hix hc P 35 36 33 34 37 38 39 ws a b
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs ha hb
    (by simp at hM; omega)
  exact ⟨sc', h, d, by rw [f 40 (by decide)]; exact hcc, f⟩

theorem gspec_andC (hix : ∀ i, ix i < E.n) (wd : Wire ι) :
    GSpec E ix (andC 35 36 33 37) (andG wd) [35, 37] 33 34 35 40 40 36 (pos E ix wd) := by
  intro P σ a b c hc hs ha hb hcc hM
  rw [t_andC] at hM
  obtain ⟨sc', h, d, f⟩ := exec_andC (E := E) (ix := ix) hix hc P 35 36 33 37 wd a
    (by decide) (by decide) hs ha (by simp at hM; omega)
  exact ⟨sc', h, d, by rw [f 40 (by decide)]; exact hcc, f⟩

theorem gspec_notC (hix : ∀ i, ix i < E.n) :
    GSpec E ix (notC 35 33) (notG (ι := ι)) [35] 33 34 35 40 40 rONE E.n := by
  intro P σ a b c hc _ ha hb hcc hM
  have hM' : E.n + 1 + P.length ≤ E.M := by simp [notC, t_exec_nand] at hM; omega
  refine ⟨_, exec_notC hix hc P 35 33 a ha hM', by simp [notG], ?_, Fr.update (by simp) _⟩
  simp [Function.update_of_ne (by decide : (40 : SR) ≠ 35), hcc, notG]

/-! ### The list codes -/

/-- `lR := lR ++ rippleAdd lA lB (reg 18)` (`n` holds the length). -/
def rippleAddC (n : SR) (lA lB lR : LR) : Code :=
  .seq (.rep n (zipBody fullAddC 16 17 19 18 20 lA lB lR)) (.lpush lR 18)

/-- `lR := lR ++ muxL (reg 36) lA lB`. -/
def muxLC (n : SR) (lA lB lR : LR) : Code :=
  .seq (.mov 40 rONE) (.rep n (zipBody (muxC 35 36 33 34 37 38 39) 33 34 35 40 40 lA lB lR))

/-- `lR := lR ++ andL (reg 36) lA` (`lB` is scratch). -/
def andLC (n : SR) (lA lB lR : LR) : Code :=
  .seq (.mov 40 rONE) (.seq (.lmov lB lA)
    (.rep n (zipBody (andC 35 36 33 37) 33 34 35 40 40 lA lB lR)))

/-- `lR := lR ++ notL lA` (`lB` is scratch). -/
def notLC (n : SR) (lA lB lR : LR) : Code :=
  .seq (.mov 40 rONE) (.seq (.lmov lB lA) (.rep n (zipBody (notC 35 33) 33 34 35 40 40 lA lB lR)))

theorem exec_rep (a : SR) (body : Code) (σ : St) :
    exec E (.rep a body) σ = (exec E body)^[σ.sc a] σ := rfl

theorem exec_rippleAddC (hnM : E.n ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n) {n : SR}
    {lA lB lR : LR} (hAB : lA ≠ lB) (hAR : lA ≠ lR) (hBR : lB ≠ lR) (as bs : List (Wire ι))
    (P : SLP ι) (σ : St) (c : Wire ι) (L0 : List ℕ) (hl : as.length = bs.length)
    (hc : Consts E σ) (hI : Inv E σ) (hS : ScOK E σ) (hA : σ.ls lA = as.map (pos E ix))
    (hB : σ.ls lB = bs.map (pos E ix)) (hR : σ.ls lR = L0) (hC : σ.sc 18 = pos E ix c)
    (hn : σ.sc n = as.length) (hcap : L0.length + as.length + 1 ≤ E.C)
    (hM : E.n + (exec E (rippleAddC n lA lB lR) (mk E ix P σ)).t ≤ E.M) :
    ∃ sc', exec E (rippleAddC n lA lB lR) (mk E ix P σ) = mk E ix (rippleAdd P as bs c).1
        { σ with sc := sc', ls := ls3 σ.ls lA lB lR (L0 ++ (rippleAdd P as bs c).2.map (pos E ix)) } ∧
      Fr (16 :: 17 :: 18 :: faRegs) σ.sc sc' := by
  rw [rippleAddC, exec_seq, exec_rep] at hM ⊢
  rw [mk_sc, hn] at hM ⊢
  obtain ⟨sc1, h1, d1, f1⟩ := iter_zipBody hnM hWM (gspec_fullAddC hix) hAB hAR hBR (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) as bs P σ c L0 hl hc hc.1 hI hS
    hA hB hR hC (by omega) hM
  set L1 := L0 ++ (zipB faG P as bs c).2.1.map (pos E ix) with hL1
  have hS1 : ScOK E { σ with sc := sc1, ls := ls3 σ.ls lA lB lR L1 } := by
    have := scOK_exec E hnM hWM (.rep n (zipBody fullAddC 16 17 19 18 20 lA lB lR)) (mk E ix P σ)
      hI hS
    rw [exec_rep, mk_sc, hn, h1] at this; exact this
  rw [h1]
  refine ⟨sc1, ?_, f1⟩
  have hlen : L1.length < E.C := by
    simp only [L1, List.length_append, List.length_map, length_zipB _ _ _ _ _ hl]; omega
  have h18 : min (pos E ix (zipB faG P as bs c).2.2) E.M = pos E ix (zipB faG P as bs c).2.2 :=
    min_eq_left (d1 ▸ hS1 18)
  rw [exec_mk_lpush, rippleAdd_eq P as bs c hl]
  congr 1
  have e : (ls3 σ.ls lA lB lR L1) lR = L1 := by simp [ls3]
  simp only [exec, e, hlen, ite_true, h18, d1]
  congr 1
  simp only [ls3, Function.update_idem, L1, List.map_append, List.map_singleton, List.append_assoc]

theorem exec_muxLC (hnM : E.n ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n) {n : SR}
    {lA lB lR : LR} (hAB : lA ≠ lB) (hAR : lA ≠ lR) (hBR : lB ≠ lR) (ws : Wire ι)
    (as bs : List (Wire ι)) (P : SLP ι) (σ : St) (L0 : List ℕ) (hl : as.length = bs.length)
    (hc : Consts E σ) (hI : Inv E σ) (hS : ScOK E σ) (hs : σ.sc 36 = pos E ix ws)
    (hA : σ.ls lA = as.map (pos E ix)) (hB : σ.ls lB = bs.map (pos E ix)) (hR : σ.ls lR = L0)
    (hn : σ.sc n = as.length) (hn40 : n ≠ 40) (hcap : L0.length + as.length ≤ E.C)
    (hM : E.n + (exec E (muxLC n lA lB lR) (mk E ix P σ)).t ≤ E.M) :
    ∃ sc', exec E (muxLC n lA lB lR) (mk E ix P σ) = mk E ix (muxL ws P as bs).1
        { σ with sc := sc', ls := ls3 σ.ls lA lB lR (L0 ++ (muxL ws P as bs).2.map (pos E ix)) } ∧
      Fr [33, 34, 40, 35, 37, 38, 39] σ.sc sc' := by
  set σ0 : St := { σ with sc := Function.update σ.sc 40 E.n }
  have e0 : exec E (.mov 40 rONE) (mk E ix P σ) = mk E ix P σ0 := by
    simp only [exec_mk_mov]; simp [exec, σ0, hc.1]
  rw [muxLC, exec_seq, e0, exec_rep] at hM ⊢
  have hn0 : σ0.sc n = as.length := by simp [σ0, Function.update_of_ne hn40, hn]
  rw [mk_sc, hn0] at hM ⊢
  obtain ⟨sc1, h1, _, f1⟩ := iter_zipBody hnM hWM (gspec_muxC hix ws) hAB hAR hBR (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) as bs P σ0 .one L0 hl
    ⟨by simp [σ0, Function.update_of_ne (by decide : rONE ≠ 40), hc.1],
      by simp [σ0, Function.update_of_ne (by decide : rZ ≠ 40), hc.2]⟩ (by simp [σ0, Function.update_of_ne (by decide : (36 : SR) ≠ 40), hs]) hI
    (fun r => by by_cases h : r = 40 <;> simp [σ0, h, hnM, hS r]) hA hB hR (by simp [σ0, pos])
    (by omega) hM
  rw [h1, muxL_eq ws P as bs .one hl]
  refine ⟨sc1, rfl, fun r hr => ?_⟩
  rw [f1 r hr]
  simp only [σ0]
  rw [Function.update_of_ne (fun h => hr (by simp [h]))]

theorem exec_andLC (hnM : E.n ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n) {n : SR}
    {lA lB lR : LR} (hAB : lA ≠ lB) (hAR : lA ≠ lR) (hBR : lB ≠ lR) (wd : Wire ι)
    (as : List (Wire ι)) (P : SLP ι) (σ : St) (L0 : List ℕ)
    (hc : Consts E σ) (hI : Inv E σ) (hS : ScOK E σ) (hs : σ.sc 36 = pos E ix wd)
    (hA : σ.ls lA = as.map (pos E ix)) (hR : σ.ls lR = L0)
    (hn : σ.sc n = as.length) (hn40 : n ≠ 40) (hcap : L0.length + as.length ≤ E.C)
    (hM : E.n + (exec E (andLC n lA lB lR) (mk E ix P σ)).t ≤ E.M) :
    ∃ sc', exec E (andLC n lA lB lR) (mk E ix P σ) = mk E ix (andL wd P as).1
        { σ with sc := sc', ls := ls3 σ.ls lA lB lR (L0 ++ (andL wd P as).2.map (pos E ix)) } ∧
      Fr [33, 34, 40, 35, 37] σ.sc sc' := by
  set σ0 : St := { σ with sc := Function.update σ.sc 40 E.n, ls := Function.update σ.ls lB (σ.ls lA) }
  have e0 : exec E (.lmov lB lA) (exec E (.mov 40 rONE) (mk E ix P σ)) = mk E ix P σ0 := by
    simp only [exec_mk_mov]; simp [exec, σ0, hc.1]; rfl
  rw [andLC, exec_seq, exec_seq, e0, exec_rep] at hM ⊢
  have hn0 : σ0.sc n = as.length := by simp [σ0, Function.update_of_ne hn40, hn]
  rw [mk_sc, hn0] at hM ⊢
  have hI0 : Inv E σ0 := by
    have := inv_exec E (.seq (.mov 40 rONE) (.lmov lB lA)) (mk E ix P σ) hI
    rw [exec_seq, e0] at this; exact this
  obtain ⟨sc1, h1, _, f1⟩ := iter_zipBody hnM hWM (gspec_andC hix wd) hAB hAR hBR (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) as as P σ0 .one L0 rfl
    ⟨by simp [σ0, Function.update_of_ne (by decide : rONE ≠ 40), hc.1],
      by simp [σ0, Function.update_of_ne (by decide : rZ ≠ 40), hc.2]⟩ (by simp [σ0, Function.update_of_ne (by decide : (36 : SR) ≠ 40), hs]) hI0
    (fun r => by by_cases h : r = 40 <;> simp [σ0, h, hnM, hS r])
    (by simp [σ0, Function.update_of_ne hAB, hA]) (by simp [σ0, hA])
    (by simp [σ0, Function.update_of_ne hBR.symm, hR]) (by simp [σ0, pos]) (by omega) hM
  rw [h1, andL_eq wd P as as .one rfl]
  refine ⟨sc1, ?_, fun r hr => ?_⟩
  · congr 2
    funext l; simp only [ls3, σ0, Function.update_apply]; split_ifs <;> rfl
  · rw [f1 r hr]
    simp only [σ0]
    rw [Function.update_of_ne (fun h => hr (by simp [h]))]

theorem exec_notLC (hnM : E.n ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n) {n : SR}
    {lA lB lR : LR} (hAB : lA ≠ lB) (hAR : lA ≠ lR) (hBR : lB ≠ lR)
    (as : List (Wire ι)) (P : SLP ι) (σ : St) (L0 : List ℕ)
    (hc : Consts E σ) (hI : Inv E σ) (hS : ScOK E σ)
    (hA : σ.ls lA = as.map (pos E ix)) (hR : σ.ls lR = L0)
    (hn : σ.sc n = as.length) (hn40 : n ≠ 40) (hcap : L0.length + as.length ≤ E.C)
    (hM : E.n + (exec E (notLC n lA lB lR) (mk E ix P σ)).t ≤ E.M) :
    ∃ sc', exec E (notLC n lA lB lR) (mk E ix P σ) = mk E ix (notL P as).1
        { σ with sc := sc', ls := ls3 σ.ls lA lB lR (L0 ++ (notL P as).2.map (pos E ix)) } ∧
      Fr [33, 34, 40, 35] σ.sc sc' := by
  set σ0 : St := { σ with sc := Function.update σ.sc 40 E.n, ls := Function.update σ.ls lB (σ.ls lA) }
  have e0 : exec E (.lmov lB lA) (exec E (.mov 40 rONE) (mk E ix P σ)) = mk E ix P σ0 := by
    simp only [exec_mk_mov]; simp [exec, σ0, hc.1]; rfl
  rw [notLC, exec_seq, exec_seq, e0, exec_rep] at hM ⊢
  have hn0 : σ0.sc n = as.length := by simp [σ0, Function.update_of_ne hn40, hn]
  rw [mk_sc, hn0] at hM ⊢
  have hI0 : Inv E σ0 := by
    have := inv_exec E (.seq (.mov 40 rONE) (.lmov lB lA)) (mk E ix P σ) hI
    rw [exec_seq, e0] at this; exact this
  obtain ⟨sc1, h1, _, f1⟩ := iter_zipBody hnM hWM (gspec_notC hix) hAB hAR hBR (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) as as P σ0 .one L0 rfl
    ⟨by simp [σ0, Function.update_of_ne (by decide : rONE ≠ 40), hc.1],
      by simp [σ0, Function.update_of_ne (by decide : rZ ≠ 40), hc.2]⟩ (by simp [σ0, Function.update_of_ne (by decide : rONE ≠ 40), hc.1]) hI0
    (fun r => by by_cases h : r = 40 <;> simp [σ0, h, hnM, hS r])
    (by simp [σ0, Function.update_of_ne hAB, hA]) (by simp [σ0, hA])
    (by simp [σ0, Function.update_of_ne hBR.symm, hR]) (by simp [σ0, pos]) (by omega) hM
  rw [h1, notL_eq P as as .one rfl]
  refine ⟨sc1, ?_, fun r hr => ?_⟩
  · congr 2
    funext l; simp only [ls3, σ0, Function.update_apply]; split_ifs <;> rfl
  · rw [f1 r hr]
    simp only [σ0]
    rw [Function.update_of_ne (fun h => hr (by simp [h]))]

end FhatGen

end SigabaNeo.Lattices
