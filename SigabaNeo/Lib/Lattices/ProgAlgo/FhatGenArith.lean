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
    (S : List SR) (rA rB rO rC rC' : SR) : Prop :=
  ∀ (P : SLP ι) (σ : St) (a b c : Wire ι), Consts E σ → σ.sc rA = pos E ix a →
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
    {rA rB rO rC rC' : SR} {lA lB lR : LR} (hG : GSpec E ix g G S rA rB rO rC rC')
    (hAB : lA ≠ lB) (hAR : lA ≠ lR) (hBR : lB ≠ lR) (hrAB : rA ≠ rB) (hrAC : rA ≠ rC)
    (hrBC : rB ≠ rC) (h0 : rONE ∉ rA :: rB :: rC :: S) (h1 : rZ ∉ rA :: rB :: rC :: S) :
    ∀ (as bs : List (Wire ι)) (P : SLP ι) (σ : St) (c : Wire ι) (L0 : List ℕ),
      as.length = bs.length → Consts E σ → Inv E σ → ScOK E σ →
      σ.ls lA = as.map (pos E ix) → σ.ls lB = bs.map (pos E ix) → σ.ls lR = L0 →
      σ.sc rC = pos E ix c → L0.length + as.length ≤ E.C →
      E.n + ((exec E (zipBody g rA rB rO rC rC' lA lB lR))^[as.length] (mk E ix P σ)).t ≤ E.M →
      ∃ sc', (exec E (zipBody g rA rB rO rC rC' lA lB lR))^[as.length] (mk E ix P σ) =
        mk E ix (zipB G P as bs c).1
          { σ with sc := sc', ls := ls3 σ.ls lA lB lR (L0 ++ (zipB G P as bs c).2.1.map (pos E ix)) } ∧
        sc' rC = pos E ix (zipB G P as bs c).2.2 ∧ Fr (rA :: rB :: rC :: S) σ.sc sc'
  | [], bs, P, σ, c, L0, hl, _, _, _, hA, hB, hR, hc, _, _ => by
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    refine ⟨σ.sc, ?_, hc, Fr.refl _ _⟩
    simp only [List.length_nil, Function.iterate_zero, id, zipB, List.map_nil, List.append_nil]
    have e : ls3 σ.ls lA lB lR L0 = σ.ls := by
      funext l; simp only [ls3, Function.update_apply]
      split_ifs with h1 h2 h3 <;> subst_vars <;> simp_all
    rw [e]
  | a :: as, [], _, _, _, _, hl, _, _, _, _, _, _, _, _, _ => by simp at hl
  | a :: as, b :: bs, P, σ, c, L0, hl, hc, hI, hS, hA, hB, hR, hC, hcap, hM => by
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
    have h0' := h0; have h1' := h1
    simp only [List.mem_cons, not_or] at h0' h1'
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
    obtain ⟨sc2, h2, d2, c2, f2⟩ := hG P σ1 a b c hc1 (by simp [σ1, sc1, Function.update_of_ne hrAB])
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
    obtain ⟨sc4, h4, d4, f4⟩ := iter_zipBody hnM hWM hG hAB hAR hBR hrAB hrAC hrBC h0 h1 as bs P1
      σ3 (G P a b c).2.2 (L0 ++ [pos E ix (G P a b c).2.1]) (by omega) hc3 hIS3.1 hIS3.2
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

end FhatGen

end SigabaNeo.Lattices
