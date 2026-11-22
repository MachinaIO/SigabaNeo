import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenLeaves

/-!
# Generating gate tapes: the balanced tree of additions

A list of numbers (each `k` wires) is held flattened in the list `12`, its length in the register
`55`. `pairBody` adds the first two numbers (`modAddC`) into the list `13`, or moves a last single
number; `iter_pairBody`: enough rounds of it are `pairRound`.
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-- One step of `pairRound` (register `6 = 2`, `7 = 0`). -/
def pairBody : Code :=
  .ifLt 55 6 (.ifLt 7 55 (.seq (takeC 2 12 13) (.seq (.zero 55) (.inc 56))) .skip)
    (.seq (.lnil 0) (.seq (takeC 2 12 0) (.seq (.lnil 1) (.seq (takeC 2 12 1) (.seq modAddC
      (.seq (takeC 2 2 13) (.seq (.sub 55 6) (.inc 56))))))))

/-- The flattened positions of a list of numbers. -/
def flatPos (L : List (List (Wire ι))) : List ℕ := (L.map (List.map (pos E ix))).flatten

theorem iter_skip_of (c : Code) (σ : St) (h : exec E c σ = σ) : ∀ j, (exec E c)^[j] σ = σ
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply, h, iter_skip_of c σ h j]

theorem exec_pairBody_done (σ : St) (h55 : σ.sc 55 = 0) (h6 : σ.sc 6 = 2) (h7 : σ.sc 7 = 0) :
    exec E pairBody σ = σ := by
  simp [pairBody, exec_ifLt, h55, h6, h7, exec]

/-- The constant registers of the tree: `Cst k K`, `6 = 2`, `7 = 0`. -/
def CstR (k K : ℕ) (σ : St) : Prop := Cst (E := E) k K σ ∧ σ.sc 6 = 2 ∧ σ.sc 7 = 0

theorem cstR_of {k K : ℕ} {σ τ : St} (h : CstR (E := E) k K σ)
    (hf : ∀ r : SR, r.val < 8 → τ.sc r = σ.sc r) : CstR (E := E) k K τ := by
  obtain ⟨⟨⟨h0, h1⟩, h2, h3, h4⟩, h6, h7⟩ := h
  exact ⟨⟨⟨by rw [hf 0 (by decide), h0], by rw [hf 1 (by decide), h1]⟩,
    by rw [hf 2 (by decide), h2], by rw [hf 3 (by decide), h3], by rw [hf 4 (by decide), h4]⟩,
    by rw [hf 6 (by decide), h6], by rw [hf 7 (by decide), h7]⟩

theorem flatPos_cons (a : List (Wire ι)) (L : List (List (Wire ι))) :
    flatPos (E := E) (ix := ix) (a :: L) = a.map (pos E ix) ++ flatPos (E := E) (ix := ix) L := rfl

set_option maxHeartbeats 4000000 in
theorem iter_pairBody (hnM : E.n + 1 ≤ E.M) (hWM : E.W ≤ E.M) (hix : ∀ i, ix i < E.n)
    {k K : ℕ} (hK : K ≤ k + 1) :
    ∀ (j : ℕ) (L : List (List (Wire ι))) (P : SLP ι) (σ : St) (L13 : List ℕ) (c : ℕ),
      (L.length + 1) / 2 ≤ j → (∀ a ∈ L, a.length = k) → CstR (E := E) k K σ → Inv E σ →
      ScOK E σ → σ.ls 12 = flatPos (E := E) (ix := ix) L → σ.ls 13 = L13 →
      σ.sc 55 = L.length → σ.sc 56 = c → L13.length + L.length * k ≤ E.C → k + 3 ≤ E.C →
      k + 2 ≤ E.M → c + L.length ≤ E.M →
      E.n + ((exec E pairBody)^[j] (mk E ix P σ)).t ≤ E.M →
      ∃ sc' ls', (exec E pairBody)^[j] (mk E ix P σ) =
          mk E ix (pairRound (.gate 0) (2 ^ K) k P L).1 (setSL σ sc' ls') ∧
        ls' 13 = L13 ++ flatPos (E := E) (ix := ix) (pairRound (.gate 0) (2 ^ K) k P L).2 ∧
        sc' 56 = c + (pairRound (.gate 0) (2 ^ K) k P L).2.length ∧
        (∀ r : SR, r.val < 16 ∨ (42 < r.val ∧ r.val < 55) ∨ 56 < r.val → sc' r = σ.sc r) ∧
        (∀ l : LR, (8 < l.val ∧ l.val < 12) ∨ 13 < l.val → ls' l = σ.ls l)
  | j, [], P, σ, L13, c, _, _, hc, _, _, _, h13, h55, h56, _, _, _, _, _ => by
    rw [iter_skip_of _ _ (exec_pairBody_done (mk E ix P σ) h55 hc.2.1 hc.2.2) j]
    exact ⟨σ.sc, σ.ls, by simp [setSL, pairRound], by simp [pairRound, flatPos, h13],
      by simp [pairRound, h56], fun _ _ => rfl, fun _ _ => rfl⟩
  | j, [a], P, σ, L13, c, hj, hL, hc, hI, _, h12, h13, h55, h56, hcap, _, _, hcM, _ => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by simp at hj; omega⟩
    have ha := hL a (by simp)
    obtain ⟨sc1, h1, f1⟩ := exec_takeC (E := E) (n := 2) (lA := 12) (lR := 13) (by decide)
      (a.map (pos E ix)) [] L13 σ hI (by rw [h12]; simp [flatPos]) h13
      (by rw [hc.1.2.1, List.length_map, ha]) (by simp at hcap; simp [ha]; omega)
    set σ1 := setSL σ (Function.update (Function.update sc1 55 0) 56 (c + 1))
      (Function.update (Function.update σ.ls 12 []) 13 (L13 ++ a.map (pos E ix)))
    have e1 : exec E pairBody (mk E ix P σ) = mk E ix P σ1 := by
      simp only [pairBody, exec_ifLt, mk_sc, h55, hc.2.1, hc.2.2, List.length_singleton]
      simp only [show 1 < 2 by decide, show 0 < 1 by decide, ite_true, exec_seq]
      rw [exec_mk_noNand _ (by simp [NoNand, takeC]), h1]
      have h56' : sc1 56 = c := by rw [f1 56 (by decide), h56]
      simp only [exec, σ1, setSL, mk, Function.update_self, h56',
        Function.update_of_ne (show (56 : SR) ≠ 55 by decide),
        min_eq_left (show c + 1 ≤ E.M by simpa using hcM)]
    rw [Function.iterate_succ_apply, e1, iter_skip_of _ _ (exec_pairBody_done (mk E ix P σ1)
      (by simp [σ1, setSL]) (by simp [σ1, setSL]; rw [f1 6 (by decide), hc.2.1])
      (by simp [σ1, setSL]; rw [f1 7 (by decide), hc.2.2])) j]
    refine ⟨_, _, rfl, by simp [σ1, setSL, pairRound, flatPos], by simp [σ1, setSL, pairRound],
      fun r hr => ?_, fun l hl => ?_⟩
    · try simp only [σ1, setSL]
      rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
        Function.update_of_ne (by rintro rfl; revert hr; decide), f1 r (by
          simp only [List.mem_singleton]; rintro rfl; revert hr; decide)]
    · try simp only [σ1, setSL]
      rw [Function.update_of_ne (by rintro rfl; revert hl; decide),
        Function.update_of_ne (by rintro rfl; revert hl; decide)]
  | j, a :: b :: rest, P, σ, L13, c, hj, hL, hc, hI, hS, h12, h13, h55, h56, hcap, hcap', hkM,
      hcM, hM => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by simp at hj; omega⟩
    have hnM' : E.n ≤ E.M := by omega
    have ha := hL a (by simp)
    have hb := hL b (by simp)
    have hr : ∀ x ∈ rest, x.length = k := fun x hx => hL x (by simp [hx])
    simp only [List.length_cons] at h55 hcap hcM hj
    -- move `a` into `0` and `b` into `1`
    obtain ⟨sc1, h1, f1⟩ := exec_takeC (E := E) (n := 2) (lA := 12) (lR := 0) (by decide)
      (a.map (pos E ix)) (flatPos (E := E) (ix := ix) (b :: rest)) [] (exec E (.lnil 0) σ)
      (inv_exec E _ σ hI) (by simp [exec, h12, flatPos_cons]) (by simp [exec])
      (by simp [exec, hc.1.2.1, ha]) (by simp [ha]; omega)
    set τ1 : St := setSL (exec E (.lnil 0) σ) sc1 (Function.update (Function.update
      (exec E (.lnil 0) σ).ls 12 (flatPos (E := E) (ix := ix) (b :: rest))) 0 ([] ++ a.map (pos E ix)))
    have h1' : exec E (takeC 2 12 0) (exec E (.lnil 0) σ) = τ1 := by rw [h1]; rfl
    have hI1 : Inv E (exec E (.lnil 1) τ1) := by
      have := inv_exec E (.seq (.lnil 0) (.seq (takeC 2 12 0) (.lnil 1))) σ hI
      simp only [exec_seq] at this; rw [h1'] at this; exact this
    obtain ⟨sc2, h2, f2⟩ := exec_takeC (E := E) (n := 2) (lA := 12) (lR := 1) (by decide)
      (b.map (pos E ix)) (flatPos (E := E) (ix := ix) rest) [] (exec E (.lnil 1) τ1) hI1
      (by simp [exec, τ1, setSL, flatPos_cons]) (by simp [exec])
      (by simp [exec, τ1, setSL]; rw [f1 2 (by decide)]; simp [exec, hc.1.2.1, hb])
      (by simp [hb]; omega)
    set τ2 : St := { exec E (.lnil 1) τ1 with sc := sc2, ls := Function.update (Function.update
      (exec E (.lnil 1) τ1).ls 12 (flatPos (E := E) (ix := ix) rest)) 1 ([] ++ b.map (pos E ix)) }
    have hτ2s : ∀ r : SR, r ≠ 41 → τ2.sc r = σ.sc r := fun r hr => by
      show sc2 r = _
      rw [f2 r (by simpa using hr)]; show sc1 r = _; rw [f1 r (by simpa using hr)]; rfl
    have hτ2l : ∀ l : LR, l ≠ 0 → l ≠ 1 → l ≠ 12 → τ2.ls l = σ.ls l := fun l h0 h1 h12' => by
      simp [τ2, exec, τ1, setSL, Function.update_of_ne h0, Function.update_of_ne h1,
        Function.update_of_ne h12']
    have e2 : exec E pairBody (mk E ix P σ) = exec E (.seq (.sub 55 6) (.inc 56))
        (exec E (takeC 2 2 13) (exec E modAddC (mk E ix P τ2))) := by
      simp only [pairBody, exec_ifLt, mk_sc, h55, hc.2.1,
        show ¬ (rest.length + 1 + 1 < 2) by omega, ite_false, exec_seq]
      rw [exec_mk_noNand (.lnil 0) trivial, exec_mk_noNand (takeC 2 12 0) (by simp [NoNand, takeC]),
        h1', exec_mk_noNand (.lnil 1) trivial, exec_mk_noNand (takeC 2 12 1)
        (by simp [NoNand, takeC]), h2]
    have hIS2 : Inv E τ2 ∧ ScOK E τ2 := by
      have hi := inv_exec E (.seq (.lnil 0) (.seq (takeC 2 12 0) (.seq (.lnil 1) (takeC 2 12 1))))
        σ hI
      have hs := scOK_exec E hnM' hWM (.seq (.lnil 0) (.seq (takeC 2 12 0) (.seq (.lnil 1)
        (takeC 2 12 1)))) σ hI hS
      simp only [exec_seq] at hi hs; rw [h1', h2] at hi hs; exact ⟨hi, hs⟩
    rw [Function.iterate_succ_apply, e2] at hM ⊢
    -- the addition
    obtain ⟨sc3, ls3', h3, d3, f3, g3⟩ := exec_modAddC hnM hWM hix hK a b P τ2
      (by have := hc.1; exact ⟨⟨by rw [hτ2s 0 (by decide), this.1.1],
        by rw [hτ2s 1 (by decide), this.1.2]⟩, by rw [hτ2s 2 (by decide), this.2.1],
        by rw [hτ2s 3 (by decide), this.2.2.1], by rw [hτ2s 4 (by decide), this.2.2.2]⟩)
      hIS2.1 hIS2.2 (by simp [τ2, exec, τ1, setSL]) (by simp [τ2]) ha hb hcap' hkM
      (le_trans (Nat.add_le_add_left (le_trans (le_trans (t_le_exec E (takeC 2 2 13) _)
        (t_le_exec E (.seq (.sub 55 6) (.inc 56)) _)) (t_le_iter E pairBody j _)) _) hM)
    set r := modAdd (.gate 0) (2 ^ K) k P a b
    have hrl : r.2.length = k := length_modAdd_eq _ _ _ _ _ _ ha hb
    rw [h3] at hM ⊢
    have hs3 : ∀ x : SR, x.val < 16 ∨ 42 < x.val → sc3 x = σ.sc x := fun x hx => by
      rw [f3 x hx, hτ2s x (by rintro rfl; revert hx; decide)]
    have hl3 : ∀ l : LR, 8 < l.val → l ≠ 12 → ls3' l = σ.ls l := fun l hl h12' => by
      rw [g3 l hl, hτ2l l (by rintro rfl; revert hl; decide) (by rintro rfl; revert hl; decide) h12']
    obtain ⟨sc4, h4, f4⟩ := exec_takeC (E := E) (n := 2) (lA := 2) (lR := 13) (by decide)
      (r.2.map (pos E ix)) [] L13 (setSL τ2 sc3 ls3')
      (is_exec hnM' hWM h3 hIS2).1 (by simp [setSL, d3])
      (by show ls3' 13 = _; rw [hl3 13 (by decide) (by decide), h13])
      (by show sc3 2 = _; rw [hs3 2 (by decide), hc.1.2.1, List.length_map, hrl])
      (by simp [hrl]; nlinarith)
    set σ5 := setSL σ (Function.update (Function.update sc4 55 rest.length) 56 (c + 1))
      (Function.update (Function.update ls3' 2 []) 13 (L13 ++ r.2.map (pos E ix)))
    have h4' : exec E (.seq (.sub 55 6) (.inc 56)) (exec E (takeC 2 2 13) (setSL τ2 sc3 ls3')) =
        σ5 := by
      rw [h4]
      have h55' : sc4 55 = rest.length + 2 := by
        rw [f4 55 (by decide)]; show sc3 55 = _; rw [hs3 55 (by decide), h55]
      have h6' : sc4 6 = 2 := by rw [f4 6 (by decide)]; show sc3 6 = _; rw [hs3 6 (by decide), hc.2.1]
      have h56' : sc4 56 = c := by rw [f4 56 (by decide)]; show sc3 56 = _; rw [hs3 56 (by decide), h56]
      simp only [exec_seq, exec, setSL, σ5, Function.update_self, h55', h6', h56',
        Function.update_of_ne (show (56 : SR) ≠ 55 by decide), Nat.add_sub_cancel,
        min_eq_left (show c + 1 ≤ E.M by omega)]
      rfl
    rw [exec_mk_noNand (takeC 2 2 13) (by simp [NoNand, takeC]),
      exec_mk_noNand (.seq (.sub 55 6) (.inc 56)) ⟨trivial, trivial⟩, h4'] at hM ⊢
    have hIS5 : Inv E σ5 ∧ ScOK E σ5 := by
      have := is_exec hnM' hWM h3 hIS2
      have h := is_exec hnM' hWM (c := .seq (takeC 2 2 13) (.seq (.sub 55 6) (.inc 56)))
        (τ := setSL τ2 sc3 ls3') (τ' := σ5) (by rw [exec_seq]; exact h4') this
      exact h
    have hs5 : ∀ x : SR, x.val < 16 ∨ (42 < x.val ∧ x.val < 55) ∨ 56 < x.val → σ5.sc x = σ.sc x :=
      fun x hx => by
        simp only [σ5, setSL]
        rw [Function.update_of_ne (by rintro rfl; revert hx; decide),
          Function.update_of_ne (by rintro rfl; revert hx; decide), f4 x (by
            simp only [List.mem_singleton]; rintro rfl; revert hx; decide)]
        exact hs3 x (by omega)
    have hl5 : ∀ l : LR, (8 < l.val ∧ l.val < 12) ∨ 13 < l.val → σ5.ls l = σ.ls l := fun l hl => by
      simp only [σ5, setSL]
      rw [Function.update_of_ne (by rintro rfl; revert hl; decide),
        Function.update_of_ne (by rintro rfl; revert hl; decide),
        hl3 l (by omega) (by rintro rfl; revert hl; decide)]
    obtain ⟨sc', ls', h', d', c', f', g'⟩ := iter_pairBody hnM hWM hix hK j rest r.1 σ5
      (L13 ++ r.2.map (pos E ix)) (c + 1) (by omega) hr
      (cstR_of hc (fun x hx => hs5 x (by omega))) hIS5.1 hIS5.2
      (by simp only [σ5, setSL]; rw [Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), g3 12 (by decide)]; simp [τ2])
      (by simp [σ5, setSL]) (by simp [σ5, setSL]) (by simp [σ5, setSL])
      (by simp [hrl]; nlinarith) hcap' hkM (by omega) hM
    refine ⟨sc', ls', h', ?_, ?_, fun x hx => (f' x hx).trans (hs5 x hx),
      fun l hl => (g' l hl).trans (hl5 l hl)⟩
    · rw [d']; simp [pairRound, flatPos, r, List.append_assoc]
    · rw [c']; simp [pairRound, r]; omega

end FhatGen

end SigabaNeo.Lattices
