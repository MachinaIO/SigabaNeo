import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMDot
import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.GadRow

/-!
# The coefficients of the lookup tables on the ring-word machine (package F4)

For the index `j < W` of the `LUT` loop (its binary digits on register `140`, least significant
first) and the table of one step of the branching program (a stream on register `141`), the code
`coefC last` writes on register `142` the word of

  `W⁻¹ Σ_{u<W} X^{L(u)} σ_{g^j}(X^{−u})`   (`last = false`: entries of `14` bits, `L(u)` their value),
  `W⁻¹ Σ_{u<W} L(u) σ_{g^j}(X^{−u})`       (`last = true`: entries of one bit),

i.e. `α_{g^j,L}` and `v_{g^j,L}` (`PE.Impl.ExpLUT.Prog.DecCoefMath` makes the link). Each round
`u` copies `m = X^{−u}`, applies `σ_{g_t}` (template register `20 + t` of length `κ_t`) for the set
bits `t < 22` of `j` (`autBitsN`), multiplies by `X^{2^{b'}}` (template `42 + b'` of length
`2N − 2^{b'}`, i.e. `X^{−(2N − 2^{b'})}`) for the set bits `b' < 14` of the entry (`rhoBitsN`) or
keeps/zeroes it by the bit of the entry (last step), and accumulates; `m := X^{−1} m`. Finally
`α := 2^{−|t₁₃|} acc` (`rotB` by the template `13` of `b` bits: `W⁻¹ = 2^{K−b}`).

`gadC` writes on register `143` the word of the matrix `α G` (`(α 2^i)_i ++ 0 ++ 0 ++ (α 2^i)_i`),
and `incC` increments the binary word of `j` on register `140` (`incW`).

All registers written are in `140 … 159` (`CK` holds throughout).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG

/-! ### Registers and code -/

/-- The template of `σ_{g_t}`: register `20 + t`. -/
def kReg (t : ℕ) : Fin 200 := ⟨20 + t % 22, by omega⟩
/-- The template of `X^{2^{b'}}`: register `42 + b'`. -/
def rReg (b' : ℕ) : Fin 200 := ⟨42 + b' % 14, by omega⟩

/-- One bit of `j`: pop it into `148`; if set, `term := σ_{g_t}(term)`. -/
def autBitC (t : ℕ) : RingVM.Code := .seq (.mv 148 147 1) (.ifb 148 (.aut 146 146 (kReg t)) .nop)

/-- The bits `t < n` of `j`. -/
def autBitsN : ℕ → RingVM.Code
  | 0 => .nop
  | n + 1 => .seq (autBitsN n) (autBitC n)

/-- One bit of the entry: pop it into `148`; if set, `term := X^{2^{b'}} term`. -/
def rhoBitC (b' : ℕ) : RingVM.Code := .seq (.mv 148 149 1) (.ifb 148 (.rhoJ 146 146 (rReg b')) .nop)

/-- The bits `b' < n` of the entry. -/
def rhoBitsN : ℕ → RingVM.Code
  | 0 => .nop
  | n + 1 => .seq (rhoBitsN n) (rhoBitC n)

/-- A round of a transition table (entries of `14` bits). -/
def uBodyA : RingVM.Code :=
  ofList [.cp 146 145, .cp 147 140, autBitsN 22, .cp 149 14, .mv 149 141 14, rhoBitsN 14,
    .add 144 144 146, .rhoJ 145 145 1]

/-- A round of the output table (entries of one bit). -/
def uBodyV : RingVM.Code :=
  ofList [.cp 146 145, .cp 147 140, autBitsN 22, .mv 148 141 1, .ifb 148 .nop (.cp 146 2),
    .add 144 144 146, .rhoJ 145 145 1]

/-- **The coefficient of index `j`** (`last`: the output table). -/
def coefC (last : Bool) : RingVM.Code :=
  ofList [.cp 144 2, .cp 145 3, .cp 148 1, .cp 150 12, .rep 150 (if last then uBodyV else uBodyA),
    .rotB 142 144 13]

/-! ### Ring values -/

variable {N K : ℕ} [NeZero (2 ^ K - 1)]

/-- `σ` along the set bits `t < n` of the word `J` (the automorphism of index `κ t`). -/
noncomputable def autBitsR (κ : ℕ → ℕ) (J : List Bool) (a : RM N K) : ℕ → RM N K
  | 0 => a
  | n + 1 => if J.getD n false then aut N (κ n) (autBitsR κ J a n) else autBitsR κ J a n

/-- `X^{−ρ b'}` along the set bits `b' < n` of the word `E`. -/
noncomputable def rhoBitsR (ρ : ℕ → ℕ) (E : List Bool) (a : RM N K) : ℕ → RM N K
  | 0 => a
  | n + 1 => if E.getD n false then xInvG _ N ^ ρ n * rhoBitsR ρ E a n else rhoBitsR ρ E a n

/-- The constants the coefficient block reads. -/
structure CK (N K W bb : ℕ) (κ ρ : ℕ → ℕ) (w : St) : Prop where
  c : Consts N K w
  one : w 3 = true :: List.replicate (N * K - 1) false
  km1 : w 5 = List.replicate (K - 1) false
  mat : w 7 = List.replicate (4 * K * (N * K)) false
  tw : w 12 = List.replicate W false
  tb : w 13 = List.replicate bb false
  t14 : w 14 = List.replicate 14 false
  vk : w 56 = List.replicate (K * (N * K)) false
  kap : ∀ t < 22, w (kReg t) = List.replicate (κ t) false
  rho : ∀ b' < 14, w (rReg b') = List.replicate (ρ b') false

/-- The registers of the constants are below `140`. -/
theorem ck_of_agree {W bb : ℕ} {κ ρ : ℕ → ℕ} {w w' : St} (h : CK N K W bb κ ρ w)
    (hw : ∀ j : Fin 200, j.val < 140 → w' j = w j) : CK N K W bb κ ρ w' where
  c := consts_of_agree h.c fun j hj => hw j (by omega)
  one := by rw [hw 3 (by decide)]; exact h.one
  km1 := by rw [hw 5 (by decide)]; exact h.km1
  mat := by rw [hw 7 (by decide)]; exact h.mat
  tw := by rw [hw 12 (by decide)]; exact h.tw
  tb := by rw [hw 13 (by decide)]; exact h.tb
  t14 := by rw [hw 14 (by decide)]; exact h.t14
  vk := by rw [hw 56 (by decide)]; exact h.vk
  kap t ht := by rw [hw _ (by simp [kReg]; omega)]; exact h.kap t ht
  rho b' hb := by rw [hw _ (by simp [rReg]; omega)]; exact h.rho b' hb

theorem ck_exec {W bb : ℕ} {κ ρ : ℕ → ℕ} {w : St} (h : CK N K W bb κ ρ w) (c : RingVM.Code)
    (hwr : (wr c).all (fun x => decide (140 ≤ x.val)) = true) :
    CK N K W bb κ ρ (exec N K c w) :=
  ck_of_agree h fun j hj => exec_not_mem c w j fun hm => by
    have := List.all_eq_true.mp hwr j hm; simp at this; omega

/-! ### The bits of `j` -/

theorem wr_autBitsN : ∀ n, wr (autBitsN n) = (List.range n).flatMap fun _ => [148, 147, 146]
  | 0 => rfl
  | n + 1 => by
    rw [autBitsN, wr, wr_autBitsN n, List.range_succ, List.flatMap_append]
    rfl

theorem mem_wr_autBitsN {n : ℕ} {j : Fin 200} (h : j ∈ wr (autBitsN n)) :
    j = 148 ∨ j = 147 ∨ j = 146 := by
  rw [wr_autBitsN] at h
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨_, _, h⟩ := h
  exact h

/-- **The bits of `j`**: after `n ≤ |J|` rounds from `147 = J`, `146` reads as `autBitsR`. -/
theorem exec_autBitsN (hN : 0 < N) {κ : ℕ → ℕ} (w : St) (J : List Bool)
    (hk : ∀ t < 22, w (kReg t) = List.replicate (κ t) false) (hκ : ∀ t < 22, 0 < κ t)
    (h1 : w 1 = [false]) (h147 : w 147 = J) (h148 : (w 148).length = 1)
    (h146 : (w 146).length = N * K) :
    ∀ n ≤ min J.length 22, (exec N K (autBitsN n) w) 147 = J.drop n ∧
      ((exec N K (autBitsN n) w) 148).length = 1 ∧
      ((exec N K (autBitsN n) w) 146).length = N * K ∧
      decRM N K ((exec N K (autBitsN n) w) 146) = autBitsR κ J (decRM N K (w 146)) n ∧
      ∀ j, j ≠ 146 → j ≠ 147 → j ≠ 148 → (exec N K (autBitsN n) w) j = w j
  | 0, _ => ⟨by simp [autBitsN, exec, h147], h148, h146, rfl, fun _ _ _ _ => rfl⟩
  | n + 1, hn => by
    obtain ⟨a147, a148, a146, ad, af⟩ := exec_autBitsN hN w J hk hκ h1 h147 h148 h146 n (by omega)
    set w' := exec N K (autBitsN n) w with hw'
    have hn' : n < J.length := by omega
    have hJ : J.drop n = J.getD n false :: J.drop (n + 1) := by
      rw [List.drop_eq_getElem_cons hn', List.getD_eq_getElem _ _ hn']
    have hw1 : w' 1 = [false] := by rw [af 1 (by decide) (by decide) (by decide)]; exact h1
    have hkt : w' (kReg n) = List.replicate (κ n) false := by
      rw [af _ (by simp [kReg, Fin.ext_iff]; omega) (by simp [kReg, Fin.ext_iff]; omega)
        (by simp [kReg, Fin.ext_iff]; omega)]
      exact hk n (by omega)
    have e : exec N K (autBitsN (n + 1)) w = exec N K (.ifb 148 (.aut 146 146 (kReg n)) .nop)
        (Function.update (Function.update w' 147 (J.drop (n + 1))) 148 [J.getD n false]) := by
      show exec N K (.ifb 148 (.aut 146 146 (kReg n)) .nop) (exec N K (.mv 148 147 1) w') = _
      rw [exec_mv_pop (v := [J.getD n false]) (by decide) (by rw [a148, hw1]; rfl) (by rw [hw1]; rfl)
        (by rw [a147, hJ]; rfl)]
    rw [e]
    set S := Function.update (Function.update w' 147 (J.drop (n + 1))) 148 [J.getD n false] with hS
    have hS148 : hd (S 148) = J.getD n false := by simp [hS, hd]
    have hkS : S (kReg n) = List.replicate (κ n) false := by
      rw [hS, Function.update_of_ne (by simp [kReg, Fin.ext_iff]; omega),
        Function.update_of_ne (by simp [kReg, Fin.ext_iff]; omega), hkt]
    have h146S : S 146 = w' 146 := by simp [hS]
    by_cases hb : J.getD n false = true
    · rw [show exec N K (.ifb 148 (.aut 146 146 (kReg n)) .nop) S =
          exec N K (.aut 146 146 (kReg n)) S from if_pos (by rw [hS148, hb])]
      simp only [exec, hkS, h146S, List.length_replicate, opd_eq a146]
      refine ⟨by simp [hS], by simp [hS], by simp [length_autMW _ _ _ _ hN], ?_,
        fun j h6 h7 h8 => ?_⟩
      · rw [Function.update_self, decRM_autMW (hκ n (by omega)) a146, ad, autBitsR, if_pos hb]
      · simp [hS, h6, h7, h8, af j h6 h7 h8]
    · rw [show exec N K (.ifb 148 (.aut 146 146 (kReg n)) .nop) S = exec N K .nop S from
          if_neg (by rw [hS148]; exact hb)]
      refine ⟨by simp [exec, hS], by simp [exec, hS], by simp [exec, h146S, a146], ?_,
        fun j h6 h7 h8 => ?_⟩
      · simp only [exec, h146S]; rw [ad, autBitsR, if_neg hb]
      · simp [exec, hS, h7, h8, af j h6 h7 h8]

/-! ### The bits of an entry -/

theorem length_rhoMW_iter (K : ℕ) (e : List Bool) : ∀ j, ((rhoMW K)^[j] e).length = e.length
  | 0 => rfl
  | j + 1 => by rw [Function.iterate_succ_apply', length_rhoMW, length_rhoMW_iter K e j]

/-- **The bits of an entry**: after `n ≤ |E|` rounds from `149 = E`, `146` reads as `rhoBitsR`. -/
theorem exec_rhoBitsN (hN : 0 < N) {ρ : ℕ → ℕ} (w : St) (E : List Bool)
    (hr : ∀ b' < 14, w (rReg b') = List.replicate (ρ b') false)
    (h1 : w 1 = [false]) (h149 : w 149 = E) (h148 : (w 148).length = 1)
    (h146 : (w 146).length = N * K) :
    ∀ n ≤ min E.length 14, (exec N K (rhoBitsN n) w) 149 = E.drop n ∧
      ((exec N K (rhoBitsN n) w) 148).length = 1 ∧
      ((exec N K (rhoBitsN n) w) 146).length = N * K ∧
      decRM N K ((exec N K (rhoBitsN n) w) 146) = rhoBitsR ρ E (decRM N K (w 146)) n ∧
      ∀ j, j ≠ 146 → j ≠ 149 → j ≠ 148 → (exec N K (rhoBitsN n) w) j = w j
  | 0, _ => ⟨by simp [rhoBitsN, exec, h149], h148, h146, rfl, fun _ _ _ _ => rfl⟩
  | n + 1, hn => by
    obtain ⟨a149, a148, a146, ad, af⟩ := exec_rhoBitsN hN w E hr h1 h149 h148 h146 n (by omega)
    set w' := exec N K (rhoBitsN n) w with hw'
    have hn' : n < E.length := by omega
    have hE : E.drop n = E.getD n false :: E.drop (n + 1) := by
      rw [List.drop_eq_getElem_cons hn', List.getD_eq_getElem _ _ hn']
    have hw1 : w' 1 = [false] := by rw [af 1 (by decide) (by decide) (by decide)]; exact h1
    have hrt : w' (rReg n) = List.replicate (ρ n) false := by
      rw [af _ (by simp [rReg, Fin.ext_iff]; omega) (by simp [rReg, Fin.ext_iff]; omega)
        (by simp [rReg, Fin.ext_iff]; omega)]
      exact hr n (by omega)
    have e : exec N K (rhoBitsN (n + 1)) w = exec N K (.ifb 148 (.rhoJ 146 146 (rReg n)) .nop)
        (Function.update (Function.update w' 149 (E.drop (n + 1))) 148 [E.getD n false]) := by
      show exec N K (.ifb 148 (.rhoJ 146 146 (rReg n)) .nop) (exec N K (.mv 148 149 1) w') = _
      rw [exec_mv_pop (v := [E.getD n false]) (by decide) (by rw [a148, hw1]; rfl) (by rw [hw1]; rfl)
        (by rw [a149, hE]; rfl)]
    rw [e]
    set S := Function.update (Function.update w' 149 (E.drop (n + 1))) 148 [E.getD n false] with hS
    have hS148 : hd (S 148) = E.getD n false := by simp [hS, hd]
    have hrS : S (rReg n) = List.replicate (ρ n) false := by
      rw [hS, Function.update_of_ne (by simp [rReg, Fin.ext_iff]; omega),
        Function.update_of_ne (by simp [rReg, Fin.ext_iff]; omega), hrt]
    have h146S : S 146 = w' 146 := by simp [hS]
    by_cases hb : E.getD n false = true
    · rw [show exec N K (.ifb 148 (.rhoJ 146 146 (rReg n)) .nop) S =
          exec N K (.rhoJ 146 146 (rReg n)) S from if_pos (by rw [hS148, hb])]
      simp only [exec, hrS, h146S, List.length_replicate, opd_eq a146]
      refine ⟨by simp [hS], by simp [hS], by simp [length_rhoMW_iter, a146], ?_,
        fun j h6 h7 h8 => ?_⟩
      · rw [Function.update_self, decRM_rhoMW_iter_mul hN a146, ad, rhoBitsR, if_pos hb]
      · simp [hS, h6, h7, h8, af j h6 h7 h8]
    · rw [show exec N K (.ifb 148 (.rhoJ 146 146 (rReg n)) .nop) S = exec N K .nop S from
          if_neg (by rw [hS148]; exact hb)]
      refine ⟨by simp [exec, hS], by simp [exec, hS], by simp [exec, h146S, a146], ?_,
        fun j h6 h7 h8 => ?_⟩
      · simp only [exec, h146S]; rw [ad, rhoBitsR, if_neg hb]
      · simp [exec, hS, h7, h8, af j h6 h7 h8]

/-! ### One round -/

/-- The registers a round writes. -/
def rndW : List (Fin 200) := [141, 144, 145, 146, 147, 148, 149]

theorem kReg_ne {t : ℕ} {j : Fin 200} (h : 140 ≤ j.val) : kReg t ≠ j := by
  intro e; subst e; simp [kReg] at h; omega

theorem rReg_ne {t : ℕ} {j : Fin 200} (h : 140 ≤ j.val) : rReg t ≠ j := by
  intro e; subst e; simp [rReg] at h; omega

/-- **A round of a transition table.** -/
theorem exec_uBodyA (hN : 0 < N) {κ ρ : ℕ → ℕ} (w : St)
    (hk : ∀ t < 22, w (kReg t) = List.replicate (κ t) false) (hκ : ∀ t < 22, 0 < κ t)
    (hr : ∀ b' < 14, w (rReg b') = List.replicate (ρ b') false)
    (h1 : w 1 = [false]) (h14 : w 14 = List.replicate 14 false) (hJ : (w 140).length = 22)
    {E rest : List Bool} (hE : E.length = 14) (h141 : w 141 = E ++ rest)
    (h144 : (w 144).length = N * K) (h145 : (w 145).length = N * K) (h148 : (w 148).length = 1) :
    (exec N K uBodyA w) 141 = rest ∧ ((exec N K uBodyA w) 148).length = 1 ∧
      (exec N K uBodyA w) 145 = rhoMW K (w 145) ∧ ((exec N K uBodyA w) 144).length = N * K ∧
      decRM N K ((exec N K uBodyA w) 144) = decRM N K (w 144) +
        rhoBitsR ρ E (autBitsR κ (w 140) (decRM N K (w 145)) 22) 14 ∧
      ∀ j, j ∉ rndW → (exec N K uBodyA w) j = w j := by
  set s2 := Function.update (Function.update w 146 (w 145)) 147 (w 140) with hs2
  obtain ⟨a147, a148, a146, ad, af⟩ := exec_autBitsN (N := N) (K := K) hN (κ := κ) s2 (w 140)
    (fun t ht => by rw [hs2, Function.update_of_ne (kReg_ne (by decide)),
      Function.update_of_ne (kReg_ne (by decide))]; exact hk t ht) hκ
    (by simp [hs2, h1]) (by simp [hs2]) (by simp [hs2, h148]) (by simp [hs2, h145]) 22
    (by rw [hJ]; simp)
  set s3 := exec N K (autBitsN 22) s2 with hs3
  have h3_1 : s3 1 = [false] := by rw [af 1 (by decide) (by decide) (by decide)]; simp [hs2, h1]
  have h3_14 : s3 14 = List.replicate 14 false := by
    rw [af 14 (by decide) (by decide) (by decide)]; simp [hs2, h14]
  have h3_141 : s3 141 = E ++ rest := by
    rw [af 141 (by decide) (by decide) (by decide)]; simp [hs2, h141]
  set s4 := Function.update s3 149 (List.replicate 14 false) with hs4
  have e5 : exec N K (.mv 149 141 14) s4 = Function.update (Function.update s4 141 rest) 149 E :=
    exec_mv_pop (by decide) (by simp [hs4, h3_14]) (by simp [hs4, h3_14, hE]) (by simp [hs4, h3_141])
  set s5 := Function.update (Function.update s4 141 rest) 149 E with hs5
  obtain ⟨b149, b148, b146, bd, bf⟩ := exec_rhoBitsN (N := N) (K := K) hN (ρ := ρ) s5 E
    (fun b' hb' => by
      rw [hs5, Function.update_of_ne (rReg_ne (by decide)), Function.update_of_ne (rReg_ne (by decide)),
        hs4, Function.update_of_ne (rReg_ne (by decide)), af _ (rReg_ne (by decide)).symm.symm
          (rReg_ne (by decide)) (rReg_ne (by decide)), hs2, Function.update_of_ne (rReg_ne (by decide)),
        Function.update_of_ne (rReg_ne (by decide))]
      exact hr b' hb')
    (by simp [hs5, hs4, h3_1]) (by simp [hs5]) (by simp [hs5, hs4, a148]) (by simp [hs5, hs4, a146])
    14 (by rw [hE]; simp)
  set s6 := exec N K (rhoBitsN 14) s5 with hs6
  have h6_144 : s6 144 = w 144 := by
    rw [bf 144 (by decide) (by decide) (by decide)]
    simp [hs5, hs4, af 144 (by decide) (by decide) (by decide), hs2]
  have h6_145 : s6 145 = w 145 := by
    rw [bf 145 (by decide) (by decide) (by decide)]
    simp [hs5, hs4, af 145 (by decide) (by decide) (by decide), hs2]
  have h6_1 : s6 1 = [false] := by
    rw [bf 1 (by decide) (by decide) (by decide)]; simp [hs5, hs4, h3_1]
  have h6_141 : s6 141 = rest := by
    rw [bf 141 (by decide) (by decide) (by decide)]; simp [hs5]
  have e : exec N K uBodyA w = Function.update (Function.update s6 144
      (addRMW N K (w 144) (s6 146))) 145 ((rhoMW K)^[1] (w 145)) := by
    simp only [uBodyA, exec_ofList_cons, exec_ofList_nil]
    rw [show exec N K (.cp 147 140) (exec N K (.cp 146 145) w) = s2 from rfl, ← hs3,
      show exec N K (.cp 149 14) s3 = s4 by simp [exec, hs4, h3_14], e5, ← hs6]
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, h6_144, h6_145, h6_1,
      opd_eq h144, opd_eq b146, opd_eq h145, List.length_singleton]
  have hdec : decRM N K (s6 146) =
      rhoBitsR ρ E (autBitsR κ (w 140) (decRM N K (w 145)) 22) 14 := by
    have h5 : s5 146 = s3 146 := by simp only [hs5, hs4, Function.update_apply, Fin.reduceEq, ↓reduceIte]
    have h2 : s2 146 = w 145 := by simp [hs2]
    rw [bd, h5, ad, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [e]; simp [h6_141]
  · rw [e]; simp [b148]
  · rw [e]; simp
  · rw [e]; simp [length_addRMW N K h144]
  · rw [e]; simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, Function.update_self]
    rw [decRM_addRMW h144 b146, hdec]
  · have h1 : j ≠ 141 ∧ j ≠ 144 ∧ j ≠ 145 ∧ j ≠ 146 ∧ j ≠ 147 ∧ j ≠ 148 ∧ j ≠ 149 := by
      simp only [rndW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj; exact hj
    obtain ⟨n1, n4, n5, n6, n7, n8, n9⟩ := h1
    rw [e, Function.update_of_ne n5, Function.update_of_ne n4, bf j n6 n9 n8]
    simp only [hs5, hs4, Function.update_of_ne n9, Function.update_of_ne n1]
    rw [af j n6 n7 n8]
    simp [hs2, n6, n7]

/-- **A round of the output table.** -/
theorem exec_uBodyV (hN : 0 < N) {κ : ℕ → ℕ} (w : St)
    (hk : ∀ t < 22, w (kReg t) = List.replicate (κ t) false) (hκ : ∀ t < 22, 0 < κ t)
    (h1 : w 1 = [false]) (h2 : w 2 = List.replicate (N * K) false) (hJ : (w 140).length = 22)
    {e : Bool} {rest : List Bool} (h141 : w 141 = e :: rest)
    (h144 : (w 144).length = N * K) (h145 : (w 145).length = N * K) (h148 : (w 148).length = 1) :
    (exec N K uBodyV w) 141 = rest ∧ ((exec N K uBodyV w) 148).length = 1 ∧
      (exec N K uBodyV w) 145 = rhoMW K (w 145) ∧ ((exec N K uBodyV w) 144).length = N * K ∧
      decRM N K ((exec N K uBodyV w) 144) = decRM N K (w 144) +
        (if e then autBitsR κ (w 140) (decRM N K (w 145)) 22 else 0) ∧
      ∀ j, j ∉ rndW → (exec N K uBodyV w) j = w j := by
  set s2 := Function.update (Function.update w 146 (w 145)) 147 (w 140) with hs2
  obtain ⟨a147, a148, a146, ad, af⟩ := exec_autBitsN (N := N) (K := K) hN (κ := κ) s2 (w 140)
    (fun t ht => by rw [hs2, Function.update_of_ne (kReg_ne (by decide)),
      Function.update_of_ne (kReg_ne (by decide))]; exact hk t ht) hκ
    (by simp [hs2, h1]) (by simp [hs2]) (by simp [hs2, h148]) (by simp [hs2, h145]) 22
    (by rw [hJ]; simp)
  set s3 := exec N K (autBitsN 22) s2 with hs3
  have h3_1 : s3 1 = [false] := by rw [af 1 (by decide) (by decide) (by decide)]; simp [hs2, h1]
  have h3_2 : s3 2 = List.replicate (N * K) false := by
    rw [af 2 (by decide) (by decide) (by decide)]; simp [hs2, h2]
  have h3_141 : s3 141 = [e] ++ rest := by
    rw [af 141 (by decide) (by decide) (by decide)]; simp [hs2, h141]
  have e4 : exec N K (.mv 148 141 1) s3 = Function.update (Function.update s3 141 rest) 148 [e] :=
    exec_mv_pop (by decide) (by rw [a148, h3_1]; rfl) (by rw [h3_1]; rfl) h3_141
  set s4 := Function.update (Function.update s3 141 rest) 148 [e] with hs4
  have hS148 : hd (s4 148) = e := by simp [hs4, hd]
  set t := if e then s3 146 else List.replicate (N * K) false with ht
  have e5 : exec N K (.ifb 148 .nop (.cp 146 2)) s4 = Function.update s4 146 t := by
    by_cases he : e = true
    · rw [show exec N K (.ifb 148 .nop (.cp 146 2)) s4 = exec N K .nop s4 from
        if_pos (by rw [hS148, he])]
      simp [exec, ht, he, hs4]
    · rw [show exec N K (.ifb 148 .nop (.cp 146 2)) s4 = exec N K (.cp 146 2) s4 from
        if_neg (by rw [hS148]; exact he)]
      simp [exec, ht, he, hs4, h3_2]
  have h4_144 : s3 144 = w 144 := by rw [af 144 (by decide) (by decide) (by decide)]; simp [hs2]
  have h4_145 : s3 145 = w 145 := by rw [af 145 (by decide) (by decide) (by decide)]; simp [hs2]
  have htl : t.length = N * K := by rw [ht]; split_ifs <;> simp [a146]
  have eE : exec N K uBodyV w = Function.update (Function.update (Function.update s4 146 t) 144
      (addRMW N K (w 144) t)) 145 ((rhoMW K)^[1] (w 145)) := by
    simp only [uBodyV, exec_ofList_cons, exec_ofList_nil]
    rw [show exec N K (.cp 147 140) (exec N K (.cp 146 145) w) = s2 from rfl, ← hs3, e4, e5]
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, hs4, h4_144, h4_145, h3_1,
      opd_eq h144, opd_eq htl, opd_eq h145, List.length_singleton]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [eE]; simp [hs4]
  · rw [eE]; simp [hs4]
  · rw [eE]; simp
  · rw [eE]; simp [length_addRMW N K h144]
  · rw [eE]; simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte]
    have h2' : s2 146 = w 145 := by simp [hs2]
    have hdt : decRM N K t = (if e then autBitsR κ (w 140) (decRM N K (w 145)) 22 else 0) := by
      rw [ht]
      by_cases he : e = true
      · rw [if_pos he, if_pos he, ad, h2']
      · rw [if_neg he, if_neg he]; exact decRM_replicate N K
    rw [decRM_addRMW h144 htl, hdt]
  · have h1 : j ≠ 141 ∧ j ≠ 144 ∧ j ≠ 145 ∧ j ≠ 146 ∧ j ≠ 147 ∧ j ≠ 148 ∧ j ≠ 149 := by
      simp only [rndW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj; exact hj
    obtain ⟨n1, n4, n5, n6, n7, n8, n9⟩ := h1
    rw [eE, Function.update_of_ne n5, Function.update_of_ne n4, Function.update_of_ne n6, hs4,
      Function.update_of_ne n8, Function.update_of_ne n1, af j n6 n7 n8]
    simp [hs2, n6, n7]

/-! ### The coefficient -/

theorem mem_wr_rhoBitsN {n : ℕ} {j : Fin 200} (h : j ∈ wr (rhoBitsN n)) :
    j = 148 ∨ j = 149 ∨ j = 146 := by
  induction n with
  | zero => simp [rhoBitsN, wr] at h
  | succ n ih =>
    have e : wr (rhoBitsN (n + 1)) = wr (rhoBitsN n) ++ [148, 149, 146] := rfl
    rw [e, List.mem_append] at h
    rcases h with h | h
    · exact ih h
    · simpa using h

theorem not_mem_rndW {j : Fin 200} (hj : j.val ≤ 140) : j ∉ rndW := by
  intro h
  simp only [rndW, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h <;> subst h <;> simp at hj

theorem wr_uBodyA_mem {j : Fin 200} (h : j ∈ wr uBodyA) : j ∈ rndW := by
  have e : wr uBodyA = [146, 147] ++ wr (autBitsN 22) ++ [149, 149, 141] ++ wr (rhoBitsN 14) ++
      [144, 145] := rfl
  rw [e] at h
  simp only [List.mem_append] at h
  simp only [rndW, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with (((h | h) | h) | h) | h
  · simp at h; tauto
  · rcases mem_wr_autBitsN h with h | h | h <;> simp [h]
  · simp at h; tauto
  · rcases mem_wr_rhoBitsN h with h | h | h <;> simp [h]
  · simp at h; tauto

theorem wr_uBodyV_mem {j : Fin 200} (h : j ∈ wr uBodyV) : j ∈ rndW := by
  have e : wr uBodyV = [146, 147] ++ wr (autBitsN 22) ++ [148, 141, 146, 144, 145] := rfl
  rw [e] at h
  simp only [List.mem_append] at h
  simp only [rndW, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with (h | h) | h
  · simp at h; tauto
  · rcases mem_wr_autBitsN h with h | h | h <;> simp [h]
  · simp at h; tauto

/-- The term of round `u` (transition tables). -/
noncomputable def termA (κ ρ : ℕ → ℕ) (J T : List Bool) (u : ℕ) : RM N K :=
  rhoBitsR ρ ((T.drop (14 * u)).take 14) (autBitsR κ J (xInvG _ N ^ u) 22) 14

/-- The term of round `u` (output table). -/
noncomputable def termV (κ : ℕ → ℕ) (J T : List Bool) (u : ℕ) : RM N K :=
  if T.getD u false then autBitsR κ J (xInvG _ N ^ u) 22 else 0

theorem decRM_one_iter (hK : 0 < K) (hN : 0 < N) (u : ℕ) :
    decRM N K ((rhoMW K)^[u] (true :: List.replicate (N * K - 1) false)) = xInvG _ N ^ u := by
  have hl : (true :: List.replicate (N * K - 1) false).length = N * K := by
    have : 0 < N * K := Nat.mul_pos hN hK
    simp; omega
  rw [decRM_rhoMW_iter_mul hN hl, decRM_one hK hN, mul_one]

/-- **The coefficient of a transition table.** -/
theorem exec_coefA (hK : 0 < K) (hN : 0 < N) {κ ρ : ℕ → ℕ} {W bb : ℕ} (w : St)
    (hck : CK N K W bb κ ρ w) (hκ : ∀ t < 22, 0 < κ t) (hbb : bb ≤ K)
    (hJ : (w 140).length = 22) {T : List Bool} (hT : 14 * W ≤ T.length) (h141 : w 141 = T) :
    ((exec N K (coefC false) w) 142).length = N * K ∧
      decRM N K ((exec N K (coefC false) w) 142) =
        (2 : ZMod (2 ^ K - 1)) ^ (K - bb) • ∑ u ∈ Finset.range W, termA κ ρ (w 140) T u ∧
      ∀ j : Fin 200, j.val ≤ 140 → (exec N K (coefC false) w) j = w j := by
  have hone : (true :: List.replicate (N * K - 1) false).length = N * K := by
    have : 0 < N * K := Nat.mul_pos hN hK
    simp; omega
  set w1 := Function.update (Function.update (Function.update (Function.update w 144
    (List.replicate (N * K) false)) 145 (true :: List.replicate (N * K - 1) false)) 148 [false]) 150
    (List.replicate W false) with hw1
  have e1 : exec N K (coefC false) w = exec N K (.rotB 142 144 13) (exec N K (.rep 150 uBodyA) w1) := by
    simp only [coefC, exec_ofList_cons, exec_ofList_nil, Bool.false_eq_true, ite_false]
    congr 2
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, hck.c.zero, hck.one,
      hck.c.one, hck.tw, hw1]
  have h150 : (w1 150).length = W := by simp [hw1]
  let P : ℕ → St → Prop := fun i w' =>
    w' 141 = T.drop (14 * i) ∧ (w' 148).length = 1 ∧
      w' 145 = (rhoMW K)^[i] (true :: List.replicate (N * K - 1) false) ∧
      (w' 144).length = N * K ∧
      decRM N K (w' 144) = ∑ u ∈ Finset.range i, termA κ ρ (w 140) T u ∧
      ∀ j : Fin 200, j.val ≤ 140 → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 150 uBodyA (fun h => by
      have := wr_uBodyA_mem h; simp [rndW] at this) P w1
    ⟨by simp [hw1, h141], by simp [hw1], by simp [hw1], by simp [hw1],
      by simp [hw1, decRM_replicate],
      fun j hj => by
        simp only [hw1]
        rw [Function.update_of_ne (by intro e; subst e; simp at hj),
          Function.update_of_ne (by intro e; subst e; simp at hj),
          Function.update_of_ne (by intro e; subst e; simp at hj),
          Function.update_of_ne (by intro e; subst e; simp at hj)]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨p141, p148, p145, p144, pd, pf⟩ := hw'
      rw [h150] at hi
      set w'' := Function.update w' 150 (w' 150).tail with hw''
      have f'' : ∀ j : Fin 200, j.val ≤ 140 → w'' j = w j := fun j hj => by
        rw [hw'', Function.update_of_ne (by intro e; subst e; simp at hj)]; exact pf j hj
      have hE : T.drop (14 * i) = (T.drop (14 * i)).take 14 ++ T.drop (14 * (i + 1)) := by
        rw [show 14 * (i + 1) = 14 * i + 14 by ring, ← List.drop_drop, List.take_append_drop]
      obtain ⟨b141, b148, b145, b144, bd, bf⟩ := exec_uBodyA (N := N) (K := K) hN (κ := κ)
        (ρ := ρ) w''
        (fun t ht => by rw [f'' _ (by simp [kReg]; omega)]; exact hck.kap t ht) hκ
        (fun b' hb' => by rw [f'' _ (by simp [rReg]; omega)]; exact hck.rho b' hb')
        (by rw [f'' 1 (by decide)]; exact hck.c.one) (by rw [f'' 14 (by decide)]; exact hck.t14)
        (by rw [f'' 140 le_rfl]; exact hJ) (E := (T.drop (14 * i)).take 14)
        (by simp; omega) (by rw [hw'', Function.update_of_ne (by decide), p141]; exact hE)
        (by rw [hw'', Function.update_of_ne (by decide)]; exact p144)
        (by rw [hw'', Function.update_of_ne (by decide), p145, length_rhoMW_iter, hone])
        (by rw [hw'', Function.update_of_ne (by decide)]; exact p148)
      have h140 : w'' 140 = w 140 := f'' 140 le_rfl
      have h145'' : w'' 145 = w' 145 := by rw [hw'', Function.update_of_ne (by decide)]
      have h144'' : w'' 144 = w' 144 := by rw [hw'', Function.update_of_ne (by decide)]
      refine ⟨b141, b148, ?_, b144, ?_, fun j hj => ?_⟩
      · rw [b145, h145'', p145, ← Function.iterate_succ_apply' (rhoMW K)]
      · rw [bd, h144'', pd, h140, h145'', p145, decRM_one_iter hK hN, Finset.sum_range_succ]
        rfl
      · rw [bf j (not_mem_rndW hj)]
        exact f'' j hj)
  rw [h150] at hP
  obtain ⟨_, _, _, q144, qd, qf⟩ := hP
  set w2 := exec N K (.rep 150 uBodyA) w1 with hw2
  have h13 : w2 13 = List.replicate bb false := by rw [qf 13 (by decide)]; exact hck.tb
  have e2 : exec N K (.rotB 142 144 13) w2 = Function.update w2 142 (rotBW N K bb (w2 144)) := by
    simp only [exec, h13, List.length_replicate, opd_eq q144]
  rw [e1, e2]
  refine ⟨by rw [Function.update_self]; exact length_rotBW N K bb q144, ?_, fun j hj => ?_⟩
  · rw [Function.update_self, show rotBW N K bb (w2 144) = rotBW N K (K - (K - bb)) (w2 144) by
      rw [show K - (K - bb) = bb by omega], decRM_rotBW q144 (by omega), qd]
  · rw [Function.update_of_ne (by intro e; subst e; simp at hj), qf j (by omega)]

/-- **The coefficient of the output table.** -/
theorem exec_coefV (hK : 0 < K) (hN : 0 < N) {κ ρ : ℕ → ℕ} {W bb : ℕ} (w : St)
    (hck : CK N K W bb κ ρ w) (hκ : ∀ t < 22, 0 < κ t) (hbb : bb ≤ K)
    (hJ : (w 140).length = 22) {T : List Bool} (hT : W ≤ T.length) (h141 : w 141 = T) :
    ((exec N K (coefC true) w) 142).length = N * K ∧
      decRM N K ((exec N K (coefC true) w) 142) =
        (2 : ZMod (2 ^ K - 1)) ^ (K - bb) • ∑ u ∈ Finset.range W, termV κ (w 140) T u ∧
      ∀ j : Fin 200, j.val ≤ 140 → (exec N K (coefC true) w) j = w j := by
  have hone : (true :: List.replicate (N * K - 1) false).length = N * K := by
    have : 0 < N * K := Nat.mul_pos hN hK
    simp; omega
  set w1 := Function.update (Function.update (Function.update (Function.update w 144
    (List.replicate (N * K) false)) 145 (true :: List.replicate (N * K - 1) false)) 148 [false]) 150
    (List.replicate W false) with hw1
  have e1 : exec N K (coefC true) w = exec N K (.rotB 142 144 13) (exec N K (.rep 150 uBodyV) w1) := by
    simp only [coefC, exec_ofList_cons, exec_ofList_nil, ite_true]
    congr 2
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, hck.c.zero, hck.one,
      hck.c.one, hck.tw, hw1]
  have h150 : (w1 150).length = W := by simp [hw1]
  let P : ℕ → St → Prop := fun i w' =>
    w' 141 = T.drop i ∧ (w' 148).length = 1 ∧
      w' 145 = (rhoMW K)^[i] (true :: List.replicate (N * K - 1) false) ∧
      (w' 144).length = N * K ∧
      decRM N K (w' 144) = ∑ u ∈ Finset.range i, termV κ (w 140) T u ∧
      ∀ j : Fin 200, j.val ≤ 140 → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 150 uBodyV (fun h => by
      have := wr_uBodyV_mem h; simp [rndW] at this) P w1
    ⟨by simp [hw1, h141], by simp [hw1], by simp [hw1], by simp [hw1],
      by simp [hw1, decRM_replicate],
      fun j hj => by
        simp only [hw1]
        rw [Function.update_of_ne (by intro e; subst e; simp at hj),
          Function.update_of_ne (by intro e; subst e; simp at hj),
          Function.update_of_ne (by intro e; subst e; simp at hj),
          Function.update_of_ne (by intro e; subst e; simp at hj)]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨p141, p148, p145, p144, pd, pf⟩ := hw'
      rw [h150] at hi
      set w'' := Function.update w' 150 (w' 150).tail with hw''
      have f'' : ∀ j : Fin 200, j.val ≤ 140 → w'' j = w j := fun j hj => by
        rw [hw'', Function.update_of_ne (by intro e; subst e; simp at hj)]; exact pf j hj
      have hE : T.drop i = T.getD i false :: T.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
      obtain ⟨b141, b148, b145, b144, bd, bf⟩ := exec_uBodyV (N := N) (K := K) hN (κ := κ) w''
        (fun t ht => by rw [f'' _ (by simp [kReg]; omega)]; exact hck.kap t ht) hκ
        (by rw [f'' 1 (by decide)]; exact hck.c.one) (by rw [f'' 2 (by decide)]; exact hck.c.zero)
        (by rw [f'' 140 le_rfl]; exact hJ)
        (by rw [hw'', Function.update_of_ne (by decide), p141]; exact hE)
        (by rw [hw'', Function.update_of_ne (by decide)]; exact p144)
        (by rw [hw'', Function.update_of_ne (by decide), p145, length_rhoMW_iter, hone])
        (by rw [hw'', Function.update_of_ne (by decide)]; exact p148)
      have h140 : w'' 140 = w 140 := f'' 140 le_rfl
      have h145'' : w'' 145 = w' 145 := by rw [hw'', Function.update_of_ne (by decide)]
      have h144'' : w'' 144 = w' 144 := by rw [hw'', Function.update_of_ne (by decide)]
      refine ⟨b141, b148, ?_, b144, ?_, fun j hj => ?_⟩
      · rw [b145, h145'', p145, ← Function.iterate_succ_apply' (rhoMW K)]
      · rw [bd, h144'', pd, h140, h145'', p145, decRM_one_iter hK hN, Finset.sum_range_succ]
        rfl
      · rw [bf j (not_mem_rndW hj)]
        exact f'' j hj)
  rw [h150] at hP
  obtain ⟨_, _, _, q144, qd, qf⟩ := hP
  set w2 := exec N K (.rep 150 uBodyV) w1 with hw2
  have h13 : w2 13 = List.replicate bb false := by rw [qf 13 (by decide)]; exact hck.tb
  have e2 : exec N K (.rotB 142 144 13) w2 = Function.update w2 142 (rotBW N K bb (w2 144)) := by
    simp only [exec, h13, List.length_replicate, opd_eq q144]
  rw [e1, e2]
  refine ⟨by rw [Function.update_self]; exact length_rotBW N K bb q144, ?_, fun j hj => ?_⟩
  · rw [Function.update_self, show rotBW N K bb (w2 144) = rotBW N K (K - (K - bb)) (w2 144) by
      rw [show K - (K - bb) = bb by omega], decRM_rotBW q144 (by omega), qd]
  · rw [Function.update_of_ne (by intro e; subst e; simp at hj), qf j (by omega)]

/-! ### The matrix `α G` -/

/-- One gadget entry: push `p` into the buffer `151`, `p := 2 p`. -/
def gadBody : RingVM.Code := ofList [.cp 154 153, .mv 151 154 2, .rotB 153 153 5]

/-- **The word of `α G`** (`α` on `142`, into `143`). -/
def gadC : RingVM.Code :=
  ofList [.cp 153 142, .cp 151 56, .cp 152 4, .rep 152 gadBody, .cp 143 7,
    .cp 154 151, .mv 143 154 56, .cp 154 56, .mv 143 154 56, .cp 154 56, .mv 143 154 56,
    .cp 154 151, .mv 143 154 56]

/-- The words `2^i α`, `i < K`. -/
def gadWords (N K : ℕ) (a : List Bool) : List (List Bool) :=
  (List.range K).map fun i => (rotBW N K (K - 1))^[i] a

theorem length_rotBW_iter {x : List Bool} (hx : x.length = N * K) :
    ∀ i, ((rotBW N K (K - 1))^[i] x).length = N * K
  | 0 => hx
  | i + 1 => by rw [Function.iterate_succ_apply', length_rotBW N K _ (length_rotBW_iter hx i)]

theorem decRM_rotBW_iter (hK : 0 < K) {x : List Bool} (hx : x.length = N * K) :
    ∀ i, decRM N K ((rotBW N K (K - 1))^[i] x) = (2 : ZMod (2 ^ K - 1)) ^ i • decRM N K x
  | 0 => by simp
  | i + 1 => by
    rw [Function.iterate_succ_apply', decRM_rotBW (length_rotBW_iter hx i) (by omega : 1 ≤ K),
      decRM_rotBW_iter hK hx i, smul_smul, pow_one, ← pow_succ']

theorem gadWords_succ (a : List Bool) (i : ℕ) :
    (List.range (i + 1)).map (fun i => (rotBW N K (K - 1))^[i] a) =
      (List.range i).map (fun i => (rotBW N K (K - 1))^[i] a) ++ [(rotBW N K (K - 1))^[i] a] := by
  rw [List.range_succ, List.map_append]; rfl

theorem push4 {r a b c d : List Bool} {n : ℕ} (hr : r.length = 4 * n) (ha : a.length = n)
    (hb : b.length = n) (hc : c.length = n) (hd : d.length = n) :
    ((((r ++ a).drop n ++ b).drop n ++ c).drop n ++ d).drop n = a ++ b ++ c ++ d := by
  have e1 := drop_append_drop r a b
  rw [ha, hb] at e1
  rw [e1]
  have e2 := drop_append_drop r (a ++ b) c
  rw [List.length_append, ha, hb, hc] at e2
  rw [e2]
  have e3 := drop_append_drop r (a ++ b ++ c) d
  rw [List.length_append, List.length_append, ha, hb, hc, hd] at e3
  rw [e3, List.drop_left' (by rw [hr]; ring)]

theorem exec_cp_mv {d t c src : Fin 200} (h : ¬(d = t ∨ d = c ∨ t = c)) (hdt : d ≠ t) (S : St)
    (hl : (S src).length = (S c).length) :
    exec N K (.mv d t c) (exec N K (.cp t src) S) = Function.update (Function.update
      (Function.update S t (S src)) t []) d ((S d ++ S src).drop (S c).length) := by
  have htc : t ≠ c := fun e => h (Or.inr (Or.inr e))
  show exec N K (.mv d t c) (Function.update S t (S src)) = _
  rw [exec_mv_push h (by rw [Function.update_self, Function.update_of_ne htc.symm]; exact hl)]
  rw [Function.update_of_ne htc.symm, Function.update_of_ne hdt, Function.update_self]

/-- **The word of `α G`**: `(2^i α)_i ++ 0 ++ 0 ++ (2^i α)_i`. -/
theorem exec_gadC (hK : 0 < K) {κ ρ : ℕ → ℕ} {W bb : ℕ} (w : St) (hck : CK N K W bb κ ρ w)
    (h142 : (w 142).length = N * K) :
    (exec N K gadC w) 143 = (gadWords N K (w 142)).flatten ++ List.replicate (K * (N * K)) false ++
      List.replicate (K * (N * K)) false ++ (gadWords N K (w 142)).flatten ∧
      ∀ j : Fin 200, j.val < 143 → (exec N K gadC w) j = w j := by
  set a := w 142 with ha
  set w1 := Function.update (Function.update (Function.update w 153 a) 151
    (List.replicate (K * (N * K)) false)) 152 (List.replicate K false) with hw1
  have hl2 : (w 2).length = N * K := by rw [hck.c.zero]; simp
  let P : ℕ → St → Prop := fun i w' =>
    w' 153 = (rotBW N K (K - 1))^[i] a ∧
      w' 151 = (List.replicate (K * (N * K)) false ++
        ((List.range i).map fun i => (rotBW N K (K - 1))^[i] a).flatten).drop
          (((List.range i).map fun i => (rotBW N K (K - 1))^[i] a).length * (N * K)) ∧
      ∀ j : Fin 200, j.val < 151 → w' j = w j
  have hP := exec_rep_inv (N := N) (K := K) 152 gadBody (by decide) P w1
    ⟨by simp [hw1], by simp [hw1, ha], fun j hj => by
      simp only [hw1]
      rw [Function.update_of_ne (by intro e; subst e; simp at hj),
        Function.update_of_ne (by intro e; subst e; simp at hj),
        Function.update_of_ne (by intro e; subst e; simp at hj)]⟩
    (fun i _ w' hw' _ => by
      obtain ⟨p153, p151, pf⟩ := hw'
      set w'' := Function.update w' 152 (w' 152).tail with hw''
      have hpl : ((rotBW N K (K - 1))^[i] a).length = N * K := length_rotBW_iter h142 i
      have e : exec N K gadBody w'' = Function.update (Function.update (Function.update w'' 154 [])
          151 ((w'' 151 ++ (rotBW N K (K - 1))^[i] a).drop (N * K))) 153
          (rotBW N K (K - 1) ((rotBW N K (K - 1))^[i] a)) := by
        simp only [gadBody, exec_ofList_cons, exec_ofList_nil]
        rw [show exec N K (.cp 154 153) w'' = Function.update w'' 154 (w'' 153) from rfl,
          exec_mv_push (by decide) (by simp [hw'', p153, hpl, pf 2 (by decide), hl2])]
        simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, hw'', p153,
          pf 2 (by decide), hl2, pf 5 (by decide), hck.km1, List.length_replicate, opd_eq hpl,
          Function.update_idem]
      have h5 : w'' 151 = w' 151 := by rw [hw'', Function.update_of_ne (by decide)]
      refine ⟨by rw [e]; simp [Function.iterate_succ_apply'], ?_, fun j hj => ?_⟩
      · rw [e]; simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h5, p151]
        rw [drop_append_flatten_succ hpl (fun y hy => by
          simp only [List.mem_map, List.mem_range] at hy
          obtain ⟨k, _, rfl⟩ := hy; exact length_rotBW_iter h142 k), gadWords_succ]
      · rw [e, Function.update_of_ne (by intro e; subst e; simp at hj),
          Function.update_of_ne (by intro e; subst e; simp at hj),
          Function.update_of_ne (by intro e; subst e; simp at hj), hw'',
          Function.update_of_ne (by intro e; subst e; simp at hj)]
        exact pf j hj)
  have h152 : (w1 152).length = K := by simp [hw1]
  rw [h152] at hP
  obtain ⟨_, q151, qf⟩ := hP
  set w2 := exec N K (.rep 152 gadBody) w1 with hw2
  have hG : ∀ x ∈ gadWords N K a, x.length = N * K := fun x hx => by
    simp only [gadWords, List.mem_map, List.mem_range] at hx
    obtain ⟨k, _, rfl⟩ := hx; exact length_rotBW_iter h142 k
  have hGl : (gadWords N K a).length = K := by simp [gadWords]
  have hPw : w2 151 = (gadWords N K a).flatten := by
    rw [q151]
    exact drop_append_flatten (b := List.replicate (K * (N * K)) false) (vs := gadWords N K a)
      (n := N * K) (by simp [hGl])
  have hPl : (gadWords N K a).flatten.length = K * (N * K) := by
    rw [length_flatten_of hG, hGl]
  have e0 : exec N K (.cp 152 4) (exec N K (.cp 151 56) (exec N K (.cp 153 142) w)) = w1 := by
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, hw1, hck.vk, hck.c.k, ← ha]
  have e1 : exec N K gadC w = exec N K (ofList [.cp 143 7, .cp 154 151, .mv 143 154 56, .cp 154 56,
      .mv 143 154 56, .cp 154 56, .mv 143 154 56, .cp 154 151, .mv 143 154 56]) w2 := by
    simp only [gadC, exec_ofList_cons]
    rw [e0]
  have h56 : w2 56 = List.replicate (K * (N * K)) false := by rw [qf 56 (by decide)]; exact hck.vk
  have h7 : w2 7 = List.replicate (4 * K * (N * K)) false := by rw [qf 7 (by decide)]; exact hck.mat
  rw [e1]
  simp only [exec_ofList_cons, exec_ofList_nil]
  rw [show exec N K (.cp 143 7) w2 = Function.update w2 143 (w2 7) from rfl]
  simp (disch := first | decide | simp [Function.update_apply, hPw, hPl, h56]) only [exec_cp_mv]
  · refine ⟨?_, fun j hj => ?_⟩
    · simp only [Function.update_apply, Fin.reduceEq, ↓reduceIte, h56, h7, hPw,
        List.length_replicate]
      rw [push4 (n := K * (N * K)) (by simp; ring) hPl (by simp) (by simp) hPl]
    · have n3 : j ≠ 143 := by intro e; subst e; simp at hj
      have n4 : j ≠ 154 := by intro e; subst e; simp at hj
      simp only [Function.update_apply, n3, n4, ↓reduceIte]
      rw [qf j (by omega)]

/-! ### Incrementing `j` -/

/-- Increment with a carry, least significant bit first. -/
def incW : Bool → List Bool → List Bool
  | _, [] => []
  | c, x :: xs => xor x c :: incW (x && c) xs

theorem length_incW : ∀ (c : Bool) (J : List Bool), (incW c J).length = J.length
  | _, [] => rfl
  | c, x :: xs => by simp [incW, length_incW _ xs]

/-- **Incrementing binary words**. -/
theorem incW_toBits : ∀ (k n : ℕ) (c : Bool), incW c (toBits k n) = toBits k (n + c.toNat)
  | 0, _, _ => rfl
  | k + 1, n, c => by
    rw [toBits, toBits, incW, incW_toBits k (n / 2)]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> cases c <;> simp [h, Nat.add_mod]
    · congr 1
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> cases c <;> simp [h] <;> omega

/-- One step of the increment: (carry, output). -/
def incStep (a : Bool × List Bool) (x : Bool) : Bool × List Bool := (x && a.1, a.2 ++ [xor x a.1])

theorem foldl_incStep : ∀ (J : List Bool) (c : Bool) (out : List Bool),
    (J.foldl incStep (c, out)).2 = out ++ incW c J
  | [], _, _ => by simp [incW]
  | x :: xs, c, out => by
    rw [List.foldl_cons, incStep, foldl_incStep xs, incW, List.append_assoc]; rfl

/-- One bit: pop it, write `x xor c`, carry `x and c`. -/
def incBody : RingVM.Code :=
  ofList [.mv 148 159 1, .ifb 156 (.ifb 148 (.seq (.cp 157 1) (.mv 155 157 1))
    (ofList [.cp 157 158, .mv 155 157 1, .cp 156 1])) (.seq (.cp 157 148) (.mv 155 157 1))]

/-- **`j := j + 1`** on register `140`. -/
def incC : RingVM.Code :=
  ofList [.cp 159 140, .cp 155 140, .cp 148 1, .cp 158 1, .cp 154 3, .mv 158 154 1, .cp 156 158,
    .cp 152 140, .rep 152 incBody, .cp 140 155]

theorem exec_incBody (w : St) (h1 : w 1 = [false]) (h158 : w 158 = [true]) {x : Bool}
    {rest : List Bool} (h159 : w 159 = x :: rest) {c : Bool} (h156 : w 156 = [c])
    (h148 : (w 148).length = 1) :
    (exec N K incBody w) 159 = rest ∧ (exec N K incBody w) 156 = [x && c] ∧
      ((exec N K incBody w) 148).length = 1 ∧
      (exec N K incBody w) 155 = (w 155 ++ [xor x c]).drop 1 ∧
      ∀ j, j ≠ 148 → j ≠ 155 → j ≠ 156 → j ≠ 157 → j ≠ 159 → (exec N K incBody w) j = w j := by
  have e1 : exec N K (.mv 148 159 1) w = Function.update (Function.update w 159 rest) 148 [x] :=
    exec_mv_pop (by decide) (by rw [h148, h1]; rfl) (by rw [h1]; rfl) (by rw [h159]; rfl)
  set S := Function.update (Function.update w 159 rest) 148 [x] with hS
  have hS156 : hd (S 156) = c := by simp [hS, h156, hd]
  have hS148 : hd (S 148) = x := by simp [hS, hd]
  have ee : exec N K incBody w = exec N K (.ifb 156 (.ifb 148 (.seq (.cp 157 1) (.mv 155 157 1))
      (ofList [.cp 157 158, .mv 155 157 1, .cp 156 1])) (.seq (.cp 157 148) (.mv 155 157 1))) S := by
    simp only [incBody, exec_ofList_cons, exec_ofList_nil]; rw [e1]
  rw [ee]
  have push : ∀ (T : St) (v : List Bool), T 157 = v → v.length = 1 → T 1 = [false] →
      exec N K (.mv 155 157 1) T = Function.update (Function.update T 157 []) 155
        ((T 155 ++ v).drop 1) := fun T v h hv h1' => by
    rw [exec_mv_push (by decide) (by rw [h, hv, h1']; rfl), h, h1']; rfl
  cases c <;> cases x
  · rw [show exec N K (.ifb 156 _ _) S = exec N K (.seq (.cp 157 148) (.mv 155 157 1)) S from
      if_neg (by rw [hS156]; decide)]
    rw [show exec N K (.seq (.cp 157 148) (.mv 155 157 1)) S =
      exec N K (.mv 155 157 1) (Function.update S 157 (S 148)) from rfl]
    rw [push _ [false] (by simp [hS]) rfl (by simp [hS, h1])]
    refine ⟨by simp [hS], by simp [hS, h156], by simp [hS], by simp [hS], fun j a b c d e => ?_⟩
    simp [hS, Function.update_apply, a, b, c, d, e]
  · rw [show exec N K (.ifb 156 _ _) S = exec N K (.seq (.cp 157 148) (.mv 155 157 1)) S from
      if_neg (by rw [hS156]; decide)]
    rw [show exec N K (.seq (.cp 157 148) (.mv 155 157 1)) S =
      exec N K (.mv 155 157 1) (Function.update S 157 (S 148)) from rfl]
    rw [push _ [true] (by simp [hS]) rfl (by simp [hS, h1])]
    refine ⟨by simp [hS], by simp [hS, h156], by simp [hS], by simp [hS], fun j a b c d e => ?_⟩
    simp [hS, Function.update_apply, a, b, c, d, e]
  · rw [show exec N K (.ifb 156 _ _) S = exec N K (.ifb 148 (.seq (.cp 157 1) (.mv 155 157 1))
        (ofList [.cp 157 158, .mv 155 157 1, .cp 156 1])) S from if_pos (by rw [hS156])]
    rw [show exec N K (.ifb 148 _ _) S = exec N K (ofList [.cp 157 158, .mv 155 157 1, .cp 156 1]) S
      from if_neg (by rw [hS148]; decide)]
    simp only [exec_ofList_cons, exec_ofList_nil]
    rw [show exec N K (.cp 157 158) S = Function.update S 157 (S 158) from rfl,
      push _ [true] (by simp [hS, h158]) rfl (by simp [hS, h1])]
    simp only [exec]
    refine ⟨by simp [hS], by simp [hS, h1], by simp [hS], by simp [hS], fun j a b c d e => ?_⟩
    simp [hS, Function.update_apply, a, b, c, d, e]
  · rw [show exec N K (.ifb 156 _ _) S = exec N K (.ifb 148 (.seq (.cp 157 1) (.mv 155 157 1))
        (ofList [.cp 157 158, .mv 155 157 1, .cp 156 1])) S from if_pos (by rw [hS156])]
    rw [show exec N K (.ifb 148 _ _) S = exec N K (.seq (.cp 157 1) (.mv 155 157 1)) S
      from if_pos (by rw [hS148])]
    rw [show exec N K (.seq (.cp 157 1) (.mv 155 157 1)) S =
      exec N K (.mv 155 157 1) (Function.update S 157 (S 1)) from rfl]
    rw [push _ [false] (by simp [hS, h1]) rfl (by simp [hS, h1])]
    refine ⟨by simp [hS], by simp [hS, h156], by simp [hS], by simp [hS], fun j a b c d e => ?_⟩
    simp [hS, Function.update_apply, a, b, c, d, e]

theorem drop_snoc_drop {L : List Bool} {i : ℕ} (hi : i ≤ L.length) (x : Bool) :
    (L.drop i ++ [x]).drop 1 = (L ++ [x]).drop (i + 1) := by
  rw [← List.drop_append_of_le_length hi, List.drop_drop, Nat.add_comm]

/-- **`j := j + 1`**: register `140` becomes `incW true` of itself. -/
theorem exec_incC (w : St) (h1 : w 1 = [false]) (h3 : w 3 = true :: List.replicate (N * K - 1) false) :
    (exec N K incC w) 140 = incW true (w 140) ∧
      ∀ j : Fin 200, j.val < 140 → (exec N K incC w) j = w j := by
  set J := w 140 with hJ
  set w1 := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update w 159 J) 155 J) 148 [false])
      158 [false]) 154 (w 3)) 154 (List.replicate (N * K - 1) false)) 158 [true]) 156 [true]) 152 J
    with hw1
  have e0 : exec N K (.cp 152 140) (exec N K (.cp 156 158) (exec N K (.mv 158 154 1)
      (exec N K (.cp 154 3) (exec N K (.cp 158 1) (exec N K (.cp 148 1) (exec N K (.cp 155 140)
        (exec N K (.cp 159 140) w))))))) = w1 := by
    rw [show exec N K (.cp 154 3) (exec N K (.cp 158 1) (exec N K (.cp 148 1) (exec N K (.cp 155 140)
        (exec N K (.cp 159 140) w)))) = Function.update (Function.update (Function.update
          (Function.update (Function.update w 159 J) 155 J) 148 [false]) 158 [false]) 154 (w 3) by
      simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, h1, hJ]]
    rw [exec_mv_pop (v := [true]) (L := List.replicate (N * K - 1) false) (by decide)
      (by simp [h1]) (by simp [h1]) (by simp [h3])]
    simp only [exec, Function.update_apply, Fin.reduceEq, ↓reduceIte, hw1, hJ]
  have e1 : exec N K incC w = exec N K (.cp 140 155) (exec N K (.rep 152 incBody) w1) := by
    simp only [incC, exec_ofList_cons, exec_ofList_nil]; rw [e0]
  let P : ℕ → St → Prop := fun i w' =>
    w' 159 = J.drop i ∧ w' 156 = [((J.take i).foldl incStep (true, [])).1] ∧ (w' 148).length = 1 ∧
      w' 155 = (J ++ ((J.take i).foldl incStep (true, [])).2).drop i ∧ w' 158 = [true] ∧
      ∀ j : Fin 200, j.val < 140 → w' j = w j
  have h152 : (w1 152).length = J.length := by simp [hw1]
  have hP := exec_rep_inv (N := N) (K := K) 152 incBody (by decide) P w1
    ⟨by simp [hw1], by simp [hw1], by simp [hw1], by simp [hw1], by simp [hw1], fun j hj => by
      simp only [hw1]
      repeat rw [Function.update_of_ne (by intro e; subst e; simp at hj)]⟩
    (fun i hi w' hw' _ => by
      obtain ⟨p159, p156, p148, p155, p158, pf⟩ := hw'
      rw [h152] at hi
      set w'' := Function.update w' 152 (w' 152).tail with hw''
      have hd : J.drop i = J.getD i false :: J.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem _ _ hi]
      obtain ⟨b159, b156, b148, b155, bf⟩ := exec_incBody (N := N) (K := K) w''
        (by rw [hw'', Function.update_of_ne (by decide), pf 1 (by decide), h1])
        (by rw [hw'', Function.update_of_ne (by decide), p158])
        (by rw [hw'', Function.update_of_ne (by decide), p159, hd])
        (by rw [hw'', Function.update_of_ne (by decide), p156]) (by
          rw [hw'', Function.update_of_ne (by decide)]; exact p148)
      have ht : J.take (i + 1) = J.take i ++ [J.getD i false] := by
        rw [List.take_succ, List.getElem?_eq_getElem hi, List.getD_eq_getElem _ _ hi]; rfl
      have hlo : ((J.take i).foldl incStep (true, [])).2.length = i := by
        rw [foldl_incStep, List.nil_append, length_incW, List.length_take]; omega
      refine ⟨b159, ?_, b148, ?_, ?_, fun j hj => ?_⟩
      · rw [b156, ht, List.foldl_append]; rfl
      · rw [b155, hw'', Function.update_of_ne (by decide), p155, drop_snoc_drop (by simp; omega),
          ht, List.foldl_append, List.append_assoc]; rfl
      · rw [bf 158 (by decide) (by decide) (by decide) (by decide) (by decide), hw'',
          Function.update_of_ne (by decide), p158]
      · have hn : ∀ r : Fin 200, 140 ≤ r.val → j ≠ r := fun r hr e => by subst e; omega
        rw [bf j (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide)) (hn _ (by decide))
          (hn _ (by decide)), hw'', Function.update_of_ne (hn _ (by decide)), pf j hj])
  rw [h152] at hP
  obtain ⟨_, _, _, q155, _, qf⟩ := hP
  rw [e1, show ∀ X : St, exec N K (.cp 140 155) X = Function.update X 140 (X 155) from fun _ => rfl]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [Function.update_self, q155, List.take_length, foldl_incStep, List.nil_append, List.drop_left]
  · rw [Function.update_of_ne (by intro e; subst e; simp at hj), qf j hj]

end AdvancedEncryption.ExpLUT.Prog
