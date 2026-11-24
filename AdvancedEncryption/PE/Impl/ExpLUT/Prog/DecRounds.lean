import PE.Impl.ExpLUT.Prog.DecRoundT

/-!
# The rounds along the bits of `j` on the ring-word machine (Dec, package F4)

`roundsN n`: for `t < n`, pop the helper data of round `t` from the streams `164` (`H`),
`165` (`h`), `166` (`A^aut`), `167` (`c^aut`) and the bit `t` of `j` from `169`; if it is set, run
`roundC t`. **`exec_roundsN`**: the pair on `120`, `121` becomes `bitRounds` of `DecAlg`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

/-- One round of the bit loop. -/
def tStep (t : ℕ) : Code :=
  ofList [.mv 122 164 7, .mv 123 164 7, .mv 124 165 6, .mv 125 165 6, .mv 126 166 77,
    .mv 127 167 10, .mv 170 169 1, .ifb 170 (roundC t) .nop]

/-- The first `n` rounds of the bit loop. -/
def roundsN : ℕ → Code
  | 0 => .nop
  | n + 1 => .seq (roundsN n) (tStep n)

/-- The word data of the rounds: the words of `H_{g_t}`, `H_{g_t^{-1}}`, `h_{g_t}`, `h_{g_t^{-1}}`,
the row families of `A^aut_t`, the family `c^aut_t`. -/
structure RData where
  Hf : ℕ → List (List Bool)
  Hi : ℕ → List (List Bool)
  hf : ℕ → List (List Bool)
  hi : ℕ → List (List Bool)
  A0 : ℕ → List (List (List Bool))
  A1 : ℕ → List (List (List Bool))
  cw : ℕ → List (List (List Bool))

/-- The word of a family of matrices from its row families. -/
def famMW (f₀ f₁ : List (List (List Bool))) : List Bool :=
  (List.zipWith (· ++ ·) (f₀.map List.flatten) (f₁.map List.flatten)).flatten

/-- The word of a family of vectors. -/
def famVW (f : List (List (List Bool))) : List Bool := (f.map List.flatten).flatten

/-- The streams from round `t` on. -/
def sH (rd : RData) (t : ℕ) : List Bool :=
  ((List.range' t (22 - t)).map fun s => (rd.Hf s).flatten ++ (rd.Hi s).flatten).flatten
def sh (rd : RData) (t : ℕ) : List Bool :=
  ((List.range' t (22 - t)).map fun s => (rd.hf s).flatten ++ (rd.hi s).flatten).flatten
def sA (rd : RData) (t : ℕ) : List Bool :=
  ((List.range' t (22 - t)).map fun s => famMW (rd.A0 s) (rd.A1 s)).flatten
def sc (rd : RData) (t : ℕ) : List Bool :=
  ((List.range' t (22 - t)).map fun s => famVW (rd.cw s)).flatten

theorem range'_succ_22 {t : ℕ} (ht : t < 22) : List.range' t (22 - t) = t :: List.range' (t + 1) (22 - (t + 1)) := by
  rw [show 22 - t = (22 - (t + 1)) + 1 by omega, List.range'_succ]

theorem sH_succ (rd : RData) {t : ℕ} (ht : t < 22) :
    sH rd t = (rd.Hf t).flatten ++ ((rd.Hi t).flatten ++ sH rd (t + 1)) := by
  rw [sH, range'_succ_22 ht]; simp [sH]
theorem sh_succ (rd : RData) {t : ℕ} (ht : t < 22) :
    sh rd t = (rd.hf t).flatten ++ ((rd.hi t).flatten ++ sh rd (t + 1)) := by
  rw [sh, range'_succ_22 ht]; simp [sh]
theorem sA_succ (rd : RData) {t : ℕ} (ht : t < 22) :
    sA rd t = famMW (rd.A0 t) (rd.A1 t) ++ sA rd (t + 1) := by
  rw [sA, range'_succ_22 ht]; simp [sA]
theorem sc_succ (rd : RData) {t : ℕ} (ht : t < 22) :
    sc rd t = famVW (rd.cw t) ++ sc rd (t + 1) := by
  rw [sc, range'_succ_22 ht]; simp [sc]

variable (D) in
/-- The word data represent the helper data `P`, `h`. -/
def RDOk (rd : RData) (P : AutPub (setting D)) (hd : AutData (setting D)) : Prop :=
  ∀ t < 22, RepM D (rd.Hf t) (P.Hf t) ∧ RepM D (rd.Hi t) (P.Hi t) ∧ RepV D (rd.hf t) (hd.hf t) ∧
    RepV D (rd.hi t) (hd.hi t) ∧ RepFV D (rd.A0 t) (fun d => P.Aaut t d 0) ∧
    RepFV D (rd.A1 t) (fun d => P.Aaut t d 1) ∧ RepFV D (rd.cw t) (hd.caut t)

theorem lenM {ms : List (List Bool)} {M : Matrix (Fin 2) (Col D.K) (Rg D)} (h : RepM D ms M) :
    ms.flatten.length = 4 * D.K * (D.N * D.K) := by rw [length_flatten_of h.wid, h.len]

theorem lenFV {f : List (List (List Bool))} {F : Dig D.K → Col D.K → Rg D} (h : RepFV D f F) :
    famVW f = famVW f ∧ (famVW f).length = 2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K)) := by
  refine ⟨rfl, ?_⟩
  rw [famVW, length_flatten_of (flatten_famV h.ok), List.length_map, h.len]

theorem lenFM {f₀ f₁ : List (List (List Bool))} {F₀ F₁ : Dig D.K → Col D.K → Rg D}
    (h₀ : RepFV D f₀ F₀) (h₁ : RepFV D f₁ F₁) :
    (famMW f₀ f₁).length = 2 * (2 * D.K) * D.K * (4 * D.K * (D.N * D.K)) := by
  rw [famMW, length_flatten_of (n := 4 * D.K * (D.N * D.K))]
  · simp [h₀.len, h₁.len]
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_zipWith, List.length_append, List.getElem_map, List.getElem_map,
      length_flatten_of ((h₀.ok _ (List.getElem_mem _)).2), (h₀.ok _ (List.getElem_mem _)).1,
      length_flatten_of ((h₁.ok _ (List.getElem_mem _)).2), (h₁.ok _ (List.getElem_mem _)).1]
    ring

/-- The template of a family of matrices (register `77`). -/
abbrev famMLen (D : Dims) : ℕ := 2 * (2 * D.K) * D.K * (4 * D.K * (D.N * D.K))

/-- The frame of the bit loop. -/
def BFr (w w' : St) : Prop :=
  ∀ j : Fin 200, (j.val < 80 ∨ (140 ≤ j.val ∧ (j.val < 164 ∨ 171 ≤ j.val))) → w' j = w j

variable (D) in
/-- **The invariant of the bit loop** after `n` rounds. -/
structure RsInv (rd : RData) (P : AutPub (setting D)) (hd : AutData (setting D))
    (x : Matrix (Fin 2) (Col D.K) (Rg D) × (Col D.K → Rg D)) (j : ℕ) (Jw : List Bool) (w₀ : St)
    (n : ℕ) (w : St) : Prop where
  ec : EC D w
  r77 : w 77 = List.replicate (famMLen D) false
  s164 : w 164 = sH rd n
  s165 : w 165 = sh rd n
  s166 : w 166 = sA rd n
  s167 : w 167 = sc rd n
  s169 : w 169 = Jw.drop n
  l122 : (w 122).length = 4 * D.K * (D.N * D.K)
  l123 : (w 123).length = 4 * D.K * (D.N * D.K)
  l124 : (w 124).length = 2 * D.K * (D.N * D.K)
  l125 : (w 125).length = 2 * D.K * (D.N * D.K)
  l126 : (w 126).length = famMLen D
  l127 : (w 127).length = 2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))
  l170 : (w 170).length = 1
  A : ∃ as, w 120 = as.flatten ∧ RepM D as (bitRounds P hd x j n).1
  c : ∃ cs, w 121 = cs.flatten ∧ RepV D cs (bitRounds P hd x j n).2
  fr : BFr w₀ w

theorem exec_tStep {rd : RData} {P : AutPub (setting D)} {hd : AutData (setting D)}
    (hok : RDOk D rd P hd) {x : Matrix (Fin 2) (Col D.K) (Rg D) × (Col D.K → Rg D)} {j : ℕ}
    {Jw : List Bool} (hJ : ∀ s < 22, Jw.getD s false = j.testBit s) (hJl : Jw.length = 22)
    {w₀ : St} {n : ℕ} (hn : n < 22) {w : St} (h : RsInv D rd P hd x j Jw w₀ n w) :
    RsInv D rd P hd x j Jw w₀ (n + 1) (exec D.N D.K (tStep n) w) := by
  obtain ⟨oHf, oHi, ohf, ohi, oA0, oA1, ocw⟩ := hok n hn
  have hc := h.ec.ck.c
  have l7 : (w 7).length = 4 * D.K * (D.N * D.K) := by rw [h.ec.ck.mat, List.length_replicate]
  have l6 : (w 6).length = 2 * D.K * (D.N * D.K) := by rw [h.ec.r6, List.length_replicate]
  have l10 : (w 10).length = 2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K)) := by
    rw [h.ec.r10, List.length_replicate]
  have l77 : (w 77).length = famMLen D := by rw [h.r77, List.length_replicate]
  have hb : Jw.drop n = [Jw.getD n false] ++ Jw.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]; rfl
  set u := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update w
      164 ((rd.Hi n).flatten ++ sH rd (n + 1))) 122 (rd.Hf n).flatten)
      164 (sH rd (n + 1))) 123 (rd.Hi n).flatten)
      165 ((rd.hi n).flatten ++ sh rd (n + 1))) 124 (rd.hf n).flatten)
      165 (sh rd (n + 1))) 125 (rd.hi n).flatten)
      166 (sA rd (n + 1))) 126 (famMW (rd.A0 n) (rd.A1 n)))
      167 (sc rd (n + 1))) 127 (famVW (rd.cw n)))
      169 (Jw.drop (n + 1))) 170 [Jw.getD n false] with hu
  have e7 : exec D.N D.K (ofList [.mv 122 164 7, .mv 123 164 7, .mv 124 165 6, .mv 125 165 6,
      .mv 126 166 77, .mv 127 167 10, .mv 170 169 1]) w = u := by
    simp only [exec_ofList_cons, exec_ofList_nil]
    rw [exec_mv_pop (d := 122) (s := 164) (c := 7) (v := (rd.Hf n).flatten) (L := (rd.Hi n).flatten ++ sH rd (n + 1)) (by decide) (by rw [h.l122, l7])
      (by rw [lenM oHf, l7]) (by rw [h.s164, sH_succ rd hn])]
    rw [exec_mv_pop (d := 123) (s := 164) (c := 7) (v := (rd.Hi n).flatten) (L := sH rd (n + 1)) (by decide) (by simp [h.l123, l7])
      (by simp [lenM oHi, l7]) (by simp)]
    rw [exec_mv_pop (d := 124) (s := 165) (c := 6) (v := (rd.hf n).flatten) (L := (rd.hi n).flatten ++ sh rd (n + 1)) (by decide) (by simp [h.l124, l6])
      (by simp [lenV ohf, l6]) (by simp [h.s165, sh_succ rd hn])]
    rw [exec_mv_pop (d := 125) (s := 165) (c := 6) (v := (rd.hi n).flatten) (L := sh rd (n + 1)) (by decide) (by simp [h.l125, l6])
      (by simp [lenV ohi, l6]) (by simp)]
    rw [exec_mv_pop (d := 126) (s := 166) (c := 77) (v := famMW (rd.A0 n) (rd.A1 n)) (L := sA rd (n + 1)) (by decide) (by simp [h.l126, l77])
      (by simp [lenFM oA0 oA1, l77]) (by simp [h.s166, sA_succ rd hn])]
    rw [exec_mv_pop (d := 127) (s := 167) (c := 10) (v := famVW (rd.cw n)) (L := sc rd (n + 1)) (by decide) (by simp [h.l127, l10])
      (by simp [(lenFV ocw).2, l10]) (by simp [h.s167, sc_succ rd hn])]
    rw [exec_mv_pop (d := 170) (s := 169) (c := 1) (v := [Jw.getD n false]) (L := Jw.drop (n + 1)) (by decide) (by simp [h.l170, hc.one])
      (by simp [hc.one]) (by simp [h.s169, hb])]
  have ulo : ∀ k : Fin 200, (k.val < 122 ∨ (127 < k.val ∧ k.val < 164) ∨ 171 ≤ k.val ∨ k.val = 168) →
      u k = w k := fun k hk => by
    have nv : ∀ d : Fin 200, (d.val = 122 ∨ d.val = 123 ∨ d.val = 124 ∨ d.val = 125 ∨ d.val = 126 ∨
        d.val = 127 ∨ d.val = 164 ∨ d.val = 165 ∨ d.val = 166 ∨ d.val = 167 ∨ d.val = 169 ∨
        d.val = 170) → k ≠ d := fun d hd e => by subst e; omega
    rw [hu, Function.update_of_ne (nv 170 (by decide)), Function.update_of_ne (nv 169 (by decide)),
      Function.update_of_ne (nv 127 (by decide)), Function.update_of_ne (nv 167 (by decide)),
      Function.update_of_ne (nv 126 (by decide)), Function.update_of_ne (nv 166 (by decide)),
      Function.update_of_ne (nv 125 (by decide)), Function.update_of_ne (nv 165 (by decide)),
      Function.update_of_ne (nv 124 (by decide)), Function.update_of_ne (nv 165 (by decide)),
      Function.update_of_ne (nv 123 (by decide)), Function.update_of_ne (nv 164 (by decide)),
      Function.update_of_ne (nv 122 (by decide)), Function.update_of_ne (nv 164 (by decide))]
  have ec' : EC D u := h.ec.of_agree fun k hk => ulo k (by omega)
  have e : exec D.N D.K (tStep n) w = exec D.N D.K (.ifb 170 (roundC n) .nop) u := by
    rw [← e7]; rfl
  have u170 : u 170 = [Jw.getD n false] := by simp [hu]
  have hbit : Jw.getD n false = j.testBit n := hJ n hn
  obtain ⟨as, hA0, hA⟩ := h.A
  obtain ⟨cs, hc0, hcs⟩ := h.c
  have u120 : u 120 = as.flatten := by rw [ulo 120 (by decide), hA0]
  have u121 : u 121 = cs.flatten := by rw [ulo 121 (by decide), hc0]
  have u164 : u 164 = sH rd (n + 1) := by simp [hu]
  have u165 : u 165 = sh rd (n + 1) := by simp [hu]
  have u166 : u 166 = sA rd (n + 1) := by simp [hu]
  have u167 : u 167 = sc rd (n + 1) := by simp [hu]
  have u169 : u 169 = Jw.drop (n + 1) := by simp [hu]
  have u77 : u 77 = List.replicate (famMLen D) false := by rw [ulo 77 (by decide), h.r77]
  have u122 : u 122 = (rd.Hf n).flatten := by simp [hu]
  have u123 : u 123 = (rd.Hi n).flatten := by simp [hu]
  have u124 : u 124 = (rd.hf n).flatten := by simp [hu]
  have u125 : u 125 = (rd.hi n).flatten := by simp [hu]
  have u126 : u 126 = famMW (rd.A0 n) (rd.A1 n) := by simp [hu]
  have u127 : u 127 = famVW (rd.cw n) := by simp [hu]
  have ufr : BFr w₀ u := fun k hk => by rw [ulo k (by omega)]; exact h.fr k hk
  by_cases hb' : j.testBit n = true
  · have e' : exec D.N D.K (tStep n) w = exec D.N D.K (roundC n) u := by
      rw [e]; show (if SigabaNeo.Tape.hd (u 170) = true then _ else _) = _; rw [u170, hbit, hb']; rfl
    have hin : RoundIn D u (bitRounds P hd x j n).1 (bitRounds P hd x j n).2 (P.Hf n) (P.Hi n)
        (hd.hf n) (hd.hi n) (P.Aaut n) (hd.caut n) :=
      { ec := ec', A := ⟨as, u120, hA⟩, c := ⟨cs, u121, hcs⟩, Hf := ⟨_, u122, oHf⟩,
        Hi := ⟨_, u123, oHi⟩, hf := ⟨_, u124, ohf⟩, hi := ⟨_, u125, ohi⟩,
        Aaut := ⟨rd.A0 n, rd.A1 n, u126, oA0, oA1⟩, caut := ⟨rd.cw n, u127, ocw⟩ }
    obtain ⟨⟨as', a120, r120⟩, ⟨cs', a121, r121⟩, rf⟩ := exec_roundC n hn u hin
    have hbr : bitRounds P hd x j (n + 1) = autStep P hd n (bitRounds P hd x j n) := by
      simp only [bitRounds, hb', ↓reduceIte]
    have rk : ∀ k : Fin 200, 140 ≤ k.val → exec D.N D.K (tStep n) w k = u k := fun k hk => by
      rw [e']; exact rf k (Or.inr (Or.inl hk))
    have rk' : ∀ k : Fin 200, (122 ≤ k.val ∧ k.val < 128) → exec D.N D.K (tStep n) w k = u k :=
      fun k hk => by rw [e']; exact rf k (Or.inr (Or.inr hk))
    have rkl : ∀ k : Fin 200, k.val < 80 → exec D.N D.K (tStep n) w k = u k := fun k hk => by
      rw [e']; exact rf k (Or.inl hk)
    exact
      { ec := ec'.of_agree fun k hk => rkl k hk
        r77 := by rw [rkl 77 (by decide), u77]
        s164 := by rw [rk 164 (by decide), u164]
        s165 := by rw [rk 165 (by decide), u165]
        s166 := by rw [rk 166 (by decide), u166]
        s167 := by rw [rk 167 (by decide), u167]
        s169 := by rw [rk 169 (by decide), u169]
        l122 := by rw [rk' 122 (by decide), u122, lenM oHf]
        l123 := by rw [rk' 123 (by decide), u123, lenM oHi]
        l124 := by rw [rk' 124 (by decide), u124, lenV ohf]
        l125 := by rw [rk' 125 (by decide), u125, lenV ohi]
        l126 := by rw [rk' 126 (by decide), u126, lenFM oA0 oA1]
        l127 := by rw [rk' 127 (by decide), u127, (lenFV ocw).2]
        l170 := by rw [rk 170 (by decide), u170]; rfl
        A := ⟨as', by rw [e', a120], by
          rw [hbr]; exact r120.congr fun a c => roundPK_eq n _ _ _ a c⟩
        c := ⟨cs', by rw [e', a121], by
          rw [hbr]; exact r121.congr fun c => roundCT_eq n _ _ _ _ _ _ _ c⟩
        fr := fun k hk => by
          rcases hk with hk | hk
          · rw [rkl k hk]; exact ufr k (Or.inl hk)
          · rw [rk k hk.1]; exact ufr k (Or.inr hk) }
  · have e' : exec D.N D.K (tStep n) w = u := by
      rw [e]; show (if SigabaNeo.Tape.hd (u 170) = true then _ else _) = _; rw [u170, hbit]; simp [SigabaNeo.Tape.hd, hb']; rfl
    have hbr : bitRounds P hd x j (n + 1) = bitRounds P hd x j n := by
      simp only [bitRounds, hb', ↓reduceIte, Bool.false_eq_true]
    rw [e']
    exact
      { ec := ec', r77 := u77, s164 := u164, s165 := u165, s166 := u166, s167 := u167,
        s169 := u169, l122 := by rw [u122, lenM oHf], l123 := by rw [u123, lenM oHi],
        l124 := by rw [u124, lenV ohf], l125 := by rw [u125, lenV ohi],
        l126 := by rw [u126, lenFM oA0 oA1], l127 := by rw [u127, (lenFV ocw).2],
        l170 := by rw [u170]; rfl, A := ⟨as, u120, hbr ▸ hA⟩, c := ⟨cs, u121, hbr ▸ hcs⟩,
        fr := ufr }

/-- **The bit loop**: after `n ≤ 22` rounds, the pair is `bitRounds … j n`. -/
theorem exec_roundsN {rd : RData} {P : AutPub (setting D)} {hd : AutData (setting D)}
    (hok : RDOk D rd P hd) {x : Matrix (Fin 2) (Col D.K) (Rg D) × (Col D.K → Rg D)} {j : ℕ}
    {Jw : List Bool} (hJ : ∀ s < 22, Jw.getD s false = j.testBit s) (hJl : Jw.length = 22)
    {w₀ w : St} (h : RsInv D rd P hd x j Jw w₀ 0 w) :
    ∀ n ≤ 22, RsInv D rd P hd x j Jw w₀ n (exec D.N D.K (roundsN n) w)
  | 0, _ => h
  | n + 1, hn => exec_tStep hok hJ hJl (by omega) (exec_roundsN hok hJ hJl h n (by omega))

end AdvancedEncryption.ExpLUT.Prog
