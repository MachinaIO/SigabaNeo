import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.EncPhases

/-!
# The last phases of `Enc` modulo `2^K − 1`

**`tailP : Prog 104`**: the bottom rows of the `16` attribute ciphertexts (`cbP`, a
loop), their digit encodings (`cbP` again into a register, the matrix `[a_t; ·]`, `deP`), the row
`c₀ = s A₀ − (s, 1) G + e₀` and `c_m = s d₁ + d₂ + e_m − u y` (`y = 1`) with `u = −2^{K−1}` if `μ`
and `0` otherwise (`rotBP`, `notP`), all shifted into the output register `0`.

Tapes: `0` output, `1` `s`, `2` `3` the attribute bits (two copies), `4` `5` `6` the rows `a`
(three copies), `7` `8` the errors `e_t` (two copies), `9` `A^in`, `10` the errors of `c^in`, `11`
`A₀`, `12` `e₀`, `13` `d`, `14` `e_m`, `15` `[μ]`, `16` the word of `1`, `17 … 24` the bit
templates, templates `25` (`K`), `26` (`N`), `27` (`N K`), `28` (`2 K`), `29` (`K − 1`), `30`
(`2 K · N K`), `31` (`2 K · N K`), `32` (`4 K · N K`), `33` (length `1`), `34` (`4 K`), `35`
(`16`), `36` (length `1`), `37` (`N K`), `38` (`2 N K`); scratch `39 … 103`.
-/

namespace SigabaNeo.Tape

open SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG

variable {k : ℕ}

namespace Prog

open scoped Prog

theorem run_cbP_map {u : Fin 74 → Fin k} (hu : Function.Injective u) {K N : ℕ} (hK : 0 < K)
    (s : Store k) (hs : ∀ i : Fin 74, 20 ≤ i.val → s (u i) = [])
    (hK' : (s (u 14)).length = K) (hN : (s (u 15)).length = N) (hNK : (s (u 16)).length = N * K)
    (hL : (s (u 17)).length = K + K) (hK1 : (s (u 18)).length = K - 1)
    (h19 : (s (u 19)).length = (K + K) * (N * K)) (h1 : (s (u 1)).length = N * K)
    (h5 : (s (u 5)).length = N * K) :
    run (map u cbP) s = Function.update (Function.update (Function.update (Function.update s (u 0)
      ((s (u 0) ++ cbRow N K (τOf (s ∘ u)) (s (u 1)) (s (u 2)) (s (u 3)) (s (u 4)) (s (u 5))).drop
        ((K + K) * (N * K)))) (u 2) ((s (u 2)).drop 8)) (u 3) ((s (u 3)).drop ((K + K) * (N * K))))
          (u 4) ((s (u 4)).drop ((K + K) * (N * K))) := by
  rw [run_map hu, run_cbP hK (s ∘ u) hs hK' hN hNK hL hK1 h19 h1 h5, extend_update hu,
    extend_update hu, extend_update hu, extend_update hu, extend_comp_self]
  rfl

def tCb1 : Fin 74 → Fin 104 := ![0, 1, 2, 4, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
  29, 30, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
def tCb2 : Fin 74 → Fin 104 := ![40, 1, 3, 5, 8, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
  29, 30, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98]
def tMa : Fin 5 → Fin 104 := ![6, 41, 45, 46, 31]
def tMr : Fin 5 → Fin 104 := ![40, 41, 45, 46, 31]
def tDE : Fin 74 → Fin 104 := ![0, 1, 41, 9, 10, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103]
def tM0 : Fin 66 → Fin 104 := ![0, 1, 44, 16, 11, 12, 25, 26, 27, 28, 29, 30, 31, 32, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]
def tRot : Fin 30 → Fin 104 := ![43, 16, 33, 25, 26, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69]
def tNot : Fin 11 → Fin 104 := ![42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 53]
def tMm : Fin 66 → Fin 104 := ![0, 1, 16, 42, 13, 14, 25, 26, 27, 36, 29, 30, 37, 38, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]

set_option maxRecDepth 10000 in
theorem tCb1_inj : Function.Injective tCb1 := by decide
set_option maxRecDepth 10000 in
theorem tCb2_inj : Function.Injective tCb2 := by decide
set_option maxRecDepth 10000 in
theorem tMa_inj : Function.Injective tMa := by decide
set_option maxRecDepth 10000 in
theorem tMr_inj : Function.Injective tMr := by decide
set_option maxRecDepth 10000 in
theorem tDE_inj : Function.Injective tDE := by decide
set_option maxRecDepth 10000 in
theorem tM0_inj : Function.Injective tM0 := by decide
set_option maxRecDepth 10000 in
theorem tRot_inj : Function.Injective tRot := by decide
set_option maxRecDepth 10000 in
theorem tNot_inj : Function.Injective tNot := by decide
set_option maxRecDepth 10000 in
theorem tMm_inj : Function.Injective tMm := by decide

/-- The bottom rows of the attribute ciphertexts. -/
def cinbotP : Prog 104 := forN 39 35 (map tCb1 cbP)

/-- One attribute ciphertext's digit encodings. -/
def cinBody : Prog 104 :=
  cp 40 30 ⨾ map tCb2 cbP ⨾ cp 41 32 ⨾ map tMa mvP ⨾ map tMr mvP ⨾ map tDE deP ⨾ clr 40 ⨾ clr 41

/-- The digit encodings of the attribute ciphertexts. -/
def cinP : Prog 104 := forN 39 35 cinBody

/-- `c₀`. -/
def c0P : Prog 104 := cp 44 1 ⨾ map tM0 mrowP ⨾ clr 44

/-- `c_m`. -/
def cmP : Prog 104 :=
  map tRot rotBP ⨾ map tNot notP ⨾ clr 43 ⨾ ifBit 15 (clr 43) (cp 42 37) ⨾ map tMm mrowP ⨾ clr 42

/-- **The last phases.** -/
def tailP : Prog 104 := cinbotP ⨾ cinP ⨾ c0P ⨾ cmP

/-! ### The bottom rows -/

/-- One bottom row: `(bits, a, e, out)`. -/
def cbStep (N K : ℕ) (τ : ℕ → ℕ) (s one : List Bool) :
    List Bool × List Bool × List Bool × List Bool → List Bool × List Bool × List Bool × List Bool
  | (x, a, e, o) => (x.drop 8, a.drop ((K + K) * (N * K)), e.drop ((K + K) * (N * K)),
      (o ++ cbRow N K τ s x a e one).drop ((K + K) * (N * K)))

/-- The bit templates of the tail. -/
def τT (S : Store 104) : ℕ → ℕ := τOf (S ∘ tCb1)

/-- The tail's template and scratch conditions. -/
structure TailOK (K N : ℕ) (S : Store 104) : Prop where
  hs : ∀ i : Fin 104, 39 ≤ i.val → S i = []
  hK : (S 25).length = K
  hN : (S 26).length = N
  hNK : (S 27).length = N * K
  h28 : (S 28).length = K + K
  hK1 : (S 29).length = K - 1
  h30 : (S 30).length = (K + K) * (N * K)
  h31 : (S 31).length = (K + K) * (N * K)
  h32 : (S 32).length = (K + K + (K + K)) * (N * K)
  h33 : (S 33).length = 1
  h36 : (S 36).length = 1
  h37 : (S 37).length = N * K
  h38 : (S 38).length = (1 + 1) * (N * K)
  h1 : (S 1).length = N * K
  h16 : (S 16).length = N * K

def cbG (S : Store 104) : List Bool × List Bool × List Bool × List Bool → Store 104
  | (x, a, e, o) =>
    Function.update (Function.update (Function.update (Function.update S 2 x) 4 a) 7 e) 0 o

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_cinbotP {K N : ℕ} (hK : 0 < K) {S : Store 104} (h : TailOK K N S) :
    run cinbotP S = cbG S ((cbStep N K (τT S) (S 1) (S 16))^[(S 35).length] (S 2, S 4, S 7, S 0)) := by
  have e := run_forN 39 35 (map tCb1 cbP) (cbG S) (cbStep N K (τT S) (S 1) (S 16))
    (fun a w => by
      obtain ⟨x, a', e', o⟩ := a
      rw [run_cbP_map tCb1_inj (K := K) (N := N) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
      · have hfix : ∀ j : Fin 74, 6 ≤ j.val → j.val < 14 →
            Function.update (cbG S (x, a', e', o)) 39 w (tCb1 j) = S (tCb1 j) := by
          intro j h1 h2; fin_cases j <;> simp_all [tCb1, cbG]
        have : τOf (Function.update (cbG S (x, a', e', o)) 39 w ∘ tCb1) = τT S := by
          funext i
          simp only [τOf, τT, Function.comp]
          rw [hfix _ (by simp) (by simp; omega)]
        rw [this]
        funext t
        fin_cases t <;> simp [tCb1, cbG, cbStep]
      · intro i hi; fin_cases i <;> simp [tCb1, cbG, h.hs] at hi ⊢
      all_goals simp [tCb1, cbG, h.hK, h.hN, h.hNK, h.h28, h.hK1, h.h30, h.h1, h.h16])
    (S 2, S 4, S 7, S 0) S (by funext t; fin_cases t <;> simp [cbG])
  rw [cinbotP, e]
  funext t
  generalize (cbStep N K (τT S) (S 1) (S 16))^[(S 35).length] (S 2, S 4, S 7, S 0) = r
  obtain ⟨x, a, e', o⟩ := r
  fin_cases t <;> simp [cbG, h.hs]

theorem noGrow_tailP : tailP.NoGrow := rfl

set_option maxRecDepth 100000 in
theorem wf_tailP : tailP.WF := wf_of_wfB (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_c0P {K N : ℕ} (hK : 0 < K) {S : Store 104} (h : TailOK K N S) :
    run c0P S = Function.update (Function.update (Function.update S 0
      ((S 0 ++ hRow N K (S 1) (S 1) (S 16) (S 11) (S 12)).drop
        ((K + K) * (N * K)))) 11 ((S 11).drop ((K + K + (K + K)) * (N * K))))
          12 ((S 12).drop ((K + K) * (N * K))) := by
  simp only [c0P, run_seq, run_copy, run_clear]
  rw [run_mrowP_map tM0_inj (K := K) (N := N) (L := K + K) hK _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi
    fin_cases i <;> simp [tM0, h.hs] at hi ⊢
  all_goals try (simp [tM0, h.hK, h.hN, h.hNK, h.h28, h.hK1, h.h30,
    h.h31, h.h32, h.h1, h.h16]; done)
  funext t
  fin_cases t <;> simp [tM0, hRow, h.hs]


/-- The message-dependent word subtracted by the message row. -/
def cmMask (N K : ℕ) (S : Store 104) : List Bool :=
  if hd (S 15) = true then notW (rotBW N K 1 (S 16)) else S 37

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_cmP {K N : ℕ} (hK : 0 < K) {S : Store 104} (h : TailOK K N S) :
    run cmP S = Function.update (Function.update (Function.update S 0
      ((S 0 ++ rowW N K 1 (S 1) (S 13) ((S 13).drop (N * K))
        (zStream N K (cmMask N K S) (S 16)) (S 14)).drop (N * K)))
          13 ((S 13).drop ((1 + 1) * (N * K)))) 14 ((S 14).drop (N * K)) := by
  have hmask : (cmMask N K S).length = N * K := by
    unfold cmMask
    split_ifs
    · rw [length_notW, length_rotBW N K 1 h.h16]
    · exact h.h37
  simp only [cmP, run_seq, run_clear]
  rw [run_rotBP_map tRot_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [tRot, h.hs] at hi ⊢
  all_goals try (simp [tRot, h.hK, h.hN, h.h16]; done)
  rw [run_notP_map tNot_inj _ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [tNot, tRot, h.hs] at hi ⊢
  have hprep : run (ifBit 15 (clr 43) (cp 42 37))
      (Function.update (Function.update (Function.update S (tRot 0)
        (rotBW N K (S (tRot 2)).length (S (tRot 1)))) (tNot 0)
          (notW (Function.update S (tRot 0)
            (rotBW N K (S (tRot 2)).length (S (tRot 1))) (tNot 1)))) 43 []) =
        Function.update S 42 (cmMask N K S) := by
    by_cases hm : hd (S 15) = true
    all_goals
      simp [run_ifBit, tRot, tNot, hm, run_clear, run_copy, cmMask, h.h33]
      funext t
      fin_cases t <;> simp [h.hs]
  rw [hprep]
  rw [run_mrowP_map tMm_inj (K := K) (N := N) (L := 1) hK _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [tMm, h.hs] at hi ⊢
  all_goals try (simp [tMm, h.hK, h.hN, h.hNK, h.h36, h.hK1, h.h30,
    h.h37, h.h38, h.h1, hmask]; done)
  funext t
  fin_cases t <;> simp [tMm, h.hs]

/-- One attribute's digit-encoding step, with the input streams explicit. -/
def ciStep (N K : ℕ) (τ : ℕ → ℕ) (s one z2 z4 : List Bool) (entries : ℕ) :
    List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool →
    List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool
  | (x, a, e, aCopy, A, E, out) =>
    let n := (K + K) * (N * K)
    let bottom := (z2 ++ cbRow N K τ s x a e one).drop n
    let top := (z4 ++ takeD n aCopy).drop n
    let C := (top ++ takeD n bottom).drop n
    let r := (deOut N K (K + K) s)^[entries] (C, out, A, E)
    (x.drop 8, a.drop n, e.drop n, aCopy.drop n, r.2.2.1, r.2.2.2, r.2.1)

/-- Mutable streams of the attribute digit-encoding loop. -/
def ciG (S : Store 104) :
    List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → Store 104
  | (x, a, e, aCopy, A, E, out) =>
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update S 3 x) 5 a) 8 e) 6 aCopy) 9 A) 10 E) 0 out

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem run_cinBody {K N : ℕ} (hK : 0 < K) {S : Store 104} (h : TailOK K N S)
    (w : List Bool) :
    run cinBody (Function.update S 39 w) = Function.update (ciG S
      (ciStep N K (τT S) (S 1) (S 16) (S 30) (S 32) (S 34).length
        (S 3, S 5, S 8, S 6, S 9, S 10, S 0))) 39 w := by
  simp only [cinBody, run_seq, run_copy, run_clear]
  rw [run_cbP_map tCb2_inj (K := K) (N := N) hK _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [tCb2, h.hs] at hi ⊢
  all_goals try (simp [tCb2, h.hK, h.hN, h.hNK, h.h28, h.hK1, h.h30,
    h.h1, h.h16]; done)
  have ht : τOf (Function.update (Function.update S 39 w) 40 (S 30) ∘ tCb2) = τT S := by
    funext i
    simp only [τOf, τT, Function.comp]
    have hf : ∀ j : Fin 74, 6 ≤ j.val → j.val < 14 →
        Function.update (Function.update S 39 w) 40 (S 30) (tCb2 j) = S (tCb1 j) := by
      intro j h1 h2
      fin_cases j <;> simp_all [tCb1, tCb2]
    rw [hf _ (by simp) (by simp; omega)]
  simp only [show (Function.update S 39 w) 30 = S 30 from rfl]
  rw [ht]
  rw [run_mvP_map tMa_inj _ (by simp [tMa, tCb2, h.hs])
    (by simp [tMa, tCb2, h.hs])]
  rw [run_mvP_map tMr_inj _ (by simp [tMr, tMa, tCb2, h.hs])
    (by simp [tMr, tMa, tCb2, h.hs])]
  rw [run_deP_map tDE_inj (K := K) (N := N) (L := K + K) hK _
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · intro i hi; fin_cases i <;> simp [tDE, tMr, tMa, tCb2, h.hs] at hi ⊢
  all_goals try (simp [tDE, tMr, tMa, tCb2, h.hK, h.hN, h.hNK, h.h28, h.hK1,
    h.h30, h.h31, h.h32, h.h33, h.h1]; done)
  funext t
  fin_cases t <;> simp [tDE, tMr, tMa, tCb2, ciG, ciStep, h.h31, h.hs]


theorem tailOK_ciG {K N : ℕ} {S : Store 104} (h : TailOK K N S)
    (a : List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :
    TailOK K N (ciG S a) := by
  obtain ⟨x, aa, e, ac, A, E, o⟩ := a
  constructor
  · intro i hi
    fin_cases i <;> simp [ciG, h.hs] at hi ⊢
  · simpa [ciG] using h.hK
  · simpa [ciG] using h.hN
  · simpa [ciG] using h.hNK
  · simpa [ciG] using h.h28
  · simpa [ciG] using h.hK1
  · simpa [ciG] using h.h30
  · simpa [ciG] using h.h31
  · simpa [ciG] using h.h32
  · simpa [ciG] using h.h33
  · simpa [ciG] using h.h36
  · simpa [ciG] using h.h37
  · simpa [ciG] using h.h38
  · simpa [ciG] using h.h1
  · simpa [ciG] using h.h16

theorem τT_ciG (S : Store 104)
    (a : List Bool × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :
    τT (ciG S a) = τT S := by
  obtain ⟨x, aa, e, ac, A, E, o⟩ := a
  have hf : ∀ j : Fin 74, 6 ≤ j.val → j.val < 14 → ciG S (x, aa, e, ac, A, E, o) (tCb1 j) =
      S (tCb1 j) := by
    intro j h1 h2
    fin_cases j <;> simp_all [tCb1, ciG]
  funext i
  simp only [τT, τOf, Function.comp]
  rw [hf _ (by simp) (by simp; omega)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem run_cinP {K N : ℕ} (hK : 0 < K) {S : Store 104} (h : TailOK K N S) :
    run cinP S = ciG S
      ((ciStep N K (τT S) (S 1) (S 16) (S 30) (S 32) (S 34).length)^[(S 35).length]
        (S 3, S 5, S 8, S 6, S 9, S 10, S 0)) := by
  have e := run_forN 39 35 cinBody (ciG S)
    (ciStep N K (τT S) (S 1) (S 16) (S 30) (S 32) (S 34).length)
    (fun a w => by
      rw [run_cinBody hK (tailOK_ciG h a) w, τT_ciG]
      obtain ⟨x, aa, ee, ac, A, E, o⟩ := a
      funext t
      fin_cases t <;> simp [ciG])
    (S 3, S 5, S 8, S 6, S 9, S 10, S 0) S (by funext t; fin_cases t <;> simp [ciG])
  rw [cinP, e]
  generalize (ciStep N K (τT S) (S 1) (S 16) (S 30) (S 32) (S 34).length)^[(S 35).length]
      (S 3, S 5, S 8, S 6, S 9, S 10, S 0) = a
  obtain ⟨x, aa, ee, ac, A, E, o⟩ := a
  funext t
  fin_cases t <;> simp [ciG, h.hs]


/-- Transfer the tail invariant when the templates and secret word are preserved. -/
theorem TailOK.of_agree {K N : ℕ} {S S' : Store 104} (h : TailOK K N S)
    (hs : ∀ i : Fin 104, 39 ≤ i.val → S' i = [])
    (hf : ∀ i : Fin 104, i = 1 ∨ (16 ≤ i.val ∧ i.val < 39) → S' i = S i) :
    TailOK K N S' := by
  constructor
  · exact hs
  · simpa only [hf 25 (by decide)] using h.hK
  · simpa only [hf 26 (by decide)] using h.hN
  · simpa only [hf 27 (by decide)] using h.hNK
  · simpa only [hf 28 (by decide)] using h.h28
  · simpa only [hf 29 (by decide)] using h.hK1
  · simpa only [hf 30 (by decide)] using h.h30
  · simpa only [hf 31 (by decide)] using h.h31
  · simpa only [hf 32 (by decide)] using h.h32
  · simpa only [hf 33 (by decide)] using h.h33
  · simpa only [hf 36 (by decide)] using h.h36
  · simpa only [hf 37 (by decide)] using h.h37
  · simpa only [hf 38 (by decide)] using h.h38
  · simpa only [hf 1 (by decide)] using h.h1
  · simpa only [hf 16 (by decide)] using h.h16

/-- Output store of the initial ciphertext row. -/
def c0Store (N K : ℕ) (S : Store 104) : Store 104 :=
  Function.update (Function.update (Function.update S 0
    ((S 0 ++ hRow N K (S 1) (S 1) (S 16) (S 11) (S 12)).drop
      ((K + K) * (N * K)))) 11 ((S 11).drop ((K + K + (K + K)) * (N * K))))
        12 ((S 12).drop ((K + K) * (N * K)))

/-- Output store of the message row. -/
def cmStore (N K : ℕ) (S : Store 104) : Store 104 :=
  Function.update (Function.update (Function.update S 0
    ((S 0 ++ rowW N K 1 (S 1) (S 13) ((S 13).drop (N * K))
      (zStream N K (cmMask N K S) (S 16)) (S 14)).drop (N * K)))
        13 ((S 13).drop ((1 + 1) * (N * K)))) 14 ((S 14).drop (N * K))

/-- The complete tail as pure word operations, in ciphertext output order. -/
def tailStore (N K : ℕ) (S : Store 104) : Store 104 :=
  let B := cbG S ((cbStep N K (τT S) (S 1) (S 16))^[(S 35).length]
    (S 2, S 4, S 7, S 0))
  let C := ciG B ((ciStep N K (τT B) (B 1) (B 16) (B 30) (B 32) (B 34).length)^[(B 35).length]
    (B 3, B 5, B 8, B 6, B 9, B 10, B 0))
  cmStore N K (c0Store N K C)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem run_tailP {K N : ℕ} (hK : 0 < K) {S : Store 104} (h : TailOK K N S) :
    run tailP S = tailStore N K S := by
  have hb : ∀ a, TailOK K N (cbG S a) := by
    rintro ⟨x, a, e, o⟩
    apply h.of_agree
    · intro i hi; fin_cases i <;> simp [cbG, h.hs] at hi ⊢
    · intro i hi; fin_cases i <;> simp [cbG] at hi ⊢
  have h0 : ∀ (T : Store 104), TailOK K N T → TailOK K N (c0Store N K T) := by
    intro T hT
    apply hT.of_agree
    · intro i hi; fin_cases i <;> simp [c0Store, hT.hs] at hi ⊢
    · intro i hi; fin_cases i <;> simp [c0Store] at hi ⊢
  let B := cbG S ((cbStep N K (τT S) (S 1) (S 16))^[(S 35).length]
    (S 2, S 4, S 7, S 0))
  let C := ciG B ((ciStep N K (τT B) (B 1) (B 16) (B 30) (B 32) (B 34).length)^[(B 35).length]
    (B 3, B 5, B 8, B 6, B 9, B 10, B 0))
  have hC : TailOK K N C := tailOK_ciG (hb _) _
  simp only [tailP, run_seq]
  rw [run_cinbotP hK h, run_cinP hK (hb _)]
  change run cmP (run c0P C) = cmStore N K (c0Store N K C)
  rw [show run c0P C = c0Store N K C from run_c0P hK hC]
  exact run_cmP hK (h0 C hC)

end Prog

end SigabaNeo.Tape
