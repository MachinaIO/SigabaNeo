import PE.Impl.DualUse.Prog.EncBits

/-!
# The deterministic core of `Enc` as one register program

`encCoreP : Prog 120` (in the fragment `NoGrow`: no coin, no lengthening; registers are
initialised from templates) computes the word of a ciphertext from the words of the public key,
the date bits, the message bit and the coins, in eight phases:

1. `gadPh`: the gadget row `G̲` (`gadP`) and the Ring-GSW gadget `Γ.G` (`gswW`, shifted into a
   register);
2. `c0Ph`, `c1Ph`: `c₀ = s B₀ + e₀`, `c₁ = s B₁ + e₁` (`matMulP`, `addRWP`);
3. `kapPh`: `κ = s p + e' (+ ⌊q/2⌋)` (`mulRWP`, `addRWP`, the word of `⌊q/2⌋` shifted into a
   register);
4. `psiPh`: the ten `Ψᵢ` (`binMulP`);
5. `zPh`: the bits `ψ_j` (`coefBitsP`);
6. `cjPh`: the encodings `c_j` (`bggEncP`);
7. `ctPh`: the fields shifted into the output register.

Tapes: `0` the output register; inputs `1` `B₀`, `2` `B₁`, `3` the `B_j`, `4` `p`, `5` the date
bits, `6` the message bit, `7` `s`, `8` `e₀`, `9` `e₁`, `10` the `Rᵢ`, `11` the errors `e_j`,
`12` `e'`; templates `13 … 38`; intermediates `39 … 51`; scratch `52 … 119`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.Prog Matrix AdvancedEncryption.RingBTVW Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open scoped Prog

/-! ### Placements -/

def uGad : Fin 21 → Fin 120 := ![42, 13, 14, 15, 18, 23, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
def uMvG1 : Fin 5 → Fin 120 := ![50, 43, 52, 53, 23]
def uFillG : Fin 3 → Fin 120 := ![43, 52, 38]
def uMvG2 : Fin 5 → Fin 120 := ![50, 43, 52, 53, 38]
def uMM0 : Fin 59 → Fin 120 := ![51, 7, 1, 13, 14, 15, 16, 17, 19, 30, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]
def uA0 : Fin 28 → Fin 120 := ![39, 51, 8, 13, 31, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74]
def uMM1 : Fin 59 → Fin 120 := ![51, 7, 2, 13, 14, 15, 16, 17, 20, 32, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]
def uA1 : Fin 28 → Fin 120 := ![40, 51, 9, 13, 33, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74]
def uMulK : Fin 38 → Fin 120 := ![51, 7, 4, 13, 14, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84]
def uAK : Fin 28 → Fin 120 := ![41, 51, 12, 13, 14, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74]
def uFH : Fin 3 → Fin 120 := ![47, 52, 37]
def uAH : Fin 28 → Fin 120 := ![51, 41, 47, 13, 14, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74]
def uBin : Fin 53 → Fin 120 := ![44, 1, 39, 10, 48, 43, 13, 14, 15, 19, 21, 22, 23, 24, 25, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]
def uBits : Fin 13 → Fin 120 := ![45, 49, 13, 14, 15, 27, 28, 52, 53, 54, 55, 56, 57]
def uBgg : Fin 72 → Fin 120 := ![46, 45, 3, 11, 7, 42, 13, 14, 15, 16, 21, 23, 26, 29, 52, 53, 54, 55, 56, 57, 58, 59, 17, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108]
def uCT0 : Fin 5 → Fin 120 := ![44, 0, 52, 53, 34]
def uCT1 : Fin 5 → Fin 120 := ![39, 0, 52, 53, 30]
def uCT2 : Fin 5 → Fin 120 := ![40, 0, 52, 53, 32]
def uCT3 : Fin 5 → Fin 120 := ![46, 0, 52, 53, 36]
def uCT4 : Fin 5 → Fin 120 := ![41, 0, 52, 53, 15]
set_option maxRecDepth 100000 in
theorem uGad_inj : Function.Injective uGad := by decide
set_option maxRecDepth 100000 in
theorem uMvG1_inj : Function.Injective uMvG1 := by decide
set_option maxRecDepth 100000 in
theorem uFillG_inj : Function.Injective uFillG := by decide
set_option maxRecDepth 100000 in
theorem uMvG2_inj : Function.Injective uMvG2 := by decide
set_option maxRecDepth 100000 in
theorem uMM0_inj : Function.Injective uMM0 := by decide
set_option maxRecDepth 100000 in
theorem uA0_inj : Function.Injective uA0 := by decide
set_option maxRecDepth 100000 in
theorem uMM1_inj : Function.Injective uMM1 := by decide
set_option maxRecDepth 100000 in
theorem uA1_inj : Function.Injective uA1 := by decide
set_option maxRecDepth 100000 in
theorem uMulK_inj : Function.Injective uMulK := by decide
set_option maxRecDepth 100000 in
theorem uAK_inj : Function.Injective uAK := by decide
set_option maxRecDepth 100000 in
theorem uFH_inj : Function.Injective uFH := by decide
set_option maxRecDepth 100000 in
theorem uAH_inj : Function.Injective uAH := by decide
set_option maxRecDepth 100000 in
theorem uBin_inj : Function.Injective uBin := by decide
set_option maxRecDepth 100000 in
theorem uBits_inj : Function.Injective uBits := by decide
set_option maxRecDepth 100000 in
theorem uBgg_inj : Function.Injective uBgg := by decide
set_option maxRecDepth 100000 in
theorem uCT0_inj : Function.Injective uCT0 := by decide
set_option maxRecDepth 100000 in
theorem uCT1_inj : Function.Injective uCT1 := by decide
set_option maxRecDepth 100000 in
theorem uCT2_inj : Function.Injective uCT2 := by decide
set_option maxRecDepth 100000 in
theorem uCT3_inj : Function.Injective uCT3 := by decide
set_option maxRecDepth 100000 in
theorem uCT4_inj : Function.Injective uCT4 := by decide

/-! ### The phases -/

/-- The gadget words: `G̲` on `42`, `Γ.G` on `43`. -/
def gadPh : Prog 120 :=
  map uGad gadP ⨾ cp 43 24 ⨾ cp 50 42 ⨾ map uMvG1 mvP ⨾ map uFillG (fillP false) ⨾ cp 50 42 ⨾
    map uMvG2 mvP ⨾ clr 50

/-- `c₀` on `39`. -/
def c0Ph : Prog 120 := map uMM0 matMulP ⨾ map uA0 addRWP ⨾ clr 51

/-- `c₁` on `40`. -/
def c1Ph : Prog 120 := map uMM1 matMulP ⨾ map uA1 addRWP ⨾ clr 51

/-- `κ` on `41`. -/
def kapPh : Prog 120 :=
  map uMulK mulRWP ⨾ map uAK addRWP ⨾ clr 51 ⨾ cp 47 15 ⨾ sin true 47 ⨾ map uFH (fillP false) ⨾
    ifBit 6 (map uAH addRWP ⨾ cp 41 51 ⨾ clr 51) (nop 51) ⨾ clr 47

/-- The `Ψᵢ` on `44`. -/
def psiPh : Prog 120 := cp 44 34 ⨾ cp 48 5 ⨾ map uBin binMulP ⨾ clr 48

/-- The bits `ψ_j` on `45`. -/
def zPh : Prog 120 := cp 45 35 ⨾ cp 49 44 ⨾ map uBits coefBitsP ⨾ clr 49

/-- The encodings `c_j` on `46`. -/
def cjPh : Prog 120 := cp 46 36 ⨾ map uBgg bggEncP

/-- The fields shifted into the output register. -/
def ctPh : Prog 120 :=
  map uCT0 mvP ⨾ map uCT1 mvP ⨾ map uCT2 mvP ⨾ map uCT3 mvP ⨾ map uCT4 mvP

/-- **The deterministic core of `Enc`.** -/
def encCoreP : Prog 120 := gadPh ⨾ c0Ph ⨾ c1Ph ⨾ kapPh ⨾ psiPh ⨾ zPh ⨾ cjPh ⨾ ctPh

theorem noGrow_encCoreP : encCoreP.NoGrow := rfl
set_option maxRecDepth 100000 in
theorem wf_encCoreP : encCoreP.WF := wf_of_wfB (by decide)

/-! ### Placed programs with several outputs -/

theorem run_map_upd2 {n m : ℕ} {u : Fin n → Fin m} (hu : Function.Injective u) (p : Prog n)
    (s : Store m) (a b : Fin n) (va vb : List Bool)
    (h : run p (s ∘ u) = Function.update (Function.update (s ∘ u) a va) b vb) :
    run (map u p) s = Function.update (Function.update s (u a) va) (u b) vb := by
  rw [run_map hu, h, extend_update hu, extend_update hu, extend_comp_self]

theorem run_map_upd3 {n m : ℕ} {u : Fin n → Fin m} (hu : Function.Injective u) (p : Prog n)
    (s : Store m) (a b c : Fin n) (va vb vc : List Bool)
    (h : run p (s ∘ u) = Function.update (Function.update (Function.update (s ∘ u) a va) b vb) c vc) :
    run (map u p) s = Function.update (Function.update (Function.update s (u a) va) (u b) vb) (u c) vc := by
  rw [run_map hu, h, extend_update hu, extend_update hu, extend_update hu, extend_comp_self]

theorem run_map_upd4 {n m : ℕ} {u : Fin n → Fin m} (hu : Function.Injective u) (p : Prog n)
    (s : Store m) (a b c d : Fin n) (va vb vc vd : List Bool)
    (h : run p (s ∘ u) = Function.update (Function.update (Function.update (Function.update (s ∘ u)
      a va) b vb) c vc) d vd) :
    run (map u p) s = Function.update (Function.update (Function.update (Function.update s (u a) va)
      (u b) vb) (u c) vc) (u d) vd := by
  rw [run_map hu, h, extend_update hu, extend_update hu, extend_update hu, extend_update hu,
    extend_comp_self]

variable {N K k : ℕ}

/-! ### The gadget words -/

theorem gsw_reg (X G : List Bool) {m : ℕ} (hX : X.length = 4 * m) (hG : G.length = 2 * m) :
    ((((X ++ takeD (2 * m) G).drop (2 * m) ++ List.replicate m false).drop m ++ takeD m G).drop m) =
      G ++ (List.replicate m false ++ G.take m) := by
  rw [takeD_of_length' hG, takeD_eq_take (by omega)]
  have h1 : (X ++ G).drop (2 * m) = X.drop (2 * m) ++ G := List.drop_append_of_le_length (by omega)
  have hX2 : (X.drop (2 * m)).length = 2 * m := by simp; omega
  have h2 : (X.drop (2 * m) ++ G ++ List.replicate m false).drop m =
      (X.drop (2 * m)).drop m ++ (G ++ List.replicate m false) := by
    rw [List.append_assoc, List.drop_append_of_le_length (by omega)]
  have hX3 : ((X.drop (2 * m)).drop m).length = m := by simp; omega
  rw [h1, h2, List.append_assoc, List.drop_left' hX3, List.append_assoc]

set_option maxHeartbeats 8000000 in
theorem run_gadPh (S : Store 120) (hS : ∀ i : Fin 120, 50 ≤ i.val → S i = [])
    (hK : (S 13).length = K) (hN : (S 14).length = N) (hNK : (S 15).length = N * K)
    (hk : (S 18).length = k) (hR : (S 23).length = 2 * k * (N * K))
    (h24 : (S 24).length = 4 * (k * (N * K))) (h38 : (S 38).length = k * (N * K)) :
    run gadPh S = Function.update (Function.update S 42 (gadW N K k)) 43 (gswW N K k) := by
  simp only [gadPh, run_seq, run_copy, run_clear]
  rw [run_gadP_map uGad_inj (K := K) (N := N) (k' := k) _ ?_ ?_ ?_ ?_ ?_ ?_]
  rw [run_mvP_map uMvG1_inj _ ?_ ?_, run_fillP_map uFillG_inj _ _ ?_, run_mvP_map uMvG2_inj _ ?_ ?_]
  · have hg := length_gadW N K k
    have e := gsw_reg (S 24) (gadW N K k) (m := k * (N * K)) h24 (by rw [hg]; ring)
    rw [gswW_eq]
    funext t
    fin_cases t <;> simp [uGad, uMvG1, uFillG, uMvG2, hS, hR, h38, show 2 * k * (N * K) = 2 * (k * (N * K)) by ring, e]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [uGad, hS] at hi ⊢)
    | simp [uGad, uMvG1, uFillG, uMvG2, hS, hK, hN, hNK, hk, hR]

/-! ### `c₀`, `c₁`, `κ` -/

set_option maxHeartbeats 8000000 in
theorem run_c0Ph {d : ℕ} (S : Store 120) (hS : ∀ i : Fin 120, 51 ≤ i.val → S i = [])
    (hK : (S 13).length = K) (hN : (S 14).length = N) (hNK : (S 15).length = N * K)
    (h16 : (S 16).length = 1) (h17 : (S 17).length = 1) (hd : (S 19).length = d)
    (h30 : (S 30).length = 1 * d * (N * K)) (h31 : (S 31).length = d * N)
    (hs : (S 7).length = N * K) (hB : (S 1).length = d * (N * K)) (he : (S 8).length = d * (N * K)) :
    run c0Ph S = Function.update S 39 (addRW (d * N) K (matMulW N K 1 1 d (S 7) (S 1)) (S 8)) := by
  simp only [c0Ph, run_seq, run_clear]
  rw [run_matMulP_map uMM0_inj (K := K) (N := N) (m := 1) (n := 1) (l := d) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_, run_addRWP_map uA0_inj (K := K) (N := d * N) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    fin_cases t <;> simp [uMM0, uA0, hS]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [uMM0, uA0, hS] at hi ⊢)
    | (simp [uMM0, uA0, hS, hK, hN, hNK, h16, h17, hd, h30, h31, hs, hB, he, length_matMulW]; done)
    | (simp [uMM0, uA0, hS, hK, hN, hNK, h16, h17, hd, h30, h31, hs, hB, he, length_matMulW]; ring)

set_option maxHeartbeats 8000000 in
theorem run_c1Ph {T : ℕ} (S : Store 120) (hS : ∀ i : Fin 120, 51 ≤ i.val → S i = [])
    (hK : (S 13).length = K) (hN : (S 14).length = N) (hNK : (S 15).length = N * K)
    (h16 : (S 16).length = 1) (h17 : (S 17).length = 1) (hT : (S 20).length = T)
    (h32 : (S 32).length = 1 * T * (N * K)) (h33 : (S 33).length = T * N)
    (hs : (S 7).length = N * K) (hB : (S 2).length = T * (N * K)) (he : (S 9).length = T * (N * K)) :
    run c1Ph S = Function.update S 40 (addRW (T * N) K (matMulW N K 1 1 T (S 7) (S 2)) (S 9)) := by
  simp only [c1Ph, run_seq, run_clear]
  rw [run_matMulP_map uMM1_inj (K := K) (N := N) (m := 1) (n := 1) (l := T) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_, run_addRWP_map uA1_inj (K := K) (N := T * N) _ ?_ ?_ ?_ ?_ ?_]
  · funext t
    fin_cases t <;> simp [uMM1, uA1, hS]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [uMM1, uA1, hS] at hi ⊢)
    | (simp [uMM1, uA1, hS, hK, hN, hNK, h16, h17, hT, h32, h33, hs, hB, he, length_matMulW]; done)
    | (simp [uMM1, uA1, hS, hK, hN, hNK, h16, h17, hT, h32, h33, hs, hB, he, length_matMulW]; ring)

/-- The word of `κ` the phase computes. -/
def kapW (N K : ℕ) (sw pw ew bw zw hw : List Bool) : List Bool :=
  let k0 := addRW N K (mulRW N K sw pw) ew
  let H := (((zw ++ [true]).tail ++ List.replicate hw.length false).drop hw.length)
  if hd bw = true then addRW N K k0 H else k0

set_option maxHeartbeats 8000000 in
theorem run_kapPh (S : Store 120) (hS : ∀ i : Fin 120, 51 ≤ i.val → S i = []) (h47 : S 47 = [])
    (hK : (S 13).length = K) (hN : (S 14).length = N) (hNK : (S 15).length = N * K)
    (hs : (S 7).length = N * K) (hp : (S 4).length = N * K) (he : (S 12).length = N * K) :
    run kapPh S = Function.update S 41 (kapW N K (S 7) (S 4) (S 12) (S 6) (S 15) (S 37)) := by
  have hk0 : (addRW N K (mulRW N K (S 7) (S 4)) (S 12)).length = N * K :=
    length_addRW N K (length_mulRW N K _ _) _
  simp only [kapPh, run_seq, run_clear, run_copy, run_sin, run_ifBit]
  rw [run_mulRWP_map uMulK_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_,
    run_addRWP_map uAK_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_, run_fillP_map uFH_inj _ _ ?_]
  · by_cases hb : hd (S 6) = true
    · simp only [uMulK, uAK, uFH, Function.update_apply, Matrix.cons_val_zero, hb, ↓reduceIte,
        show (6 : Fin 120) ≠ 47 by decide, show (6 : Fin 120) ≠ 51 by decide,
        show (6 : Fin 120) ≠ 41 by decide]
      rw [run_addRWP_map uAH_inj (K := K) (N := N) _ ?_ ?_ ?_ ?_ ?_]
      · funext t
        fin_cases t <;> simp [uMulK, uAK, uFH, uAH, hS, h47, kapW, hb]
      all_goals first
        | (intro i hi; fin_cases i <;> simp [uAH, hS] at hi ⊢)
        | (simp [uMulK, uAK, uFH, uAH, hS, hK, hN, hNK, hk0, hb]; done)
    · simp only [uMulK, uAK, uFH, Function.update_apply, Matrix.cons_val_zero, hb, ↓reduceIte,
        show (6 : Fin 120) ≠ 47 by decide, show (6 : Fin 120) ≠ 51 by decide,
        show (6 : Fin 120) ≠ 41 by decide, run_nop]
      funext t
      fin_cases t <;> simp [uMulK, uAK, uFH, hS, h47, kapW, hb]
  all_goals first
    | (intro i hi; fin_cases i <;> simp [uMulK, uAK, hS] at hi ⊢)
    | (simp [uMulK, uAK, uFH, hS, hK, hN, hNK, hs, hp, he, length_mulRW]; done)

/-! ### The `Ψᵢ`, the bits, the encodings -/

set_option maxHeartbeats 8000000 in
theorem run_psiPh {d L : ℕ} (S : Store 120) (hS : ∀ i : Fin 120, 52 ≤ i.val → S i = [])
    (h48 : S 48 = []) (hK : (S 13).length = K) (hN : (S 14).length = N)
    (hNK : S 15 = List.replicate (N * K) false) (hd : (S 19).length = d) (hL : (S 21).length = L)
    (h23 : S 23 = List.replicate (L * (N * K)) false)
    (h24 : S 24 = List.replicate (2 * L * (N * K)) false) (h25 : (S 25).length = 2 * L * N)
    (hG : (S 43).length = 2 * L * (N * K)) :
    run psiPh S = Function.update (Function.update S 44
      ((Prog.iStepB N K d L (S 1) (S 39) (S 43))^[(S 22).length] (S 34, S 10, S 5)).1) 10
      ((Prog.iStepB N K d L (S 1) (S 39) (S 43))^[(S 22).length] (S 34, S 10, S 5)).2.1 := by
  simp only [psiPh, run_seq, run_copy, run_clear]
  set T := Function.update (Function.update S 44 (S 34)) 48 (Function.update S 44 (S 34) 5) with hT
  have hb := run_binMulP (N := N) (K := K) (d := d) (L := L) (T ∘ uBin)
    (fun i hi => by fin_cases i <;> simp [uBin, hT, hS] at hi ⊢)
    (by simp [uBin, hT, hK]) (by simp [uBin, hT, hN]) (by simp [uBin, hT, hNK])
    (by simp [uBin, hT, hd]) (by simp [uBin, hT, hL]) (by simp [uBin, hT, h23])
    (by simp [uBin, hT, h24]) (by simp [uBin, hT, h25]) (by simp [uBin, hT, hG])
  rw [run_map_upd3 uBin_inj _ _ 0 3 4 _ _ _ hb]
  funext t
  fin_cases t <;> simp [uBin, hT, h48]

set_option maxHeartbeats 8000000 in
theorem run_zPh {P : ℕ} (S : Store 120) (hS : ∀ i : Fin 120, 52 ≤ i.val → S i = [])
    (h49 : S 49 = []) (hK : (S 13).length = K) (hN : (S 14).length = N)
    (hNK : (S 15).length = N * K) (hP : (S 28).length = P) :
    run zPh S = Function.update S 45
      ((Prog.eStepC N K P)^[(S 27).length] (S 35, S 44)).1 := by
  simp only [zPh, run_seq, run_copy, run_clear]
  set T := Function.update (Function.update S 45 (S 35)) 49 (Function.update S 45 (S 35) 44) with hT
  have hb := run_coefBitsP (N := N) (K := K) (P := P) (T ∘ uBits)
    (fun i hi => by fin_cases i <;> simp [uBits, hT, hS] at hi ⊢)
    (by simp [uBits, hT, hK]) (by simp [uBits, hT, hN]) (by simp [uBits, hT, hNK])
    (by simp [uBits, hT, hP])
  rw [run_map_upd2 uBits_inj _ _ 0 1 _ _ hb]
  funext t
  fin_cases t <;> simp [uBits, hT, h49]

set_option maxHeartbeats 8000000 in
theorem run_cjPh {L : ℕ} (S : Store 120) (hS : ∀ i : Fin 120, 52 ≤ i.val → S i = [])
    (hK : (S 13).length = K) (hN : (S 14).length = N) (hNK : (S 15).length = N * K)
    (h16 : (S 16).length = 1) (h17 : (S 17).length = 1) (hL : (S 21).length = L)
    (h23 : (S 23).length = 1 * L * (N * K)) (h26 : (S 26).length = L * N)
    (hs : (S 7).length = N * K) (hg : (S 42).length = L * N * K) :
    run cjPh S = Function.update (Function.update (Function.update (Function.update S 46
      ((Prog.jStepE N K L (S 7) (S 42))^[(S 29).length] (S 36, S 45, S 3, S 11)).1) 45
      ((Prog.jStepE N K L (S 7) (S 42))^[(S 29).length] (S 36, S 45, S 3, S 11)).2.1) 3
      ((Prog.jStepE N K L (S 7) (S 42))^[(S 29).length] (S 36, S 45, S 3, S 11)).2.2.1) 11
      ((Prog.jStepE N K L (S 7) (S 42))^[(S 29).length] (S 36, S 45, S 3, S 11)).2.2.2 := by
  simp only [cjPh, run_seq, run_copy]
  set T := Function.update S 46 (S 36) with hT
  have hb := run_bggEncP (N := N) (K := K) (L := L) (T ∘ uBgg)
    (fun i hi => by fin_cases i <;> simp [uBgg, hT, hS] at hi ⊢)
    (by simp [uBgg, hT, hK]) (by simp [uBgg, hT, hN]) (by simp [uBgg, hT, hNK])
    (by simp [uBgg, hT, h16]) (by simp [uBgg, hT, h17]) (by simp [uBgg, hT, hL])
    (by simp [uBgg, hT, h23]) (by simp [uBgg, hT, h26]) (by simp [uBgg, hT, hs])
    (by simp [uBgg, hT, hg])
  rw [run_map_upd4 uBgg_inj _ _ 0 1 2 3 _ _ _ _ hb]
  funext t
  fin_cases t <;> simp [uBgg, hT]

/-- The output register after shifting the fields. -/
theorem run_ctPh_out (S : Store 120) (h52 : S 52 = []) (h53 : S 53 = []) :
    (run ctPh S) 0 =
      (((((S 0 ++ takeD (S 34).length (S 44)).drop (S 34).length ++
        takeD (S 30).length (S 39)).drop (S 30).length ++
        takeD (S 32).length (S 40)).drop (S 32).length ++
        takeD (S 36).length (S 46)).drop (S 36).length ++
        takeD (S 15).length (S 41)).drop (S 15).length := by
  simp only [ctPh, run_seq]
  rw [run_mvP_map uCT0_inj _ (by simp [uCT0, h52]) (by simp [uCT0, h53]),
    run_mvP_map uCT1_inj _ (by simp [uCT1, uCT0, h52]) (by simp [uCT1, uCT0, h53]),
    run_mvP_map uCT2_inj _ (by simp [uCT2, uCT1, uCT0, h52]) (by simp [uCT2, uCT1, uCT0, h53]),
    run_mvP_map uCT3_inj _ (by simp [uCT3, uCT2, uCT1, uCT0, h52])
      (by simp [uCT3, uCT2, uCT1, uCT0, h53]),
    run_mvP_map uCT4_inj _ (by simp [uCT4, uCT3, uCT2, uCT1, uCT0, h52])
      (by simp [uCT4, uCT3, uCT2, uCT1, uCT0, h53])]
  simp [uCT0, uCT1, uCT2, uCT3, uCT4]

end AdvancedEncryption.DualUse.Prog
