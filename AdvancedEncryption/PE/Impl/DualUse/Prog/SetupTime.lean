import PE.Impl.DualUse.Prog.Chi
import SigabaNeo.Lib.Machines.Prog.SampleTime
import SigabaNeo.Lib.Machines.Inline.Regions

/-!
# Time bounds of the setup programs

Explicit bounds on `XProg.timeBoundT` of the setup programs of the reductions, from the shape
bounds of `SigabaNeo.Lib.Machines.Prog.SampleTime` (`ATB`: from `x` bits on tape `0` and `S` on
the other tapes, a block costs at most `T x S`, appends at most `a` bits and grows its scratch by at
most `s`):

* the blocks: `atb_coinAp`, `atb_bitAp0`, `atb_coinsF`, `atb_zerosF`, `atb_entB`, `atb_entF`,
  `atb_repF` (counted loops, `countT`);
* `atb_tail5P` and **`time_setup5P`**: from the bounds `a`, `b` of the instance word and of the
  date (the component layout `io2 a b 0`), `timeBoundT (setup5P hk c) (io2 a b 0) ≤ time5 hk c a b`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.XProg Matrix
  AdvancedEncryption.RingBTVW Cslib Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

/-! ### Combinators -/

/-- Monotone time functions. -/
def Mono2 (T : ℕ → ℕ → ℕ) : Prop := ∀ x x' S S', x ≤ x' → S ≤ S' → T x S ≤ T x' S'

theorem ATB.seq2 {p q : XProg 7} {S₁ S₂ a s b u : ℕ} {T U : ℕ → ℕ → ℕ}
    (hp : ATB p 0 S₁ a s T) (hq : ATB q 0 S₂ b u U) :
    ATB (XProg.seq p q) 0 (max S₁ S₂) (a + b) (s + u) (fun x S => T x S + U (x + a) (S + s)) :=
  (hp.mono (le_max_left _ _) le_rfl le_rfl fun _ _ _ => le_rfl).seq
    (hq.mono (le_max_right _ _) le_rfl le_rfl fun _ _ _ => le_rfl)

theorem mono2_seq {T U : ℕ → ℕ → ℕ} (a s : ℕ) (hT : Mono2 T) (hU : Mono2 U) :
    Mono2 (fun x S => T x S + U (x + a) (S + s)) := fun x x' S S' hx hS =>
  Nat.add_le_add (hT x x' S S' hx hS) (hU _ _ _ _ (by omega) (by omega))

theorem mono2_affine (u v w : ℕ) : Mono2 (fun x S => u * (x + S) + v) := fun x x' S S' hx hS =>
  Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _

/-! ### Blocks -/

/-- The time of appending one bit. -/
def tBit (x S : ℕ) : ℕ := 2 * (x + S + 1) + 3

/-- The time of appending one fair bit. -/
def tCoin (x S : ℕ) : ℕ := 6 * (x + S) + 16

theorem mono_tBit : Mono2 tBit := fun x x' S S' hx hS => by unfold tBit; omega

theorem mono_tCoin : Mono2 tCoin := fun x x' S S' hx hS => by unfold tCoin; omega

theorem atb_bitAp0 (b : Bool) : ATB (bitAp 0 b) (0 : Fin 7) 0 1 0 tBit :=
  ATB.prim _ fun x S _ i => by
    simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega

theorem atb_coinAp : ATB (coinAp 0 2) (0 : Fin 7) 1 1 0 tCoin := by
  have h1 := ATB.coin (r := (0 : Fin 7)) (i := 2) (by decide)
  have h2 : ATB (prog (.prim (.snocHead 0 2))) (0 : Fin 7) 0 1 0 tBit :=
    ATB.prim _ fun x S _ i => by
      simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega
  have h3 : ATB (prog (.prim (.clear 2))) (0 : Fin 7) 0 0 0 tBit :=
    ATB.prim _ fun x S _ i => by
      simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega
  have h23 : ATB (prog (.seq (.prim (.snocHead 0 2)) (.prim (.clear 2)))) (0 : Fin 7) 0 (1 + 0)
      (0 + 0) (fun x S => tBit x S + tBit (x + 1) (S + 0)) := fun x S hS => h2.seq h3 x S hS
  refine (ATB.seq2 h1 h23).mono (by simp) le_rfl le_rfl fun x S _ => ?_
  simp only [tBit, tCoin]; omega

/-- The time of `n` fair bits. -/
def tCoins (n : ℕ) : ℕ → ℕ → ℕ := countT n 1 0 tCoin

/-- The time of `n` zeros. -/
def tZeros (n : ℕ) : ℕ → ℕ → ℕ := countT n 1 0 tBit

theorem atb_coinsF (n : ℕ) : ATB (coinsF n) (0 : Fin 7) (max 1 n) n 0 (tCoins n) :=
  (ATB.count (t := 3) (c := 4) (by decide) (by decide) (by decide) atb_coinAp
    (preserves_coinAp (by decide) (by decide)) mono_tCoin n).mono le_rfl (by simp) (by simp)
    fun _ _ _ => le_rfl

theorem atb_zerosF (n : ℕ) : ATB (zerosF n) (0 : Fin 7) (max 0 n) n 0 (tZeros n) :=
  (ATB.count (t := 3) (c := 4) (by decide) (by decide) (by decide) (atb_bitAp0 false)
    (preserves_bitAp _ (by decide)) mono_tBit n).mono le_rfl (by simp) (by simp)
    fun _ _ _ => le_rfl

theorem mono_tCoins (n : ℕ) : Mono2 (tCoins n) := countT_mono mono_tCoin

theorem mono_tZeros (n : ℕ) : Mono2 (tZeros n) := countT_mono mono_tBit

/-- The time of a binary ring element. -/
def tEntB (N K : ℕ) (x S : ℕ) : ℕ := tCoin x S + tZeros (N * K - 1) (x + 1) (S + 0)

theorem atb_entB (N K : ℕ) :
    ATB (entB N K) (0 : Fin 7) (max 1 (max 0 (N * K - 1))) (1 + (N * K - 1)) (0 + 0) (tEntB N K) :=
  ATB.seq2 atb_coinAp (atb_zerosF _)

theorem mono_tEntB (N K : ℕ) : Mono2 (tEntB N K) :=
  mono2_seq 1 0 mono_tCoin (mono_tZeros _)

/-- The time of a flooding coefficient. -/
def tEntF (K w : ℕ) (x S : ℕ) : ℕ := tCoins (min w K) x S + tZeros (K - w) (x + min w K) (S + 0)

theorem atb_entF (K w : ℕ) :
    ATB (entF K w) (0 : Fin 7) (max (max 1 (min w K)) (max 0 (K - w))) (min w K + (K - w)) (0 + 0)
      (tEntF K w) :=
  ATB.seq2 (atb_coinsF _) (atb_zerosF _)

theorem mono_tEntF (K w : ℕ) : Mono2 (tEntF K w) :=
  mono2_seq _ 0 (mono_tCoins _) (mono_tZeros _)

theorem atb_repF {body : XProg 7} {S₀ a s : ℕ} {T : ℕ → ℕ → ℕ} (hb : ATB body (0 : Fin 7) S₀ a s T)
    (hc : body.Preserves 6) (hT : Mono2 T) (n : ℕ) :
    ATB (repF n body) (0 : Fin 7) (max S₀ n) (n * a) (n * s) (countT n a s T) :=
  ATB.count (t := 5) (c := 6) (by decide) (by decide) (by decide) hb hc hT n

theorem preserves6_entB (N K : ℕ) : (entB N K).Preserves 6 :=
  ⟨preserves_coinAp (by decide) (by decide), preserves_zerosF _ (by decide)⟩

theorem preserves6_entF (K w : ℕ) : (entF K w).Preserves 6 :=
  ⟨preserves_coinsF _ (by decide), preserves_zerosF _ (by decide)⟩

/-! ### Appending the date -/

/-- The time of appending tape `1` (at most `m` bits) to tape `0`. -/
def tApp (x S m : ℕ) : ℕ :=
  (2 * (x + S) + 3) + ((2 * (x + S) + 3) + (m * (2 * (x + m + S) + 3 +
    (tBit (x + m) S + tBit (x + m + 1) S) + 1) + 2)) +
    (2 * (x + m + S) + 3) + (2 * (x + m + S) + 3)

theorem appendTape_bounds {ℓ : Fin 7 → ℕ} {x S m : ℕ} (hm : m ≤ S) (hℓ : ℓ ≤ shp 0 x S)
    (h1 : ℓ 1 ≤ m) :
    timeBoundT (appendTapeP 0 1 3 4) ℓ ≤ tApp x S m ∧
      lenBoundT (appendTapeP 0 1 3 4) ℓ ≤ shp 0 (x + m) S := by
  have hb2 : ATB (prog (.prim (.snocHead 0 3))) (0 : Fin 7) 0 1 0 tBit :=
    ATB.prim _ fun x S _ i => by
      simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega
  have hb3 : ATB (prog (.prim (.tail 3))) (0 : Fin 7) 0 0 0 tBit :=
    ATB.prim _ fun x S _ i => by
      simp only [Prim.lenT, shp, Function.update_apply]; split_ifs <;> omega
  have hb := hb2.seq hb3
  set ℓ1 := (Prim.copy 3 1).lenT ℓ
  have hℓ1 : ℓ1 ≤ shp 0 x S := fun i => by
    simp only [ℓ1, Prim.lenT, Function.update_apply]
    split_ifs with h
    · subst h; simp only [shp]; have := h1; simp; omega
    · exact hℓ i
  have hf := forN_bounds (t := 1) (c := 4) (by decide) hb
    ⟨preserves_prim (by simp [Prim.writes]), preserves_prim (by simp [Prim.writes])⟩
    (mono2_seq 1 0 mono_tBit mono_tBit) (le_refl 0 |>.trans (Nat.zero_le S)) hm hℓ1
    (by simp only [ℓ1, Prim.lenT, Function.update_apply]; simpa using h1)
  have hs0 := supB_shp (0 : Fin 7) x S
  have hs1 := supB_mono hℓ
  set ℓ2 := lenBoundT (forN 4 1 (XProg.seq (prog (.prim (.snocHead 0 3))) (prog (.prim (.tail 3))))) ℓ1
  have hℓ2 : ℓ2 ≤ shp 0 (x + m) S := hf.2.trans (shp_mono (by simp) (by simp))
  have hs2 := supB_mono hℓ2
  have hs3 := supB_shp (0 : Fin 7) (x + m) S
  have hℓ3 : (Prim.clear 3).lenT ℓ2 ≤ shp 0 (x + m) S := fun i => by
    simp only [Prim.lenT, Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hℓ2 i
  have hs4 := supB_mono hℓ3
  refine ⟨?_, ?_⟩
  · show timeBoundT (prog (.prim (.copy 3 1))) ℓ + (timeBoundT _ ℓ1 +
      (timeBoundT (prog (.prim (.clear 3))) ℓ2 +
        timeBoundT (prog (.prim (.clear 1))) ((Prim.clear 3).lenT ℓ2))) ≤ _
    rw [timeBoundT_prim, timeBoundT_prim, timeBoundT_prim]
    have := hf.1
    simp only [Nat.add_zero, Nat.mul_zero, Nat.mul_one, Nat.zero_add] at this
    simp only [Prim.pad, tApp]
    omega
  · show (Prim.clear 1).lenT ((Prim.clear 3).lenT ℓ2) ≤ _
    intro i
    show Function.update ((Prim.clear 3).lenT ℓ2) 1 0 i ≤ _
    rw [Function.update_apply]; split_ifs
    · exact Nat.zero_le _
    · exact hℓ3 i

/-! ### The setup of hybrid 5 -/

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The scratch bound needed by the random part of the secret of hybrid 5. -/
def s5 : ℕ := max (max 1 (N * K)) (max (max 1 (nW hk c)) (max (max (max 1 (max 0 (N * K - 1)))
  (nR hk c)) (max (max (max 1 (min c.w K)) (max 0 (K - c.w))) (nE (N := N) hk))))

/-- The time of the random part of the secret of hybrid 5. -/
def tTail5 (x S : ℕ) : ℕ :=
  tCoins (N * K) x S + (tCoins (nW hk c) (x + N * K) (S + 0) +
    (countT (nR hk c) (1 + (N * K - 1)) (0 + 0) (tEntB N K) (x + N * K + nW hk c) (S + 0 + 0) +
      countT (nE (N := N) hk) (min c.w K + (K - c.w)) (0 + 0) (tEntF K c.w)
        (x + N * K + nW hk c + nR hk c * (1 + (N * K - 1))) (S + 0 + 0 + nR hk c * (0 + 0))))

theorem atb_tail5P : ATB (tail5P hk c) (0 : Fin 7) (s5 hk c)
    (N * K + (nW hk c + (nR hk c * (1 + (N * K - 1)) + nE (N := N) hk * (min c.w K + (K - c.w)))))
    (0 + (0 + (nR hk c * (0 + 0) + nE (N := N) hk * (0 + 0)))) (tTail5 hk c) := by
  have h := ATB.seq2 (atb_coinsF (N * K)) (ATB.seq2 (atb_coinsF (nW hk c))
    (ATB.seq2 (atb_repF (atb_entB N K) (preserves6_entB N K) (mono_tEntB N K) (nR hk c))
      (atb_repF (atb_entF K c.w) (preserves6_entF K c.w) (mono_tEntF K c.w) (nE (N := N) hk))))
  refine h.mono le_rfl le_rfl le_rfl fun x S _ => le_of_eq ?_
  simp only [tTail5, Nat.add_assoc]

/-- **The time of the setup of hybrid 5**, from the bounds `a` of the instance word and `b` of the
date. -/
def time5 (a b : ℕ) : ℕ :=
  tApp a (max b (s5 hk c)) b + tTail5 hk c (a + b) (max b (s5 hk c))

theorem time_setup5P (a b : ℕ) :
    timeBoundT (setup5P hk c) (io2 (R := 5) a b 0) ≤ time5 hk c a b := by
  set S := max b (s5 hk c)
  have hℓ : io2 (R := 5) a b 0 ≤ shp (0 : Fin 7) a S := fun i => by
    simp only [io2, shp]; split_ifs <;> simp_all <;> omega
  obtain ⟨h1, h2⟩ := appendTape_bounds (le_max_left b _) hℓ (by simp [io2])
  show timeBoundT (appendTapeP 0 1 3 4) _ + timeBoundT (tail5P hk c) _ ≤ _
  exact Nat.add_le_add h1 ((atb_tail5P hk c).time (le_max_right _ _) h2)

end AdvancedEncryption.DualUse.Prog
