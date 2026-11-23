import PE.Impl.DualUse.ConcreteNoise
import PE.Impl.DualUse.Params.SimTrapNorm
import PE.Impl.DualUse.KeyBoxes

/-!
# The noise chain over variable sizes

The size and noise bounds of `Params/Sizes.lean` for variable `N`, `k`, `|Wd| = d`, flooding width
`w` and depth bound `D`, with every bound a power of two whose exponent is a variable bounded by
an arithmetic hypothesis. A configuration instantiates them with numerals: the hypotheses are then
inequalities between small numerals (`norm_num`), and no power of two with a large exponent is
evaluated.

With `k ≤ 2^a`, `N ≤ 2^n`:

* `|Col k| N ≤ 2^(a + n + 1)` (`WN_le`), `+ 1 ≤ 2^(a + n + 2)` (`WN1_le`);
* `modFactor ≤ 2^(2 (a + 3) + 10 (a + n + 2))` (`modFactor_le`, for `a ≥ 2`);
* `treeHeight ≤ a + n + 2` (`treeHeight_le`);
* `gswFactor ≤ 2^(m (a + n + 3) + a + n + 2)` with `m` the exponent of `modFactor`
  (`gswFactor_le`); `G^D ≤ 2^(g D)` (`gswPow_le`);
* `|rowBits| ≤ 2^(2a + n + 1)` (`R_le`), `|rowBits| WN + 1 ≤ 2^(r + w + 1)` (`RW_le`);
* the shifts of the trapdoors (`simTrapBound_le`, `realShift_le`) and the noise (`noise_ok`).
-/

namespace AdvancedEncryption.DualUse.Params.Gen

open SigabaNeo.Lattices SigabaNeo.Lattices.SLP AdvancedEncryption.RingBTVW
open AdvancedEncryption.DualUse.Concrete (pow_mul_le' pow_mul_le pow_le_pow' sum_bound)

variable {N k d a n : ℕ}

theorem card_col (k : ℕ) : Fintype.card (Col k) = 2 * k := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem WN_le (hk : k ≤ 2 ^ a) (hN : N ≤ 2 ^ n) {e : ℕ} (he : a + n + 1 ≤ e) :
    Fintype.card (Col k) * N ≤ 2 ^ e := by
  rw [card_col]
  have h : 2 * k * N ≤ 2 * 2 ^ a * 2 ^ n := Nat.mul_le_mul (Nat.mul_le_mul_left _ hk) hN
  refine h.trans (le_of_eq_of_le ?_ (pow_le_pow' he))
  rw [← pow_succ', ← pow_add]; congr 1; omega

theorem WN1_le (hk : k ≤ 2 ^ a) (hN : N ≤ 2 ^ n) {e : ℕ} (he : a + n + 2 ≤ e) :
    Fintype.card (Col k) * N + 1 ≤ 2 ^ e := by
  have h := WN_le hk hN (le_refl (a + n + 1))
  have h2 : (2 : ℕ) ^ (a + n + 2) = 2 * 2 ^ (a + n + 1) := by rw [← pow_succ']
  have h1 : 1 ≤ (2 : ℕ) ^ (a + n + 1) := Nat.one_le_two_pow
  exact (show Fintype.card (Col k) * N + 1 ≤ 2 ^ (a + n + 2) by omega).trans (pow_le_pow' he)

theorem modFactor_le (hk : k ≤ 2 ^ a) (hN : N ≤ 2 ^ n) (ha : 2 ≤ a) {e : ℕ}
    (he : 2 * (a + 3) + 10 * (a + n + 2) ≤ e) :
    modFactor (Fintype.card (Col k) * N) k ≤ 2 ^ e := by
  unfold modFactor
  have h1 : 4 * k + 14 ≤ 2 ^ (a + 3) := by
    have h4 : 4 ≤ 2 ^ a := (pow_le_pow' ha).trans' (by norm_num)
    rw [pow_add]; omega
  have h2 : (4 * k + 14) ^ 2 ≤ 2 ^ (2 * (a + 3)) := by
    calc (4 * k + 14) ^ 2 ≤ (2 ^ (a + 3)) ^ 2 := Nat.pow_le_pow_left h1 _
      _ = 2 ^ (2 * (a + 3)) := by rw [← pow_mul, mul_comm]
  have h3 : (Fintype.card (Col k) * N + 1) ^ 10 ≤ 2 ^ (10 * (a + n + 2)) := by
    calc (Fintype.card (Col k) * N + 1) ^ 10 ≤ (2 ^ (a + n + 2)) ^ 10 :=
          Nat.pow_le_pow_left (WN1_le hk hN le_rfl) _
      _ = 2 ^ (10 * (a + n + 2)) := by rw [← pow_mul, mul_comm]
  exact (pow_mul_le h2 h3).trans (pow_le_pow' he)

theorem treeHeight_le (hk : k ≤ 2 ^ a) (hN : N ≤ 2 ^ n) {e : ℕ} (he : a + n + 2 ≤ e) :
    treeHeight N k ≤ e := by
  unfold treeHeight
  refine Nat.clog_le_of_le_pow ?_
  have : Fintype.card ((Fin 2 × Fin k) × Fin N) = Fintype.card (Col k) * N := by
    rw [Fintype.card_prod, Fintype.card_fin]
  rw [this]
  exact WN1_le hk hN he

theorem gswFactor_le (hk : k ≤ 2 ^ a) (hN : N ≤ 2 ^ n) (ha : 2 ≤ a) {m g : ℕ}
    (hm : 2 * (a + 3) + 10 * (a + n + 2) ≤ m) (hg : m * (a + n + 3) + (a + n + 2) ≤ g) :
    gswFactor (Fintype.card (Col k) * N) N k ≤ 2 ^ g := by
  unfold gswFactor
  have h1 : modFactor (Fintype.card (Col k) * N) k ^ (treeHeight N k + 1) ≤
      2 ^ (m * (a + n + 3)) := by
    calc modFactor (Fintype.card (Col k) * N) k ^ (treeHeight N k + 1)
        ≤ (2 ^ m) ^ (treeHeight N k + 1) := Nat.pow_le_pow_left (modFactor_le hk hN ha hm) _
      _ ≤ (2 ^ m) ^ (a + n + 3) :=
          Nat.pow_le_pow_right (by positivity) (by have := treeHeight_le hk hN le_rfl; omega)
      _ = 2 ^ (m * (a + n + 3)) := by rw [← pow_mul]
  exact (pow_mul_le h1 (WN1_le hk hN le_rfl)).trans (pow_le_pow' hg)

/-- `G^n ≤ 2^t` for `n ≤ D` from `G ≤ 2^g` and `g D ≤ t`. -/
theorem gswPow_le {g D t : ℕ} (hG : gswFactor (Fintype.card (Col k) * N) N k ≤ 2 ^ g)
    (ht : g * D ≤ t) {m : ℕ} (hm : m ≤ D) :
    gswFactor (Fintype.card (Col k) * N) N k ^ m ≤ 2 ^ t :=
  calc gswFactor (Fintype.card (Col k) * N) N k ^ m
      ≤ gswFactor (Fintype.card (Col k) * N) N k ^ D :=
        Nat.pow_le_pow_right (gswFactor_pos _ N k) hm
    _ ≤ (2 ^ g) ^ D := Nat.pow_le_pow_left hG _
    _ = 2 ^ (g * D) := (pow_mul 2 g D).symm
    _ ≤ 2 ^ t := pow_le_pow' ht

theorem R_le (hk : k ≤ 2 ^ a) (hN : N ≤ 2 ^ n) {e : ℕ} (he : 2 * a + n + 1 ≤ e) :
    Fintype.card (Fin 1 × Col k × Fin k × Fin N) ≤ 2 ^ e := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc 1 * (2 * k * (k * N)) ≤ 1 * (2 * 2 ^ a * (2 ^ a * 2 ^ n)) := by gcongr
    _ = 2 ^ (2 * a + n + 1) := by
        rw [one_mul, ← pow_succ', ← pow_add, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ e := pow_le_pow' he

theorem RW_le (hk : k ≤ 2 ^ a) (hN : N ≤ 2 ^ n) {e : ℕ} (he : 3 * a + 2 * n + 3 ≤ e) :
    Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (Fintype.card (Col k) * N) + 1 ≤ 2 ^ e := by
  have h := pow_mul_le (R_le hk hN le_rfl) (WN_le hk hN le_rfl)
  have h2 : (2 : ℕ) ^ (2 * a + n + 1 + (a + n + 1) + 1) = 2 * 2 ^ (2 * a + n + 1 + (a + n + 1)) := by
    rw [← pow_succ']
  have h1 : 1 ≤ (2 : ℕ) ^ (2 * a + n + 1 + (a + n + 1)) := Nat.one_le_two_pow
  refine (show _ ≤ 2 ^ (2 * a + n + 1 + (a + n + 1) + 1) by omega).trans (pow_le_pow' ?_)
  omega

theorem card_trapCol_le (hk : k ≤ 2 ^ a) (ha : 1 ≤ a) {e : ℕ} (he : a + 3 ≤ e) :
    Fintype.card (DualUse.TrapCol k) ≤ 2 ^ e := by
  rw [Fintype.card_sum, Fintype.card_sum, card_col, Fintype.card_fin]
  have h2 : 2 ≤ 2 ^ a := (pow_le_pow' ha).trans' (by norm_num)
  refine (show 1 + (2 * k + 2 * k) ≤ 2 ^ (a + 3) by rw [pow_add]; omega).trans (pow_le_pow' he)

theorem E_le (hd : d ≤ 2 ^ a) (hN : N ≤ 2 ^ n) (w : ℕ) {e : ℕ} (he : a + n + w ≤ e) :
    Fintype.card (Fin d) * N * 2 ^ w ≤ 2 ^ e := by
  rw [Fintype.card_fin]
  exact (pow_mul_le (pow_mul_le hd hN) (le_refl (2 ^ w))).trans (pow_le_pow' he)

/-- **The shift of the simulated trapdoor** for predicates of depth at most `D`. -/
theorem simTrapBound_le {eWN eRW t E D m : ℕ} (hWN : Fintype.card (Col k) * N ≤ 2 ^ eWN)
    (hRW : Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (Fintype.card (Col k) * N) + 1 ≤ 2 ^ eRW)
    (hGD : gswFactor (Fintype.card (Col k) * N) N k ^ D ≤ 2 ^ t) (hm : m ≤ D)
    (hE : eWN + eRW + t ≤ E) : DualUse.simTrapBound N k m ≤ 2 ^ E := by
  have hGm : gswFactor (Fintype.card (Col k) * N) N k ^ m ≤ 2 ^ t :=
    (Nat.pow_le_pow_right (gswFactor_pos _ N k) hm).trans hGD
  unfold DualUse.simTrapBound
  exact (pow_mul_le hWN (pow_mul_le hRW hGm)).trans (pow_le_pow' (by omega))

/-- **The shift of the real trapdoor** (errors within `16`). -/
theorem realShift_le {eWN E : ℕ} (hWN : Fintype.card (Col k) * N ≤ 2 ^ eWN)
    (hE : 2 * eWN + 4 ≤ E) : (Fintype.card (Col k) * N) ^ 2 * 16 ≤ 2 ^ E := by
  have h : (Fintype.card (Col k) * N) ^ 2 * 16 ≤ (2 ^ eWN) ^ 2 * 2 ^ 4 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hWN 2) (le_refl _)
  rw [← pow_mul, ← pow_add] at h
  exact h.trans (pow_le_pow' (by omega))

/-- **The noise of a predicate of depth at most `D`** is below `q / 4` when the exponents add up
to at most `K - 6`. -/
theorem noise_ok {Attr : Type} [Fintype Attr] {K : ℕ} (hk : 2 ^ K < 2 ^ k) (w : ℕ)
    (f : SLP Attr × Wire Attr) {D : ℕ} (hf : SLP.depth f.1 f.2 ≤ D) (S : ℕ)
    {eWN eRW eGD eE eT eS : ℕ}
    (hWN : Fintype.card (Col k) * N ≤ 2 ^ eWN)
    (hRW : Fintype.card (Fin 1 × Col k × Fin k × Fin N) * (Fintype.card (Col k) * N) + 1 ≤ 2 ^ eRW)
    (hGD : gswFactor (Fintype.card (Col k) * N) N k ^ D ≤ 2 ^ eGD)
    (hE : Fintype.card (Fin d) * N * 2 ^ w ≤ 2 ^ eE)
    (hT : Fintype.card (DualUse.TrapCol k) * N * 2 ^ w ≤ 2 ^ eT)
    (hS : S ≤ 2 ^ eS) (hTE : eT ≤ eWN + eRW + eGD + eE)
    (hK : eWN + eRW + eGD + eE + eS + 6 ≤ K) :
    4 * DualUse.noiseBound (Wd := Fin d) (Wt := DualUse.TrapCol k) (N := N) hk (2 ^ w) S f + 2
      < 2 ^ K := by
  set M := eWN + eRW + eGD + eE + eS with hM
  have hRB := RingBTVW.noiseBound_le_of_depth_le (N := N) (Attr := Attr) hk
    (Fintype.card (Fin d) * N * 2 ^ w) S f hf
  have T1 : Fintype.card (Fin d) * N * 2 ^ w ≤ 2 ^ M := hE.trans (pow_le_pow' (by omega))
  have T2 : Fintype.card (Col k) * N * (Fintype.card (Fin d) * N * 2 ^ w) * S ≤ 2 ^ M :=
    (pow_mul_le (pow_mul_le hWN hE) hS).trans (pow_le_pow' (by omega))
  have T3 : Fintype.card (Col k) * N * ((Fintype.card (Fin 1 × Col k × Fin k × Fin N) *
      (Fintype.card (Col k) * N) + 1) * (gswFactor (Fintype.card (Col k) * N) N k ^ D *
        (Fintype.card (Fin d) * N * 2 ^ w))) * S ≤ 2 ^ M :=
    (pow_mul_le (pow_mul_le hWN (pow_mul_le hRW (pow_mul_le hGD hE))) hS).trans
      (pow_le_pow' (by omega))
  have T4 : Fintype.card (Fin d) * N * 2 ^ w * S ≤ 2 ^ M :=
    (pow_mul_le hE hS).trans (pow_le_pow' (by omega))
  have T5 : Fintype.card (DualUse.TrapCol k) * N * 2 ^ w * S ≤ 2 ^ M :=
    (pow_mul_le hT hS).trans (pow_le_pow' (by omega))
  have hsum := sum_bound _ _ _ _ _ (2 ^ M) T1 T2 T3 T4 T5 Nat.one_le_two_pow
  have e64 : 64 * (2 : ℕ) ^ M = 2 ^ (M + 6) := by rw [pow_add]; ring
  unfold DualUse.noiseBound
  calc 4 * (RingBTVW.noiseBound (N := N) hk (Fintype.card (Fin d) * N * 2 ^ w) S f +
        (Fintype.card (Fin d) * N * 2 ^ w * S +
          Fintype.card (DualUse.TrapCol k) * N * 2 ^ w * S)) + 2
      ≤ 4 * (Fintype.card (Fin d) * N * 2 ^ w +
          Fintype.card (Col k) * N * (Fintype.card (Fin d) * N * 2 ^ w) * S +
          Fintype.card (Col k) * N * ((Fintype.card (Fin 1 × Col k × Fin k × Fin N) *
            (Fintype.card (Col k) * N) + 1) * (gswFactor (Fintype.card (Col k) * N) N k ^ D *
              (Fintype.card (Fin d) * N * 2 ^ w))) * S +
          (Fintype.card (Fin d) * N * 2 ^ w * S +
            Fintype.card (DualUse.TrapCol k) * N * 2 ^ w * S)) + 2 := by
        gcongr
    _ < 64 * 2 ^ M := hsum
    _ = 2 ^ (M + 6) := e64
    _ ≤ 2 ^ K := pow_le_pow' (by omega)

/-! ### The abort probability -/

theorem card_coef_le (hd : d ≤ 2 ^ a) (hk : 1 + 4 * k ≤ 2 ^ a) (hN : N ≤ 2 ^ n) {e : ℕ}
    (he : a + 1 + n ≤ e) : Fintype.card (DualUse.Coef d (DualUse.TrapCol k) N) ≤ 2 ^ e := by
  rw [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_sum,
    Fintype.card_sum, Fintype.card_fin, card_col]
  have h1 : d + (1 + (2 * k + 2 * k)) ≤ 2 ^ (a + 1) := by rw [pow_succ]; omega
  exact (Nat.mul_le_mul h1 hN).trans (le_of_eq_of_le (by rw [← pow_add]) (pow_le_pow' (by omega)))

theorem four_τ_le (E : ℕ) : 4 * 2 ^ E + 1 ≤ 2 ^ (E + 3) := by
  rw [pow_add]
  have : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  omega

/-- The product of the abort bound, `|Coef| (4 τ + 1) 2^κ ≤ 2^B`, from the exponents. -/
theorem abort_prod {C c Eτ κ B : ℕ} (hC : C ≤ 2 ^ c) (h : c + (Eτ + 3) + κ ≤ B) :
    C * (4 * 2 ^ Eτ + 1) * 2 ^ κ ≤ 2 ^ B :=
  (pow_mul_le (pow_mul_le hC (four_τ_le Eτ)) (le_refl _)).trans (pow_le_pow' h)

end AdvancedEncryption.DualUse.Params.Gen
