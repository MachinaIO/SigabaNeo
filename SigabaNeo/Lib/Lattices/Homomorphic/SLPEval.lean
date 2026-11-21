import SigabaNeo.Lib.Lattices.Homomorphic.SLP
import SigabaNeo.Lib.Lattices.Homomorphic.NoiseBound

/-!
# Homomorphic evaluation of straight-line programs

The evaluation of `SigabaNeo.Lib.Lattices.Homomorphic.Eval` for programs with shared gates
(`SLP`): one joint run (`SLP.valueOf`) on states `HState` carrying a public key or ciphertext `A`,
the plaintext bit `x`, an encoding `c`, its error `e`, and a bound `bd` on that error. A NAND gate
sends `A` to `G − A_a G⁻¹(A_b)`, `x` to `1 − x_a x_b`, `c` and `e` to `−(c_a G⁻¹(A_b) + x_a c_b)`,
and `bd` to `WN · bd_a + bd_b` (`hstep`).

* **BGG+** (`slp_bgg_key_relation`): if every input has `c = s(A − x G) + e`, so has every wire.
* **Ring-GSW** (`slp_gsw_invariant`): if every input has `t A = x (t G) + e`, so has every wire.
* **Noise** (`slp_noise`): over `ℤ_q[X]/(X^N + 1)` with binary decompositions, if every input has a
  `0/1` plaintext and `rnorm e ≤ bd`, so has every wire.
-/

namespace SigabaNeo.Lattices

open Matrix

/-- The state of homomorphic evaluation at a wire. -/
structure HState (R : Type*) (r W : Type*) where
  /-- The public key (BGG+) or the ciphertext (Ring-GSW). -/
  A : Matrix r W R
  /-- The plaintext. -/
  x : R
  /-- The encoding (BGG+). -/
  c : Matrix (Fin 1) W R
  /-- The error. -/
  e : Matrix (Fin 1) W R
  /-- A bound on the error. -/
  bd : ℕ

namespace HState

variable {R : Type*} [CommRing R] {r W : Type*} [Fintype W] (Γ : GadgetMatrix R r W) (WN : ℕ)

/-- The state of the constant `1`. -/
def one : HState R r W := ⟨Γ.G, 1, 0, 0, 0⟩

/-- A NAND gate. -/
def hstep (u v : HState R r W) : HState R r W :=
  ⟨Γ.G - u.A * Γ.ginv v.A, 1 - u.x * v.x, -(u.c * Γ.ginv v.A + u.x • v.c),
    -(u.e * Γ.ginv v.A + u.x • v.e), WN * u.bd + v.bd⟩

end HState

open HState

variable {R : Type*} [CommRing R] {r W : Type*} [Fintype r] [Fintype W] (Γ : GadgetMatrix R r W)
  {ι : Type*} (WN : ℕ)

/-- **The BGG+ key relation for programs.** -/
theorem slp_bgg_key_relation (s : Matrix (Fin 1) r R) (inp : ι → HState R r W)
    (h : ∀ i, (inp i).c = s * ((inp i).A - (inp i).x • Γ.G) + (inp i).e) (p : SLP ι) (w : Wire ι) :
    (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).c =
      s * ((SLP.valueOf inp (one Γ) (hstep Γ WN) p w).A -
        (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).x • Γ.G) +
        (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).e := by
  refine SLP.valueOf_invariant inp (one Γ) (hstep Γ WN)
    (fun u => u.c = s * (u.A - u.x • Γ.G) + u.e) h (by simp [HState.one]) ?_ p w
  intro a b ha hb
  simp only [hstep]
  rw [ha, hb]
  have hG := Γ.mul_ginv b.A
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, hG, sub_smul, one_smul, smul_add, smul_sub, smul_smul]
  module

/-- **The Ring-GSW invariant for programs.** -/
theorem slp_gsw_invariant (t : Matrix (Fin 1) r R) (inp : ι → HState R r W)
    (h : ∀ i, t * (inp i).A = (inp i).x • (t * Γ.G) + (inp i).e) (p : SLP ι) (w : Wire ι) :
    t * (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).A =
      (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).x • (t * Γ.G) +
        (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).e := by
  refine SLP.valueOf_invariant inp (one Γ) (hstep Γ WN)
    (fun u => t * u.A = u.x • (t * Γ.G) + u.e) h (by simp [HState.one]) ?_ p w
  intro a b ha hb
  simp only [hstep]
  have hG := Γ.mul_ginv b.A
  have hstep' : t * (a.A * Γ.ginv b.A) = (a.x • (t * Γ.G) + a.e) * Γ.ginv b.A := by
    rw [← Matrix.mul_assoc, ha]
  rw [Matrix.mul_sub, hstep']
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hG, hb, smul_add, smul_smul,
    sub_smul, one_smul]
  module

omit [Fintype r] in
/-- The plaintexts are those of the ring evaluation. -/
theorem slp_x_eq (inp : ι → HState R r W) (p : SLP ι) (w : Wire ι) :
    (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).x = SLP.eval (fun i => (inp i).x) p w :=
  SLP.valueOf_map _ _ _ _ _ _ HState.x (fun _ => rfl) rfl (fun _ _ => rfl) p w

omit [Fintype r] in
/-- The public keys depend on the input public keys only. -/
theorem slp_A_eq (inp inp' : ι → HState R r W) (h : ∀ i, (inp i).A = (inp' i).A) (p : SLP ι)
    (w : Wire ι) :
    (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).A = (SLP.valueOf inp' (one Γ) (hstep Γ WN) p w).A := by
  have h1 := SLP.valueOf_map inp (one Γ) (hstep Γ WN) (fun i => (inp i).A) Γ.G
    (fun A B => Γ.G - A * Γ.ginv B) HState.A (fun _ => rfl) rfl (fun _ _ => rfl) p w
  have h2 := SLP.valueOf_map inp' (one Γ) (hstep Γ WN) (fun i => (inp' i).A) Γ.G
    (fun A B => Γ.G - A * Γ.ginv B) HState.A (fun _ => rfl) rfl (fun _ _ => rfl) p w
  rw [h1, h2]
  congr 1
  funext i
  exact h i

/-! ### Public keys and encodings, separately -/

/-- `EvalF` of a program: the public key at a wire. -/
def slpPK (Bj : ι → Matrix r W R) (p : SLP ι) (w : Wire ι) : Matrix r W R :=
  SLP.valueOf Bj Γ.G (fun A B => Γ.G - A * Γ.ginv B) p w

/-- The step of `EvalFX` on (public key, input, encoding). -/
def encStep (u v : Matrix r W R × R × Matrix (Fin 1) W R) : Matrix r W R × R × Matrix (Fin 1) W R :=
  (Γ.G - u.1 * Γ.ginv v.1, 1 - u.2.1 * v.2.1, -(u.2.2 * Γ.ginv v.1 + u.2.1 • v.2.2))

/-- `EvalFX` of a program: the encoding at a wire, knowing the inputs `x`. The same function
evaluates the errors. -/
def slpEnc (Bj : ι → Matrix r W R) (x : ι → R) (c : ι → Matrix (Fin 1) W R) (p : SLP ι) (w : Wire ι) :
    Matrix (Fin 1) W R :=
  (SLP.valueOf (fun j => (Bj j, x j, c j)) (Γ.G, 1, 0) (encStep Γ) p w).2.2

omit [Fintype r] in
theorem slpPK_eq (inp : ι → HState R r W) (p : SLP ι) (w : Wire ι) :
    (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).A = slpPK Γ (fun j => (inp j).A) p w :=
  SLP.valueOf_map _ _ _ _ _ _ HState.A (fun _ => rfl) rfl (fun _ _ => rfl) p w

omit [Fintype r] in
theorem slpEnc_eq_c (inp : ι → HState R r W) (p : SLP ι) (w : Wire ι) :
    (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).c =
      slpEnc Γ (fun j => (inp j).A) (fun j => (inp j).x) (fun j => (inp j).c) p w := by
  have := SLP.valueOf_map inp (one Γ) (hstep Γ WN) (fun j => ((inp j).A, (inp j).x, (inp j).c))
    (Γ.G, 1, 0) (encStep Γ) (fun u => (u.A, u.x, u.c)) (fun _ => rfl) rfl (fun _ _ => rfl) p w
  exact congrArg (fun t => t.2.2) this

omit [Fintype r] in
theorem slpEnc_eq_e (inp : ι → HState R r W) (p : SLP ι) (w : Wire ι) :
    (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).e =
      slpEnc Γ (fun j => (inp j).A) (fun j => (inp j).x) (fun j => (inp j).e) p w := by
  have := SLP.valueOf_map inp (one Γ) (hstep Γ WN) (fun j => ((inp j).A, (inp j).x, (inp j).e))
    (Γ.G, 1, 0) (encStep Γ) (fun u => (u.A, u.x, u.e)) (fun _ => rfl) rfl (fun _ _ => rfl) p w
  exact congrArg (fun t => t.2.2) this

/-- **The BGG+ key relation for programs**, for `EvalF` and `EvalFX`: encodings
`c_j = s(B_j − x_j G) + e_j` evaluate to `s(EvalF − f(x) G) + EvalFX(e)`. -/
theorem slp_enc_key_relation (s : Matrix (Fin 1) r R) (Bj : ι → Matrix r W R) (x : ι → R)
    (c e : ι → Matrix (Fin 1) W R) (h : ∀ j, c j = s * (Bj j - x j • Γ.G) + e j) (p : SLP ι)
    (w : Wire ι) :
    slpEnc Γ Bj x c p w = s * (slpPK Γ Bj p w - SLP.eval x p w • Γ.G) + slpEnc Γ Bj x e p w := by
  have hk := slp_bgg_key_relation Γ 0 s (fun j => ⟨Bj j, x j, c j, e j, 0⟩) h p w
  rw [slpEnc_eq_c, slpPK_eq, slp_x_eq, slpEnc_eq_e] at hk
  exact hk

/-- The noise bound of a program: `E` at the inputs, `0` at `1`, `WN · E_a + E_b` at a gate. -/
def slpBound (WN E : ℕ) (p : SLP ι) (w : Wire ι) : ℕ :=
  SLP.valueOf (fun _ => E) 0 (fun a b => WN * a + b) p w

omit [Fintype r] in
theorem slpBound_eq (inp : ι → HState R r W) (E : ℕ) (hE : ∀ j, (inp j).bd = E) (p : SLP ι)
    (w : Wire ι) : (SLP.valueOf inp (one Γ) (hstep Γ WN) p w).bd = slpBound WN E p w :=
  SLP.valueOf_map _ _ _ _ _ _ HState.bd hE rfl (fun _ _ => rfl) p w

section Noise

open Cslib

variable {N q : ℕ} [NeZero q] {r W : Type*} [Fintype W]

/-- **The noise of programs.** With decompositions of norm at most `1`, if every input has a `0/1`
plaintext and an error of norm at most its bound, so has every wire, with `WN = |W| N`. -/
theorem slp_noise (Γ : GadgetMatrix (Negacyclic (ZMod q) N) r W)
    (hΓ : ∀ A c c', cnorm (Γ.ginv A c c') ≤ 1) (inp : ι → HState (Negacyclic (ZMod q) N) r W)
    (h : ∀ i, ((inp i).x = 0 ∨ (inp i).x = 1) ∧ rnorm (inp i).e ≤ (inp i).bd) (p : SLP ι)
    (w : Wire ι) :
    let u := SLP.valueOf inp (one Γ) (hstep Γ (Fintype.card W * N)) p w
    (u.x = 0 ∨ u.x = 1) ∧ rnorm u.e ≤ u.bd := by
  refine SLP.valueOf_invariant inp (one Γ) (hstep Γ (Fintype.card W * N))
    (fun u => (u.x = 0 ∨ u.x = 1) ∧ rnorm u.e ≤ u.bd) h ?_ ?_ p w
  · exact ⟨Or.inr rfl, by simp [HState.one, rnorm_zero]⟩
  · intro a b ⟨hax, hae⟩ ⟨hbx, hbe⟩
    refine ⟨?_, ?_⟩
    · simp only [hstep]
      rcases hax with h1 | h1 <;> rcases hbx with h2 | h2 <;> simp [h1, h2]
    · simp only [hstep, rnorm_neg]
      refine (rnorm_add_le _ _).trans (Nat.add_le_add ?_ ?_)
      · refine (rnorm_mul_le _ _ 1 (hΓ _)).trans ?_
        rw [mul_one]
        exact Nat.mul_le_mul_left _ hae
      · exact (rnorm_smul_le_of_bit _ hax _).trans hbe

/-- **The noise of `EvalFX` for programs.** -/
theorem slp_enc_noise (Γ : GadgetMatrix (Negacyclic (ZMod q) N) r W)
    (hΓ : ∀ A c c', cnorm (Γ.ginv A c c') ≤ 1) (Bj : ι → Matrix r W (Negacyclic (ZMod q) N))
    (x : ι → Negacyclic (ZMod q) N) (hx : ∀ j, x j = 0 ∨ x j = 1)
    (e : ι → Matrix (Fin 1) W (Negacyclic (ZMod q) N)) (E : ℕ) (he : ∀ j, rnorm (e j) ≤ E)
    (p : SLP ι) (w : Wire ι) :
    rnorm (slpEnc Γ Bj x e p w) ≤ slpBound (Fintype.card W * N) E p w := by
  have h := (slp_noise Γ hΓ (fun j => ⟨Bj j, x j, 0, e j, E⟩) (fun j => ⟨hx j, he j⟩) p w).2
  rw [slpEnc_eq_e, slpBound_eq _ _ _ E (fun _ => rfl)] at h
  exact h

end Noise

end SigabaNeo.Lattices
