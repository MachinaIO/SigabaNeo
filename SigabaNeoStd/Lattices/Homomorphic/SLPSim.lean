import SigabaNeoStd.Lattices.Homomorphic.SLPEval

/-!
# The simulation relation for straight-line programs

Public keys `Aᵢ = B Wᵢ + xᵢ G` evaluate along a straight-line program to `A_w = B W_w + w(x) G`
(`slp_sim_relation`), where `W_w = slpSim` is evaluated alongside: the relation behind `Setup*` and
`KeyGen*` of BTVW17 §4.2 ([ABB10], [BGG+14]), for programs instead of circuits.
-/

namespace SigabaNeo.Lattices

open Matrix

variable {R : Type*} [CommRing R] {r W m : Type*} [Fintype r] [Fintype W] [Fintype m]
  (Γ : GadgetMatrix R r W) {ι : Type*}

/-- One gate on (public key, its short matrix, its input value). -/
def simStep (u v : Matrix r W R × Matrix m W R × R) : Matrix r W R × Matrix m W R × R :=
  (Γ.G - u.1 * Γ.ginv v.1, -(u.2.1 * Γ.ginv v.1 + u.2.2 • v.2.1), 1 - u.2.2 * v.2.2)

/-- The joint run on (public key, short matrix, value). -/
def simRun (A : ι → Matrix r W R) (Wm : ι → Matrix m W R) (x : ι → R) (p : SLP ι) (w : Wire ι) :
    Matrix r W R × Matrix m W R × R :=
  SLP.valueOf (fun i => (A i, Wm i, x i)) (Γ.G, 0, 1) (simStep Γ) p w

/-- The short matrix `W_w` of a wire. -/
def slpSim (A : ι → Matrix r W R) (Wm : ι → Matrix m W R) (x : ι → R) (p : SLP ι) (w : Wire ι) :
    Matrix m W R :=
  (simRun Γ A Wm x p w).2.1

omit [Fintype r] [Fintype m] in
theorem simRun_fst (A : ι → Matrix r W R) (Wm : ι → Matrix m W R) (x : ι → R) (p : SLP ι)
    (w : Wire ι) : (simRun Γ A Wm x p w).1 = slpPK Γ A p w :=
  SLP.valueOf_map _ _ _ A Γ.G _ Prod.fst (fun _ => rfl) rfl (fun _ _ => rfl) p w

omit [Fintype r] [Fintype m] in
theorem simRun_snd_snd (A : ι → Matrix r W R) (Wm : ι → Matrix m W R) (x : ι → R) (p : SLP ι)
    (w : Wire ι) : (simRun Γ A Wm x p w).2.2 = SLP.eval x p w :=
  SLP.valueOf_map _ _ _ x 1 _ (fun u : Matrix r W R × Matrix m W R × R => u.2.2) (fun _ => rfl) rfl (fun _ _ => rfl) p w

omit [Fintype r] in
/-- **The simulation relation along a program.** -/
theorem slp_sim_relation (B : Matrix r m R) (A : ι → Matrix r W R) (Wm : ι → Matrix m W R)
    (x : ι → R) (h : ∀ i, A i = B * Wm i + x i • Γ.G) (p : SLP ι) (w : Wire ι) :
    slpPK Γ A p w = B * slpSim Γ A Wm x p w + SLP.eval x p w • Γ.G := by
  have hinv := SLP.valueOf_invariant (fun i => (A i, Wm i, x i)) (Γ.G, 0, 1) (simStep Γ)
    (fun u => u.1 = B * u.2.1 + u.2.2 • Γ.G) (fun i => h i) (by simp) ?_ p w
  · rw [← simRun_fst Γ A Wm x, ← simRun_snd_snd Γ A Wm x]
    exact hinv
  · rintro ⟨Aa, Wa, a⟩ ⟨Ab, Wb, b⟩ ha hb
    simp only at ha hb ⊢
    simp only [simStep]
    have hG := Γ.mul_ginv Ab
    rw [ha, Matrix.add_mul, Matrix.smul_mul, hG, hb]
    simp only [Matrix.mul_neg, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add,
      smul_smul, sub_smul, one_smul]
    abel

end SigabaNeo.Lattices
