import PE.Impl.DualUse.AHAssembly
import PE.Impl.DualUse.SimKeys
import PE.Impl.DualUse.ParamSupport

/-!
# Key queries answered with the simulated trapdoor

The reductions know, for the selected attribute `x`, the binary `Rᵢ` and `W_j` behind the
ciphertexts `Ψᵢ = [B₀; c₀] Rᵢ + xᵢ G` and the keys `B_j = B₀ W_j + ψ_j G̲` (`SimData`, `SimValid`).
They answer a key query `C` with one try of box rejection with the trapdoor
`W_f = simKeyMat …` (`KGsim`). For a query that is not authorized for `x`, this is the ideal key
law (`KGsim_eq_KGi`) as soon as the boxes cover the simulated trapdoor (`SimCovered`): a window
predicate of at most `L ≥ dateBound` bits that is not authorized has `f(x) = 1`, so
`B_f̂ = B₀ W_f + G̲`.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)
variable {ms : Machines hk c}

/-- What a reduction knows about the selected attribute's ciphertext and keys. -/
structure SimData where
  /-- The public key. -/
  mpk : PK hk c
  /-- The second row of `A`. -/
  c₀ : Matrix (Fin 1) (Fin c.d) (Rg N K)
  /-- The matrices `Rᵢ`. -/
  Rm : Fin nA → Matrix (Fin c.d) (Col k) (Rg N K)
  /-- The matrices `W_j`. -/
  W : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin c.d) (Col k) (Rg N K)
  /-- The attribute ciphertexts. -/
  Ψ : Fin nA → Matrix (Fin 2) (Col k) (Rg N K)
  /-- The selected attribute. -/
  x : Date

variable {hk c}

/-- The relations between the data, and the matrices `Rᵢ`, `W_j` binary (coefficients within
`1`, what the boxes need to cover the simulated trapdoor). -/
def SimValid (d : SimData hk c) : Prop :=
  (∀ i, d.Ψ i = gswPK d.mpk.B₀ d.c₀ * d.Rm i + bitR (R := Rg N K) (bitsOf d.x i) •
      (Sdw (N := N) hk).Γ.G) ∧
    (∀ j, d.mpk.Bj j = d.mpk.B₀ * d.W j + bitsOf (Sdw (N := N) hk) d.Ψ j • (Sdw (N := N) hk).Γ₁.G) ∧
    (∀ i a b, cnorm (d.Rm i a b) ≤ 1) ∧ ∀ j a b, cnorm (d.W j a b) ≤ 1

/-- The binary matrices `W_j` from their columns have coefficients within `1`. -/
theorem cnorm_wMat (w : JC (Sdw (N := N) hk) → (Fin c.d → Bool)) (j) (a : Fin c.d) (b : Col k) :
    cnorm (wMat (R := Rg N K) w j a b) ≤ 1 :=
  cnorm_bitVal_le _

/-- The binary matrices `Rᵢ` of `lawRmBin` have coefficients within `1`. -/
theorem cnorm_of_lawRmBin {Rm : (Sdw (N := N) hk).Attr → Matrix (Fin c.d) (Col k) (Rg N K)}
    (h : Rm ∈ (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d)).support) :
    ∀ i a b, cnorm (Rm i a b) ≤ 1 := by
  unfold lawRmBin at h
  rw [PMF.mem_support_map_iff] at h
  obtain ⟨bits, -, rfl⟩ := h
  intro i a b
  exact cnorm_bitVal_le _

/-- The coins of the rest of `Enc` have binary `Rᵢ`. -/
theorem cnorm_of_lawRestC {rest : Rest (Sdw (N := N) hk) (Fin c.d) (TrapCol k)}
    (h : rest ∈ (lawRestC hk c).support) : ∀ i a b, cnorm (rest.2.2.2.1 i a b) ≤ 1 := by
  unfold lawRestC lawRestNF at h
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨σ, -, u₀, -, e₀, -, ea, -, ez, -, Rm, hRm, e', -, rfl⟩ := h
  exact cnorm_of_lawRmBin hRm

/-- The simulated trapdoor of a predicate. -/
noncomputable def simW (d : SimData hk c) (C : List Bool) : Matrix (Fin c.d) (Col k) (Rg N K) :=
  simKeyMat (S := Sdw (N := N) hk) d.Rm (bitsOf d.x) d.W d.Ψ d.mpk.Bj (predC C)

open Classical in
/-- **The simulated key oracle.** -/
noncomputable def KGsim (d : SimData hk c) (C : List Bool) : PMF (List Bool) :=
  if C.length ≤ c.L then
    if ValidC C then
      (keyLaw c.Big c.Small c.hBig c.dec d.mpk (simTrap (Wt := TrapCol k) (simW d C))).map
        fun o => (skEnc hk c).enc (d.mpk, keyOfOutput o)
    else PMF.pure ((skEnc hk c).enc (d.mpk, dummyKey c))
  else PMF.pure []

variable (hk c) in
/-- The boxes cover the simulated trapdoor of every unauthorized window predicate. -/
def SimCovered : Prop :=
  ∀ d : SimData hk c, SimValid d → ∀ w : Window, evalGates (encDate d.x, parse (winWord w)) = true →
    ∀ y ∈ c.Small, ∀ u, y + simTrap (Wt := TrapCol k) (simW d (winWord w)) (c.dec u) ∈ c.Big

/-- A window predicate that is not authorized for `x` is true on `x`. -/
theorem evalGates_of_not_auth (hL : dateBound ≤ c.L) (w : Window) (x : Date)
    (h : authI hk c (winWord w) x = false) : evalGates (encDate x, parse (winWord w)) = true := by
  unfold authI at h
  simp only [decide_eq_false_iff_not] at h
  rw [win_authorized_iff (impl hk c) rfl] at h
  have hlen := (Finset.le_sup (f := fun wx : Window × Date =>
      (encodeTuple [paramsWord PUniv params, winWord wx.1, PUniv.encAttr wx.2]).length)
      (Finset.mem_univ (α := Window × Date) (w, x))).trans hL
  by_contra hne
  exact h ⟨hlen, ⟨w, rfl⟩, by simpa using hne⟩

/-- The predicate's key matrix with the simulated trapdoor: `B_f̂ = B₀ W_f + G̲` when `f(x) = 1`. -/
theorem keyMatrix_simW (d : SimData hk c) (hv : SimValid d) (w : Window)
    (hev : evalGates (encDate d.x, parse (winWord w)) = true) :
    keyMatrix d.mpk (predC (winWord w)) =
      d.mpk.B₀ * simW d (winWord w) + (Sdw (N := N) hk).Γ₁.G := by
  have h := keyMatrix_eq_sim (ringSetting_fhatCorrect hk (Fin nA)) d.mpk d.c₀ d.Rm (bitsOf d.x)
    d.W d.Ψ hv.1 hv.2.1 (predC (winWord w))
  have hne : parse (winWord w) ≠ [] := by
    rw [winWord, parse_unparse, winGates, predGates, toGates]
    simp
  have hb : SLP.evalBool (bitsOf d.x) (predC (winWord w)).1 (predC (winWord w)).2 = true := by
    rw [predC, ← evalGates_predOf (bitsOf d.x) _ hne, ofFn_bitsOf]; exact hev
  have hcirc : (ringSetting N (2 ^ K) k hk (Fin nA)).circ (predC (winWord w)) =
      (predC (winWord w)).1.circuit (predC (winWord w)).2 := by simp only [ringSetting]
  have heval : ((ringSetting N (2 ^ K) k hk (Fin nA)).circ (predC (winWord w))).eval
      (fun i => bitR (R := Rg N K) (bitsOf d.x i)) = 1 := by
    rw [hcirc, SLP.eval_circuit]
    have := SLP.eval_bits (R := Rg N K) (bitsOf d.x) (predC (winWord w)).1 (predC (winWord w)).2
    simp only [bitR] at this ⊢
    rw [this, hb, if_pos rfl]
  have e2 := congrArg (fun r : Rg N K => d.mpk.B₀ * simW d (winWord w) + r • (Sdw (N := N) hk).Γ₁.G)
    heval
  simp only [one_smul] at e2
  exact h.trans e2

/-- **Simulated keys have the ideal law** on every query that is not authorized for `x`. -/
theorem KGsim_eq_KGi (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : dateBound ≤ c.L) (hcov : SimCovered hk c) (d : SimData hk c) (hv : SimValid d)
    (C : List Bool) (hC : authI hk c C d.x = false) : KGsim d C = KGi hk c d.mpk C := by
  unfold KGsim KGi
  split_ifs with hlen hw
  · obtain ⟨w, rfl⟩ := hw
    have hev := evalGates_of_not_auth hL w d.x hC
    rw [keyLaw_eq_ideal c.Big c.Small c.hBig c.dec hdec d.mpk _ _
      ⟨simTrap_public (Wt := TrapCol k) d.mpk _ _ (keyMatrix_simW d hv w hev),
        hcov d hv w hev⟩]
  · rfl
  · rfl

end AdvancedEncryption.DualUse
