import PE.Impl.DualUse.SimGame

/-!
# The reduction of hybrid 3

For a Ring-LWE pair `(a, b)` the reduction's secret is `(x, B₀, w, p, rest, e)`: the columns `w`
give `B_j = B₀ W_j + ψ_j G̲`, the coins `rest` the ciphertexts `Ψᵢ = [B₀; c₀] Rᵢ + xᵢ G`, and
`B₁ = toB₁ (a, b)`. The view of hybrid 3 is the image of this secret (`F3_eq`), the data are valid
(`sd3_valid`), so the reduction's experiment accepts as the hybrid's (`accept3`).
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The secret of the reduction of hybrid 3. -/
abbrev Sec3 := Date × Matrix (Fin 1) (Fin c.d) (Rg N K) × (JC (Sdw (N := N) hk) → (Fin c.d → Bool)) ×
  Rg N K × Rest (Sdw (N := N) hk) (Fin c.d) (TrapCol k) ×
  ((Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin 1) (Col k) (Rg N K))

/-- The law of the secret. -/
noncomputable def setup3 (x : Date) : PMF (Sec3 hk c) :=
  (PMF.uniformOfFintype (Matrix (Fin 1) (Fin c.d) (Rg N K))).bind fun B₀ =>
    (Cslib.Probability.PMF.pi fun _ : JC (Sdw (N := N) hk) =>
      PMF.uniformOfFintype (Fin c.d → Bool)).bind fun w =>
    (PMF.uniformOfFintype (Rg N K)).bind fun p => (lawRestC hk c).bind fun rest =>
      (lawEc hk c).bind fun e => PMF.pure (x, B₀, w, p, rest, e)

/-- The public key and the challenge from the secret. -/
noncomputable def view3 (ab : Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K))
    (σ : Sec3 hk c) : PK hk c × CT hk c :=
  let r := coinsOf σ.2.2.2.2.1 σ.2.2.2.2.2
  let mpk : PK hk c := ⟨σ.2.1, toB₁ (Sdw (N := N) hk) ab,
    bjOf σ.2.1 (bitsOf σ.1) r (hashCols σ.2.1 σ.2.2.1), σ.2.2.2.1⟩
  (mpk, { encrypt mpk (bitsOf σ.1) false r with cj := floodCj σ.2.1 σ.2.2.1 r })

/-- What the reduction knows. -/
noncomputable def sd3 (ab : Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K))
    (σ : Sec3 hk c) : SimData hk c :=
  let r := coinsOf σ.2.2.2.2.1 σ.2.2.2.2.2
  ⟨(view3 hk c ab σ).1, scalar r.s * σ.2.1 + r.e₀, r.Rm, wMat σ.2.2.1,
    gswOf σ.2.1 (bitsOf σ.1) r, σ.1⟩

theorem F3_eq (x : Date) (ab) : F3 hk c x ab = (setup3 hk c x).map (view3 hk c ab) := by
  unfold F3 viewW setup3
  simp only [PMF.map_bind, PMF.pure_map, PMF.pure_bind]
  rfl

theorem sd3_valid (ab) (x : Date) (σ : Sec3 hk c) (hσ : σ ∈ (setup3 hk c x).support) :
    SimValid (sd3 hk c ab σ) := by
  refine ⟨fun i => rfl, fun j => ?_, ?_, fun j a b => cnorm_wMat _ j a b⟩
  · show bjOf σ.2.1 (bitsOf σ.1) _ (hashCols σ.2.1 σ.2.2.1) j = _
    unfold bjOf
    rw [of_hashCols]
    rfl
  · simp only [setup3, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hσ
    obtain ⟨_, _, _, _, _, _, rest, hrest, _, _, rfl⟩ := hσ
    exact cnorm_of_lawRestC hrest

theorem setup3_x (x : Date) : ∀ σ ∈ (setup3 hk c x).support, σ.1 = x := by
  intro σ hσ
  simp only [setup3, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hσ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := hσ
  rfl

variable [NeZero c.d]

/-- **The reduction of hybrid 3 accepts as the hybrid**, on any law of Ring-LWE pairs. -/
theorem accept3 (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : dateBound ≤ c.L) (hcov : SimCovered hk c) (A : Machine 3) (D : Machine)
    (inst : PMF (Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K))) :
    accOn A D inst (F3 hk c) = ((inst.bind fun ab =>
      ((A.runWith (Generic.oracle (specSim (setup3 hk c) (view3 hk c ab) (sd3 hk c ab)))
        (paramsWord dateUniverse params) {}).map Generic.obs).bind (DcB D)) true).toReal :=
  accOn_sim hdec hL hcov A D inst (F3 hk c) (fun _ => setup3 hk c) (view3 hk c) (sd3 hk c)
    (fun x ab => F3_eq hk c x ab) (fun _ _ => rfl) (fun _ x σ hσ => setup3_x hk c x σ hσ)
    (fun ab x σ hσ => sd3_valid hk c ab x σ hσ)

end AdvancedEncryption.DualUse
