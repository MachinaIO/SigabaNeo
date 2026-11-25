import PE.Impl.RingBTVW.SimGame3

/-!
# The reduction of hybrid 5 and of the ideal side

* Hybrid 5: for a normal-form instance, the secret is `(x, u₀, w, Rᵢ, e)`; the reduction knows `Rᵢ`
  and `W_j` (`accept5`).
* The ideal side (`FI`, the view `hybI1` with `B₁ = toB₁ (a, b)`): the secret is
  `(x, B₀, w, p, r, ct)`, with internal coins `r` for `Ψ` and the simulator's uniform `ct`
  (`acceptI`).
-/

namespace AdvancedEncryption.RingBTVW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW.Fresh Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPCircuit AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-! ### Hybrid 5 -/

/-- The secret of the reduction of hybrid 5. -/
abbrev Sec5 := PUniv.Attr × Rg N K × (JC (Sdw (N := N) hk) → (Fin c.d → Bool)) ×
  (Fin nA → Matrix (Fin c.d) (Col k) (Rg N K)) ×
  ((Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin 1) (Col k) (Rg N K))

/-- The law of the secret. -/
noncomputable def setup5 (x : PUniv.Attr) : PMF (Sec5 hk c) :=
  (PMF.uniformOfFintype (Rg N K)).bind fun u₀ =>
    (Cslib.Probability.PMF.pi fun _ : JC (Sdw (N := N) hk) =>
      PMF.uniformOfFintype (Fin c.d → Bool)).bind fun w =>
    (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d)).bind fun Rm =>
      (lawEc hk c).bind fun e => PMF.pure (x, u₀, w, Rm, e)

/-- The public key and the challenge from the instance and the secret. -/
noncomputable def view5 (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k)
    (σ : Sec5 hk c) : PK hk c × CT hk c :=
  let x := attrBits σ.1
  let u₀ := σ.2.1
  let B₀ := i.1.1
  let a := i.1.2.1
  let z := i.1.2.2.1
  let p := i.1.2.2.2
  let c₀ := scalar u₀ * B₀ + i.2.1
  let c₁ : Matrix (Fin 1) (TrapCol k) (Rg N K) := Matrix.of fun _ c => match c with
    | .inl _ => u₀
    | .inr (.inl c) => (scalar u₀ * a + i.2.2.1) 0 c
    | .inr (.inr c) => (scalar u₀ * z + i.2.2.2.1) 0 c
  let Ψ : Fin nA → Matrix (Fin 2) (Col k) (Rg N K) :=
    fun j => gswPK B₀ c₀ * σ.2.2.2.1 j + bitR (R := Rg N K) (x j) • (Sdw (N := N) hk).Γ.G
  let Bj := fun j => B₀ * wMat σ.2.2.1 j + bitsOf (Sdw (N := N) hk) Ψ j • (Sdw (N := N) hk).Γ₁.G
  (⟨B₀, trapRowU a z, Bj, p⟩,
    ⟨Ψ, c₀, c₁, fun j => c₀ * wMat σ.2.2.1 j + σ.2.2.2.2 j, u₀ * p + i.2.2.2.2 + 0⟩)

/-- What the reduction knows. -/
noncomputable def sd5 (i : Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k)
    (σ : Sec5 hk c) : SimData hk c :=
  ⟨(view5 hk c i σ).1, scalar σ.2.1 * i.1.1 + i.2.1, σ.2.2.2.1, wMat σ.2.2.1,
    (view5 hk c i σ).2.Ψ, σ.1⟩

theorem F5_eq (x : PUniv.Attr) (i) : F5 hk c x i = (setup5 hk c x).map (view5 hk c i) := by
  unfold F5 reduction5 setup5
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.pure_bind]
  rfl

theorem sd5_valid (i) (x : PUniv.Attr) (σ : Sec5 hk c) (hσ : σ ∈ (setup5 hk c x).support) :
    SimValid (sd5 hk c i σ) := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, fun j a b => cnorm_wMat _ j a b⟩
  simp only [setup5, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hσ
  obtain ⟨_, _, _, _, Rm, hRm, _, _, rfl⟩ := hσ
  exact cnorm_of_lawRmBin hRm

theorem setup5_x (x : PUniv.Attr) : ∀ σ ∈ (setup5 hk c x).support, σ.1 = x := by
  intro σ hσ
  simp only [setup5, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hσ
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hσ
  rfl

variable [NeZero c.d]

/-- **The reduction of hybrid 5 accepts as the hybrid.** -/
theorem accept5 (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : bpLen ≤ c.L) (hcov : SimCovered hk c) (A : Machine 3) (D : Machine)
    (inst : PMF (Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k)) :
    accOn A D inst (F5 hk c) = ((inst.bind fun i =>
      ((A.runWith (Generic.oracle (specSim (setup5 hk c) (view5 hk c i) (sd5 hk c i)))
        (paramsWord PUniv params) {}).map Generic.obs).bind (DcB D)) true).toReal :=
  accOn_sim hdec hL hcov A D inst (F5 hk c) (fun _ => setup5 hk c) (view5 hk c) (sd5 hk c)
    (fun x i => F5_eq hk c x i) (fun _ _ => rfl) (fun _ x σ hσ => setup5_x hk c x σ hσ)
    (fun i x σ hσ => sd5_valid hk c i x σ hσ)

/-! ### The ideal side -/

/-- The secret of the reduction of the ideal side. -/
abbrev SecI := PUniv.Attr × Matrix (Fin 1) (Fin c.d) (Rg N K) × (JC (Sdw (N := N) hk) → (Fin c.d → Bool)) ×
  Rg N K × EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k) × CT hk c

/-- The law of the secret. -/
noncomputable def setupI (x : PUniv.Attr) : PMF (SecI hk c) :=
  (PMF.uniformOfFintype (Matrix (Fin 1) (Fin c.d) (Rg N K))).bind fun B₀ =>
    (Cslib.Probability.PMF.pi fun _ : JC (Sdw (N := N) hk) =>
      PMF.uniformOfFintype (Fin c.d → Bool)).bind fun w =>
    (PMF.uniformOfFintype (Rg N K)).bind fun p => (lawCoinsC hk c).bind fun r =>
      (ctUc hk c).bind fun ct => PMF.pure (x, B₀, w, p, r, ct)

/-- The public key and the challenge from the secret. -/
noncomputable def viewI (ab : Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K))
    (σ : SecI hk c) : PK hk c × CT hk c :=
  (⟨σ.2.1, toB₁ (Sdw (N := N) hk) ab, bjOf σ.2.1 (attrBits σ.1) σ.2.2.2.2.1 (hashCols σ.2.1 σ.2.2.1),
    σ.2.2.2.1⟩, σ.2.2.2.2.2)

/-- What the reduction knows. -/
noncomputable def sdI (ab : Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K))
    (σ : SecI hk c) : SimData hk c :=
  ⟨(viewI hk c ab σ).1, scalar σ.2.2.2.2.1.s * σ.2.1 + σ.2.2.2.2.1.e₀, σ.2.2.2.2.1.Rm,
    wMat σ.2.2.1, gswOf σ.2.1 (attrBits σ.1) σ.2.2.2.2.1, σ.1⟩

theorem FI_eq (x : PUniv.Attr) (ab) : FI hk c x ab = (setupI hk c x).map (viewI hk c ab) := by
  unfold FI hybI1 contI setupI
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, PMF.pure_bind]
  refine congrArg (PMF.bind _) (funext fun B₀ => ?_)
  rw [Cslib.Probability.PMF.pi_map, PMF.bind_map]
  rfl

theorem sdI_valid (ab) (x : PUniv.Attr) (σ : SecI hk c) (hσ : σ ∈ (setupI hk c x).support) :
    SimValid (sdI hk c ab σ) := by
  refine ⟨fun i => rfl, fun j => ?_, ?_, fun j a b => cnorm_wMat _ j a b⟩
  · show bjOf σ.2.1 (attrBits σ.1) _ (hashCols σ.2.1 σ.2.2.1) j = _
    unfold bjOf
    rw [of_hashCols]
    rfl
  · simp only [setupI, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hσ
    obtain ⟨_, _, _, _, _, _, r, hr, _, _, rfl⟩ := hσ
    unfold lawCoinsC lawCoins at hr
    simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hr
    obtain ⟨rest, hrest, e, -, rfl⟩ := hr
    exact cnorm_of_lawRestC hrest

theorem setupI_x (x : PUniv.Attr) : ∀ σ ∈ (setupI hk c x).support, σ.1 = x := by
  intro σ hσ
  simp only [setupI, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hσ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := hσ
  rfl

/-- **The reduction of the ideal side accepts as the hybrid.** -/
theorem acceptI (hdec : ∀ u, gadgetMap (S := Sdw (N := N) hk) (c.dec u) = u)
    (hL : bpLen ≤ c.L) (hcov : SimCovered hk c) (A : Machine 3) (D : Machine)
    (inst : PMF (Matrix (Fin 1) (Col k) (Rg N K) × Matrix (Fin 1) (Col k) (Rg N K))) :
    accOn A D inst (FI hk c) = ((inst.bind fun ab =>
      ((A.runWith (Generic.oracle (specSim (setupI hk c) (viewI hk c ab) (sdI hk c ab)))
        (paramsWord PUniv params) {}).map Generic.obs).bind (DcB D)) true).toReal :=
  accOn_sim hdec hL hcov A D inst (FI hk c) (fun _ => setupI hk c) (viewI hk c) (sdI hk c)
    (fun x ab => FI_eq hk c x ab) (fun _ _ => rfl) (fun _ x σ hσ => setupI_x hk c x σ hσ)
    (fun ab x σ hσ => sdI_valid hk c ab x σ hσ)

end AdvancedEncryption.RingBTVW
