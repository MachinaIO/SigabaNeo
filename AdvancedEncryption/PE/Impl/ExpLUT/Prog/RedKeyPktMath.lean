import PE.Impl.ExpLUT.Prog.RedKeyPktSkel

/-!
# The packet stream, part 2: the slab segments of the programmed key (at `D`)

For the programming `P = progOf zr` (binary `zr`), the slab segments of `sePkOf … r` are rows of
bits of `zr` (the `Ā` slabs `inl w`: column `w` of the bit matrices) or unit rows (the `η` slabs
`inr (k, c')`):

* `inl w`: `ad_t = ∏_d (ρ_{t,d} ++ ρ_{t,d})` with `ρ_{t,d} = (bit zr(R^aut_{t,d,c}) w)_c`,
  `cr_t = hr_t = 0`, `l0 = (bit zr(R₀_c) w)_c ++ 0`, `z_i = (bit zr(Z_{i,c}) w)_c`,
  `rd_i = ∏_d (ρ'_{i,d} ++ ρ'_{i,d})` with `ρ'_{i,d} = (bit zr(R^in_{i,d,c}) w)_c`;
* `inr (k, c')`: `cr_t = e_{c'}` iff `k = (t, 1)`, `hr_t = e_{c'}` iff `k = (t, 0)`, all else `0`.

**`sePkOf_eq`**: `sePkOf D mpk C ct x (progOf zr) r = ptPacket D.b G (ptAd zr r) (ptCr r) Aa
(ptHr r) Hf (ptL0 zr r) A₀ SP (ptZ zr r) (ptRd zr r) PU` with the public segments `ptG`, `ptAa`,
`ptHf`, `ptA0`, `ptSP`, `ptPU` (independent of `r`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedKeyPkt

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Tape SigabaNeo.Tape.MVM Cslib
open SigabaNeo.Lattices.Algo.NegaG
open SigabaNeo.Lattices.Algo (encRM)
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

variable (D : Dims)

/-! ### Rows of bits, unit rows -/

/-- The row of the bits `f c`. -/
noncomputable def ptRowB (f : Fin 2 × Fin D.K → Bool) : List (Rg D) :=
  vecL (N := D.N) (K := D.K) fun c => bitVal (f c)

/-- The unit row `e_{c'}`. -/
noncomputable def ptUnit (c' : Fin 2 × Fin D.K) : List (Rg D) :=
  vecL (N := D.N) (K := D.K) fun c => if c' = c then 1 else 0

/-- The zero row. -/
noncomputable def ptZRow : List (Rg D) := List.replicate (2 * D.K) 0

/-- A family of rows over the digits, each row twice (`adL` of a family constant in the row). -/
noncomputable def ptDig (f : DigI D.K → List (Rg D)) : List (Rg D) :=
  (Enum.list (α := DigI D.K)).flatMap fun d => f d ++ f d

theorem adL_rows (f : DigI D.K → Fin 2 × Fin D.K → Rg D) :
    adL (N := D.N) (K := D.K) (fun d _ c => f d c) =
      ptDig D fun d => vecL (N := D.N) (K := D.K) (f d) := by
  simp only [adL, matL, enum_fin2, List.flatMap_cons, List.flatMap_nil, List.append_nil, ptDig]
  rfl

theorem vecL_zero' : vecL (N := D.N) (K := D.K) (fun _ => (0 : Rg D)) = ptZRow D :=
  seVecL_zero

/-! ### The slab rows of the programmed key -/

variable (zr : PrI (setting D) Pos → Wb D → Bool)

/-- The slab segment `ad_t`. -/
noncomputable def ptAd : Rest (Wb D) (Jh D) (setting D).τ → ℕ → List (Rg D)
  | .inl w, t => if h : t < D.b then
      ptDig D fun d => ptRowB D fun c => zr (.inr (.inr (.inr (⟨t, h⟩, d, c)))) w else []
  | .inr _, _ => ptDig D fun _ => ptZRow D

/-- The slab segment `cr_t`. -/
noncomputable def ptCr : Rest (Wb D) (Jh D) (setting D).τ → ℕ → List (Rg D)
  | .inl _, _ => ptZRow D
  | .inr (k, c'), t => if k.1.val = t ∧ k.2 = 1 then ptUnit D c' else ptZRow D

/-- The slab segment `hr_t`. -/
noncomputable def ptHr : Rest (Wb D) (Jh D) (setting D).τ → ℕ → List (Rg D)
  | .inl _, _ => ptZRow D
  | .inr (k, c'), t => if k.1.val = t ∧ k.2 = 0 then ptUnit D c' else ptZRow D

/-- The slab segment `l0` (the start slab). -/
noncomputable def ptL0 : Rest (Wb D) (Jh D) (setting D).τ → List (Rg D)
  | .inl w => ptRowB D (fun c => zr (.inr (.inl c)) w) ++
      (List.replicate (2 ^ D.b - 1) (ptZRow D)).flatten
  | .inr _ => (List.replicate (2 ^ D.b) (ptZRow D)).flatten

/-- The slab segment `z_i`. -/
noncomputable def ptZ : Rest (Wb D) (Jh D) (setting D).τ → ℕ → List (Rg D)
  | .inl w, i => ptRowB D fun c => zr (.inl (⟨i % 16, Nat.mod_lt _ (by decide)⟩, c)) w
  | .inr _, _ => ptZRow D

/-- The slab segment `rd_i`. -/
noncomputable def ptRd : Rest (Wb D) (Jh D) (setting D).τ → ℕ → List (Rg D)
  | .inl w, i => ptDig D fun d => ptRowB D fun c =>
      zr (.inr (.inr (.inl (⟨i % 16, Nat.mod_lt _ (by decide)⟩, d, c)))) w
  | .inr _, _ => ptDig D fun _ => ptZRow D

/-! ### The fresh rows of `slabFreshOf (progOf zr)` -/

theorem rowT_ne_row0 {t : ℕ} (ht : t < D.b) : (setting D).rowT t ≠ (setting D).row0 := by
  intro h
  have h1 := rowT_val (S := setting D) (t := t) ht
  rw [h] at h1
  have : ((setting D).row0 : ℕ) = 0 := rfl
  rw [this] at h1
  exact absurd h1.symm (by positivity)

theorem seRhoOf_inl (w : Wb D) {t : ℕ} (ht : t < D.b) (d : Dig (setting D).τ) (c : Col (setting D).τ) :
    seRhoOf D (ExpLUT.progOf zr) (.inl w) t d c = bitVal (zr (.inr (.inr (.inr (⟨t, ht⟩, d, c)))) w) := by
  simp only [seRhoOf, slabFreshOf, finExt, dif_pos (show t < (setting D).b from ht), slabβ,
    ExpLUT.progOf]
  rw [if_pos trivial]; rfl

theorem seRhoOf_inr (ρ : Jh D × Col (setting D).τ) (t : ℕ) (d : Dig (setting D).τ)
    (c : Col (setting D).τ) : seRhoOf D (ExpLUT.progOf zr) (.inr ρ) t d c = 0 := by
  simp only [seRhoOf, slabFreshOf, finExt]
  split_ifs <;> rfl

theorem seCrOf_inl (w : Wb D) (t : ℕ) (c : Col (setting D).τ) :
    seCrOf D (ExpLUT.progOf zr) (.inl w) t c = 0 := by
  simp only [seCrOf, slabFreshOf, finExt]
  split_ifs <;> rfl

theorem seCrOf_inr (k : Jh D) (c' : Col (setting D).τ) {t : ℕ} (ht : t < D.b) (c : Col (setting D).τ) :
    seCrOf D (ExpLUT.progOf zr) (.inr (k, c')) t c =
      if k.1.val = t ∧ k.2 = 1 ∧ c' = c then 1 else 0 := by
  simp only [seCrOf, slabFreshOf, finExt, helperMap]
  rw [dif_pos (show t < (setting D).b from ht)]
  simp only [slabη]
  by_cases h : (k.1.val = t ∧ k.2 = 1 ∧ c' = c)
  · rw [if_pos h, if_pos]
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨trivial, Prod.ext (Fin.ext h1) h2, h3⟩
  · rw [if_neg h, if_neg]
    rintro ⟨-, h2, h3⟩
    subst h2
    exact h ⟨rfl, rfl, h3⟩

theorem seHrOf_inl (w : Wb D) (t : ℕ) (c : Col (setting D).τ) :
    seHrOf D (ExpLUT.progOf zr) (.inl w) t c = 0 := by
  simp only [seHrOf, slabFreshOf, finExt]
  split_ifs <;> rfl

theorem seHrOf_inr (k : Jh D) (c' : Col (setting D).τ) {t : ℕ} (ht : t < D.b) (c : Col (setting D).τ) :
    seHrOf D (ExpLUT.progOf zr) (.inr (k, c')) t c =
      if k.1.val = t ∧ k.2 = 0 ∧ c' = c then 1 else 0 := by
  simp only [seHrOf, slabFreshOf, finExt, helperMap]
  rw [dif_pos (show t < (setting D).b from ht)]
  simp only [slabη]
  by_cases h : (k.1.val = t ∧ k.2 = 0 ∧ c' = c)
  · rw [if_pos h, if_pos]
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨trivial, Prod.ext (Fin.ext h1) h2, h3⟩
  · rw [if_neg h, if_neg]
    rintro ⟨-, h2, h3⟩
    subst h2
    exact h ⟨rfl, rfl, h3⟩

theorem seZvOf_inl (w : Wb D) (t : Pos) (c : Col (setting D).τ) :
    seZvOf D (ExpLUT.progOf zr) (.inl w) t c = bitVal (zr (.inl (t, c)) w) := by
  simp only [seZvOf, slabFreshOf, slabβ, ExpLUT.progOf]
  rw [if_pos trivial]; rfl

theorem seZvOf_inr (ρ : Jh D × Col (setting D).τ) (t : Pos) (c : Col (setting D).τ) :
    seZvOf D (ExpLUT.progOf zr) (.inr ρ) t c = 0 := rfl

theorem seRvOf_inl (w : Wb D) (t : Pos) (d : Dig (setting D).τ) (c : Col (setting D).τ) :
    seRvOf D (ExpLUT.progOf zr) (.inl w) t d c = bitVal (zr (.inr (.inr (.inl (t, d, c)))) w) := by
  simp only [seRvOf, slabFreshOf, slabβ, ExpLUT.progOf]
  rw [if_pos trivial]; rfl

theorem seRvOf_inr (ρ : Jh D × Col (setting D).τ) (t : Pos) (d : Dig (setting D).τ)
    (c : Col (setting D).τ) : seRvOf D (ExpLUT.progOf zr) (.inr ρ) t d c = 0 := rfl

/-! ### The start slab -/

theorem flatMap_finRange_succ {α : Type*} (n : ℕ) (f : Fin (n + 1) → List α) :
    (List.finRange (n + 1)).flatMap f = f 0 ++ (List.finRange n).flatMap fun i => f i.succ := by
  rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem flatMap_const_zero {α β : Type*} (l : List α) (u : List β) :
    l.flatMap (fun _ => u) = (List.replicate l.length u).flatten := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih, List.replicate_succ]

theorem flatMap_finRange_single {α : Type*} {n : ℕ} (hn : 0 < n) (f : Fin n → List α)
    (A Z : List α) (h0 : f ⟨0, hn⟩ = A) (hi : ∀ i : Fin n, i.val ≠ 0 → f i = Z) :
    (List.finRange n).flatMap f = A ++ (List.replicate (n - 1) Z).flatten := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [flatMap_finRange_succ]
  have e1 : f 0 = A := h0
  have e2 : (List.finRange m).flatMap (fun i => f i.succ) = (List.finRange m).flatMap fun _ => Z :=
    List.flatMap_congr fun i _ => hi _ (Fin.succ_ne_zero i |> fun h e => h (Fin.ext e))
  rw [e1, e2, flatMap_const_zero, List.length_finRange]
  rfl

theorem seRows_slabβ (r : Rest (Wb D) (Jh D) (setting D).τ) :
    seRows (seSlabL D (slabβ (setting D).row0 (ExpLUT.progOf (J := Jh D) zr).R0 r)) = ptL0 D zr r := by
  rw [seRows, seSlabL, List.flatMap_map]
  rcases r with w | ⟨k, c'⟩
  · simp only [ptL0]
    refine flatMap_finRange_single (setting D).E.W_pos _ _ _ ?_ ?_
    · show vecL _ = vecL _
      refine congrArg vecL (funext fun c => ?_)
      simp [slabβ, Setting.row0, ExpLUT.progOf]
      rfl
    · intro i hi
      have : i ≠ (setting D).row0 := fun h => hi (by rw [h]; rfl)
      simp only [slabβ, if_neg this]
      exact vecL_zero' D
  · simp only [ptL0]
    have e : (fun i : Fin (setting D).E.W => vecL (N := D.N) (K := D.K)
        (fun c => slabβ (J := Jh D) (setting D).row0 (ExpLUT.progOf (J := Jh D) zr).R0 (.inr (k, c')) i c)) =
        fun _ => ptZRow D := funext fun _ => vecL_zero' D
    rw [e, flatMap_const_zero, List.length_finRange]
    rfl

/-! ### The public segments -/

variable (mpk : MPKt D) (ct : CTt D) (C : List Bool) (x : Pos → ℕ)

/-- `G_t = matL C_{g_t}`. -/
noncomputable def ptG (t : ℕ) : List (Rg D) :=
  matL (N := D.N) (K := D.K) fun a c => gcAut (setting D) ((setting D).idx (2 ^ t))
    ((evalPub (helperMap D) mpk).aut.Hi t) ((evalData (helperMap D) mpk ct).aut.hi t) a c

/-- `Aa_t = adL A^aut_t`. -/
noncomputable def ptAa (t : ℕ) : List (Rg D) :=
  adL (N := D.N) (K := D.K) fun d a c => (evalPub (helperMap D) mpk).aut.Aaut t d a c

/-- `Hf_t = matL H_{g_t}`. -/
noncomputable def ptHf (t : ℕ) : List (Rg D) :=
  matL (N := D.N) (K := D.K) fun a c => (evalPub (helperMap D) mpk).aut.Hf t a c

/-- `matL A₀`. -/
noncomputable def ptA0L : List (Rg D) := matL (N := D.N) (K := D.K) fun a c => mpk.A0 a c

/-- `SP_i = adL A^in_i ++ matL C^in_{read i} ++ [X^{z_i}]`. -/
noncomputable def ptSP (i : ℕ) : List (Rg D) :=
  adL (AinK D mpk i) ++ (matL (N := D.N) (K := D.K) (fun a c =>
    (evalData (helperMap D) mpk ct).Cin ((bpOf (progOf C)).read i) a c) ++
    [(setting D).E.X ^ (bpOf (progOf C)).state x i])

/-- `PU_i = [X^{z_i + w x_{read i}}]`. -/
noncomputable def ptPU (i : ℕ) : List (Rg D) :=
  [(setting D).E.X ^ ((bpOf (progOf C)).state x i + (bpOf (progOf C)).w * x ((bpOf (progOf C)).read i))]

theorem ptPacket_congr {α : Type*} {b : ℕ} {G G' ad ad' cr cr' Aa Aa' hr hr' Hf Hf' : ℕ → List α}
    {l0 l0' A0 A0' : List α} {SP SP' z z' rd rd' PU PU' : ℕ → List α}
    (hG : ∀ t < b, G t = G' t) (had : ∀ t < b, ad t = ad' t) (hcr : ∀ t < b, cr t = cr' t)
    (hAa : ∀ t < b, Aa t = Aa' t) (hhr : ∀ t < b, hr t = hr' t) (hHf : ∀ t < b, Hf t = Hf' t)
    (hl0 : l0 = l0') (hA0 : A0 = A0') (hSP : ∀ i < 16, SP i = SP' i) (hz : ∀ i < 16, z i = z' i)
    (hrd : ∀ i < 16, rd i = rd' i) (hPU : ∀ i < 16, PU i = PU' i) :
    ptPacket b G ad cr Aa hr Hf l0 A0 SP z rd PU = ptPacket b G' ad' cr' Aa' hr' Hf' l0' A0' SP' z' rd' PU' := by
  unfold ptPacket
  rw [hl0, hA0]
  congr 1
  · refine List.flatMap_congr fun t ht => ?_
    have ht' : t < b := List.mem_range.mp ht
    rw [hG t ht', had t ht', hcr t ht', hAa t ht', hhr t ht', hHf t ht']
  · congr 2
    refine List.flatMap_congr fun i hi => ?_
    have hi' : i < 16 := List.mem_range.mp hi
    rw [hSP i hi', hz i hi', hrd i hi', hPU i hi']

/-- **The packet of the slab `r` of the programmed key.** -/
theorem sePkOf_eq (r : Rest (Wb D) (Jh D) (setting D).τ) :
    sePkOf D mpk C ct x (ExpLUT.progOf zr) r =
      ptPacket D.b (ptG D mpk ct) (ptAd D zr r) (ptCr D r) (ptAa D mpk) (ptHr D r) (ptHf D mpk)
        (ptL0 D zr r) (ptA0L D mpk) (ptSP D mpk ct C x) (ptZ D zr r) (ptRd D zr r) (ptPU D C x) := by
  rw [sePkOf, sePacket_eq_ptPacket]
  refine ptPacket_congr (fun _ _ => rfl) ?_ ?_ (fun _ _ => rfl) ?_ (fun _ _ => rfl)
    (seRows_slabβ D zr r) rfl (fun _ _ => rfl) ?_ ?_ (fun _ _ => rfl)
  · intro t ht
    refine (adL_rows D (fun d c => seRhoOf D (ExpLUT.progOf zr) r t d c)).trans ?_
    rcases r with w | ρ
    · simp only [ptAd, dif_pos ht]
      congr 1; funext d
      unfold ptRowB; refine congrArg vecL (funext fun c => ?_)
      exact seRhoOf_inl D zr w ht d c
    · simp only [ptAd]
      congr 1; funext d
      refine Eq.trans ?_ (vecL_zero' D)
      refine congrArg vecL (funext fun c => ?_)
      exact seRhoOf_inr D zr ρ t d c
  · intro t ht
    show vecL (N := D.N) (K := D.K) (fun c => seCrOf D (ExpLUT.progOf zr) r t c) = _
    rcases r with w | ⟨k, c'⟩
    · refine Eq.trans ?_ (vecL_zero' D)
      refine congrArg vecL (funext fun c => ?_)
      exact seCrOf_inl D zr w t c
    · simp only [ptCr]
      split_ifs with h
      · unfold ptUnit; refine congrArg vecL (funext fun c => ?_)
        rw [seCrOf_inr D zr k c' ht c]
        by_cases hc : c' = c
        · rw [if_pos ⟨h.1, h.2, hc⟩]; exact (if_pos hc).symm
        · rw [if_neg (fun h' => hc h'.2.2)]; exact (if_neg hc).symm
      · refine Eq.trans ?_ (vecL_zero' D)
        refine congrArg vecL (funext fun c => ?_)
        rw [seCrOf_inr D zr k c' ht c, if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
  · intro t ht
    show vecL (N := D.N) (K := D.K) (fun c => seHrOf D (ExpLUT.progOf zr) r t c) = _
    rcases r with w | ⟨k, c'⟩
    · refine Eq.trans ?_ (vecL_zero' D)
      refine congrArg vecL (funext fun c => ?_)
      exact seHrOf_inl D zr w t c
    · simp only [ptHr]
      split_ifs with h
      · unfold ptUnit; refine congrArg vecL (funext fun c => ?_)
        rw [seHrOf_inr D zr k c' ht c]
        by_cases hc : c' = c
        · rw [if_pos ⟨h.1, h.2, hc⟩]; exact (if_pos hc).symm
        · rw [if_neg (fun h' => hc h'.2.2)]; exact (if_neg hc).symm
      · refine Eq.trans ?_ (vecL_zero' D)
        refine congrArg vecL (funext fun c => ?_)
        rw [seHrOf_inr D zr k c' ht c, if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
  · intro i _
    show vecL (N := D.N) (K := D.K)
      (fun c => seZvOf D (ExpLUT.progOf zr) r ((bpOf (progOf C)).read i) c) = _
    rcases r with w | ρ
    · unfold ptZ ptRowB; refine congrArg vecL (funext fun c => ?_)
      exact seZvOf_inl D zr w _ c
    · refine Eq.trans ?_ (vecL_zero' D)
      refine congrArg vecL (funext fun c => ?_)
      exact seZvOf_inr D zr ρ _ c
  · intro i _
    refine (adL_rows D (fun d c =>
      seRvOf D (ExpLUT.progOf zr) r ((bpOf (progOf C)).read i) d c)).trans ?_
    rcases r with w | ρ
    · simp only [ptRd]
      unfold ptRowB
      exact congrArg (ptDig D) (funext fun d => congrArg vecL (funext fun c =>
        seRvOf_inl D zr w _ d c))
    · simp only [ptRd]
      congr 1; funext d
      refine Eq.trans ?_ (vecL_zero' D)
      refine congrArg vecL (funext fun c => ?_)
      exact seRvOf_inr D zr ρ _ d c

end AdvancedEncryption.ExpLUT.Prog.RedKeyPkt
