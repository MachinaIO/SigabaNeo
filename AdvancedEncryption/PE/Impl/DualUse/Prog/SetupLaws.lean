import PE.Impl.DualUse.Prog.Layout
import SigabaNeo.Lib.Encode.Laws
import SigabaNeo.Lib.Machines.Prog.Sample

/-!
# The laws of the encoded secrets

The words of the secrets of the reductions, under their laws, as concatenations of independent
blocks of *coefficient words*:

* `μB N K`: the word of a binary ring element `bitVal b` for a fair `b`: one fair bit, then
  `N · K − 1` zeros (`coefB_eq`, for `N, K ≥ 1`);
* `μF K w`: the word of a flooding coefficient (uniform in `{0, …, 2^w − 1}`, as a residue mod
  `2^K`): `min w K` fair bits, then `K − w` zeros (`coefF_eq`);
* uniform blocks: fair bits.

Field laws: `wLaw_eq` (binary columns), `rmLaw_eq` (`lawRmBin`, column-major `rmTEnc`),
`eLaw_eq` (`lawEc`). **`setup5_enc`**: the word of the secret of hybrid 5,
`(setup5 x).map sec5Enc.enc`, is the concatenation of `encAttr x`, `N · K` fair bits (`u₀`),
`|JC| · d` fair bits (`w`), `nA · 2k · d` independent `μB` (the `Rᵢ`), and `|JC| · N` independent
`μF` (the errors).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW Cslib
  Cslib.Probability
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.BPWord

variable {N K k : ℕ}

/-! ### Coefficient words -/

/-- A binary ring element: one fair bit, then `N · K − 1` zeros. -/
noncomputable def μB (N K : ℕ) : PMF (List Bool) :=
  cat (BitString.uniformList 1) (PMF.pure (List.replicate (N * K - 1) false))

/-- A flooding coefficient: `min w K` fair bits, then `K − w` zeros. -/
noncomputable def μF (K w : ℕ) : PMF (List Bool) :=
  cat (BitString.uniformList (min w K)) (PMF.pure (List.replicate (K - w) false))

theorem concatN_head_zero (v : List Bool) (K : ℕ) : ∀ n : ℕ,
    Algo.concatN (n + 1) (fun t => if t = 0 then v else Algo.zeroW K) = v ++ List.replicate (n * K) false
  | 0 => by simp [Algo.concatN]
  | n + 1 => by
    rw [Algo.concatN, concatN_head_zero v K n, if_neg (by omega), Algo.zeroW, List.append_assoc,
      List.replicate_append_replicate, Nat.succ_mul]

theorem enc_bitVal (hN : 0 < N) (hK : 0 < K) (b : Bool) :
    (ringEnc N K).enc (bitVal (R := Rg N K) b) = b :: List.replicate (N * K - 1) false := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have h := Algo.enc_bitR (N := N' + 1) (K := K' + 1) b
  rw [show bitVal (R := Rg (N' + 1) (K' + 1)) b = if b then 1 else 0 from rfl, h, Algo.constW,
    concatN_head_zero]
  simp only [Algo.bitW, Algo.zeroW, List.cons_append, List.replicate_append_replicate]
  congr 2
  rw [Nat.add_mul, Nat.succ_mul]; omega

/-- **Binary ring elements.** -/
theorem coefB_eq (hN : 0 < N) (hK : 0 < K) :
    (PMF.uniformOfFintype Bool).map (fun b => (ringEnc N K).enc (bitVal (R := Rg N K) b)) =
      μB N K := by
  rw [μB, SigabaNeo.Tape.XProg.uniformList_one, cat, PMF.bind_map]
  simp only [Function.comp_def, PMF.pure_map, enc_bitVal hN hK]
  exact (PMF.bind_pure_comp _ _).symm

theorem takeD_eq_map : ∀ (n : ℕ) (u : List Bool),
    Tape.takeD n u = (List.finRange n).map fun i : Fin n => u.getD i.val false
  | 0, u => rfl
  | n + 1, u => by
    rw [Tape.takeD, takeD_eq_map n u.tail, List.finRange_succ, List.map_cons, List.map_map]
    cases u <;> simp [Tape.hd, Function.comp_def]

/-- The flooding coefficient word of `t < 2^w`. -/
def gF (K w : ℕ) (t : Fin (2 ^ w)) : List Bool := (zmodEnc K).enc ((t : ℕ) : ZMod (2 ^ K))

/-- The bits of `t < 2^w`. -/
def finBits (w : ℕ) (t : Fin (2 ^ w)) : Fin w → Bool := fun i => t.val.testBit i

theorem finBits_bijective (w : ℕ) : Function.Bijective (finBits w) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => Fin.ext (Nat.eq_of_testBit_eq fun j => ?_), by simp⟩
  by_cases hj : j < w
  · exact congrFun h ⟨j, hj⟩
  · have hw : 2 ^ w ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (a.isLt.trans_le hw), Nat.testBit_lt_two_pow (b.isLt.trans_le hw)]

theorem gF_eq (K w : ℕ) (t : Fin (2 ^ w)) : gF K w t = Tape.takeD K (List.ofFn (finBits w t)) := by
  have : NeZero (2 ^ K) := ⟨by positivity⟩
  rw [takeD_eq_map, gF]
  show (List.finRange K).map _ = _
  refine List.map_congr_left fun i _ => ?_
  rw [ZMod.val_natCast, Nat.testBit_mod_two_pow]
  simp only [i.isLt, decide_true, Bool.true_and]
  by_cases hi : i.val < w
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]; rfl
  · rw [List.getD_eq_default _ _ (by simpa using hi),
      Nat.testBit_lt_two_pow (t.isLt.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- **Flooding coefficients.** -/
theorem coefF_eq (K w : ℕ) : (PMF.uniformOfFintype (Fin (2 ^ w))).map (gF K w) = μF K w := by
  have hu : (PMF.uniformOfFintype (Fin (2 ^ w))).map (finBits w) = PMF.uniformOfFintype _ :=
    PMF.uniformOfFintype_map_equiv (Equiv.ofBijective _ (finBits_bijective w))
  have h1 : (PMF.uniformOfFintype (Fin (2 ^ w))).map (gF K w) =
      (BitString.uniformList w).map (Tape.takeD K) := by
    rw [show gF K w = Tape.takeD K ∘ List.ofFn ∘ finBits w from funext (gF_eq K w),
      ← PMF.map_comp, ← PMF.map_comp, hu]
    rfl
  rw [h1, μF]
  by_cases hKw : K ≤ w
  · rw [Nat.min_eq_right hKw, Nat.sub_eq_zero_of_le hKw, List.replicate_zero, cat_pure_nil_right,
      ← BitString.uniformList_take hKw]
    refine PMF.map_congr_on_support _ _ _ fun u hu => ?_
    rw [Tape.takeD_eq_take (by rw [BitString.length_of_mem_support_uniformList hu]; exact hKw)]
  · rw [Nat.min_eq_left (by omega), cat]
    rw [← PMF.bind_pure_comp]
    refine PMF.bind_congr_on_support _ _ _ fun u hu => ?_
    have hl := BitString.length_of_mem_support_uniformList hu
    simp only [Function.comp_apply, PMF.pure_map]
    congr 1
    rw [show K = w + (K - w) by omega, Tape.takeD_add, Tape.takeD_of_length' hl, ← hl,
      List.drop_length, Tape.takeD_nil, hl]
    congr 2; omega

/-! ### Field laws -/

variable (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

theorem unif_bits : (PMF.uniformOfFintype Bool).map bitEnc.enc = BitString.uniformList 1 :=
  SigabaNeo.Tape.XProg.uniformList_one.symm

/-- **The binary columns `w`** are uniform words. -/
theorem wLaw_eq :
    (Cslib.Probability.PMF.pi fun _ : JC (Sdw (N := N) hk) =>
      PMF.uniformOfFintype (Fin c.d → Bool)).map (wEnc hk c).enc =
      BitString.uniformList ((Enum.list (α := JC (Sdw (N := N) hk))).length *
        ((Enum.list (α := Fin c.d)).length * 1)) := by
  rw [wEnc, fun_enc_pi, unif_fun bitEnc unif_bits, catPow_uniformList]

theorem fun_enc_eq {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (f : α → β) :
    (FixedEnc.fun e).enc f = ((Enum.list (α := α)).map f).flatMap e.enc := rfl

theorem matTEnc_enc {r s : Type} [Enum r] [Enum s] (M : Matrix r s (Rg N K)) :
    (matTEnc (N := N) (K := K) r s).enc M = ((Enum.list (α := s)).map (fun col a => M a col)).flatMap
      (fun row => ((Enum.list (α := r)).map row).flatMap (ringEnc N K).enc) := rfl

theorem flatMap_map_product {α β γ : Type} (l₁ : List α) (l₂ : List β) (r : α × β → γ)
    (G : γ → List Bool) :
    ((l₁.product l₂).map r).flatMap G = l₁.flatMap (fun i => l₂.flatMap (fun c => G (r (i, c)))) := by
  rw [List.flatMap_map, Algo.flatMap_product]

/-- The word of the `Rᵢ` of binary columns `r`. -/
theorem rmTEnc_rMat (r : (Sdw (N := N) hk).Attr × Col k → (Fin c.d → Bool)) :
    (rmTEnc c).enc (rMat (R := Rg N K) r) =
      ((Enum.list (α := (Sdw (N := N) hk).Attr × Col k)).map r).flatMap
        (fun f => ((List.finRange c.d).map f).flatMap
          (fun b => (ringEnc N K).enc (bitVal (R := Rg N K) b))) := by
  refine Eq.trans ?_ (flatMap_map_product (List.finRange nA) (Enum.list (α := Col k)) r _).symm
  refine Eq.trans (List.flatMap_map (f := rMat (R := Rg N K) r)
    (g := (matTEnc (N := N) (K := K) (Fin c.d) (Col k)).enc) (l := List.finRange nA)) ?_
  refine List.flatMap_congr fun i _ => ?_
  refine (matTEnc_enc _).trans ?_
  simp only [List.flatMap_map]
  rfl

/-- **The `Rᵢ`** (column-major): independent binary ring elements. -/
theorem rmLaw_eq (hN : 0 < N) (hK : 0 < K) :
    (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d) (k := k)).map (rmTEnc c).enc =
      catPow (μB N K) ((Enum.list (α := (Sdw (N := N) hk).Attr × Col k)).length *
        (List.finRange c.d).length) := by
  refine (PMF.map_comp _ _ _).trans ?_
  refine (congrArg (fun f => PMF.map f (Cslib.Probability.PMF.pi fun _ :
    (Sdw (N := N) hk).Attr × Col k => PMF.uniformOfFintype (Fin c.d → Bool)))
    (funext (rmTEnc_rMat hk c))).trans ?_
  rw [pi_map_flatMap, ← catPow_mul, ← coefB_eq hN hK]
  congr 1
  rw [← Cslib.Probability.PMF.pi_uniformOfFintype]
  exact pi_map_flatMap (α := Fin c.d) (PMF.uniformOfFintype Bool)
    (fun b => (ringEnc N K).enc (bitVal (R := Rg N K) b))

/-- The word of the flooding errors from their coefficients `T`. -/
theorem eEnc_flood (T : JC (Sdw (N := N) hk) × Fin N → Fin (2 ^ c.w)) :
    (eEnc (N := N) hk).enc (fun j => Matrix.of fun _ col =>
      Negacyclic.ofCoeffs (fun n => ((T ((j, col), n) : ℕ) : ZMod (2 ^ K)))) =
      ((Enum.list (α := JC (Sdw (N := N) hk) × Fin N)).map T).flatMap (gF K c.w) := by
  refine Eq.trans ?_ (flatMap_map_product _ _ T _).symm
  refine Eq.trans ?_ (Algo.flatMap_product _ _ _).symm
  refine Eq.trans (List.flatMap_map (l := Enum.list) (f := fun j => Matrix.of fun _ col =>
      Negacyclic.ofCoeffs (fun n => ((T ((j, col), n) : ℕ) : ZMod (2 ^ K))))
    (g := (matEnc (N := N) (K := K) (Fin 1) (Col k)).enc)) ?_
  refine List.flatMap_congr fun j _ => ?_
  show (FixedEnc.fun (α := Col k) (ringEnc N K)).enc (fun col =>
      Negacyclic.ofCoeffs (fun n => ((T ((j, col), n) : ℕ) : ZMod (2 ^ K)))) ++ [] = _
  rw [List.append_nil]
  refine Eq.trans (List.flatMap_map _ _ _) ?_
  refine List.flatMap_congr fun col _ => ?_
  refine (ringEnc_flatMap' N K _).trans ?_
  rw [List.flatMap_map]
  rfl

/-- **The flooding errors**: independent flooding coefficients. -/
theorem eLaw_eq [NeZero c.d] :
    (lawEc hk c).map (eEnc (N := N) hk).enc =
      catPow (μF K c.w) (Enum.list (α := JC (Sdw (N := N) hk) × Fin N)).length := by
  have : NeZero (2 ^ c.w) := ⟨by positivity⟩
  have h1 : lawEc hk c = (PMF.uniformOfFintype (JC (Sdw (N := N) hk) × Fin N → Fin (2 ^ c.w))).map
      (fun T j => Matrix.of fun _ col =>
        Negacyclic.ofCoeffs (fun n => ((T ((j, col), n) : ℕ) : ZMod (2 ^ K)))) := by
    unfold lawEc floodRows floodLaw
    rw [PMF.map_comp]
    rfl
  rw [h1, PMF.map_comp]
  refine (congrArg (fun f => PMF.map f (PMF.uniformOfFintype
    (JC (Sdw (N := N) hk) × Fin N → Fin (2 ^ c.w)))) (funext (eEnc_flood hk c))).trans ?_
  rw [← Cslib.Probability.PMF.pi_uniformOfFintype, pi_map_flatMap, coefF_eq]

theorem cat_map_left {α : Type} (μ : PMF α) (f : α → List Bool) (ν : PMF (List Bool)) :
    cat (μ.map f) ν = μ.bind fun a => ν.map (f a ++ ·) := by
  rw [cat, PMF.bind_map]; rfl

theorem bind_pure_eq_map {α β : Type} (μ : PMF α) (f : α → β) :
    (μ.bind fun a => PMF.pure (f a)) = μ.map f := PMF.bind_pure_comp f μ

/-! ### The secret of hybrid 5 -/

/-- **The word of the secret of hybrid 5**: `encAttr x`, then `N · K` fair bits (`u₀`), the fair
bits of `w`, the binary ring elements of the `Rᵢ` (column-major), the flooding coefficients. -/
theorem setup5_enc [NeZero c.d] (hN : 0 < N) (hK : 0 < K) (x : PUniv.Attr) :
    (setup5 hk c x).map (sec5Enc hk c).enc =
      cat (PMF.pure (encAttr x)) (cat (BitString.uniformList (N * K))
        (cat (BitString.uniformList ((Enum.list (α := JC (Sdw (N := N) hk))).length *
          ((Enum.list (α := Fin c.d)).length * 1)))
        (cat (catPow (μB N K) ((Enum.list (α := (Sdw (N := N) hk).Attr × Col k)).length *
          (List.finRange c.d).length))
          (catPow (μF K c.w) (Enum.list (α := JC (Sdw (N := N) hk) × Fin N)).length)))) := by
  rw [← unif_ring, ← wLaw_eq hk c, ← rmLaw_eq hk c hN hK, ← eLaw_eq hk c, cat_pure_left,
    cat_map_left, cat_map_left]
  erw [cat_map_left]
  rw [setup5]
  simp only [PMF.map_bind, bind_pure_eq_map, PMF.map_comp, Function.comp_def]
  refine congrArg (PMF.bind _) (funext fun a => ?_)
  refine congrArg (PMF.bind _) (funext fun a₁ => ?_)
  refine Eq.trans ?_ (PMF.map_bind _ _ _).symm
  refine congrArg (PMF.bind _) (funext fun a₂ => ?_)
  refine Eq.trans ?_ (PMF.map_comp _ _ _).symm
  rfl

/-! ### The coins `rest` (hybrid 3, ideal side) -/

/-- The word of the `Rᵢ`, typed on the attributes of the setting. -/
def rmW (Rm : (Sdw (N := N) hk).Attr → Matrix (Fin c.d) (RingBTVW.Col k) (Rg N K)) : List Bool :=
  (rmTEnc c).enc Rm

theorem rmW_law (hN : 0 < N) (hK : 0 < K) :
    (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d) (k := k)).map (rmW hk c) =
      catPow (μB N K) ((Enum.list (α := (Sdw (N := N) hk).Attr × RingBTVW.Col k)).length *
        (List.finRange c.d).length) := rmLaw_eq hk c hN hK

/-- The word of a χ coefficient. -/
noncomputable def μχ : PMF (List Bool) := c.χc.map (zmodEnc K).enc

theorem χR_enc : (χR c).map (ringEnc N K).enc = catPow (μχ c) N := ofCoeffs_pi_ringEnc N K c.χc

/-- A row with independent entries, encoded. -/
theorem rowLaw_enc (χ : PMF (Rg N K)) (ι : Type) [Fintype ι] [DecidableEq ι] [Enum ι] :
    (rowLaw χ ι).map (matEnc (N := N) (K := K) (Fin 1) ι).enc =
      catPow (χ.map (ringEnc N K).enc) (Enum.list (α := ι)).length := by
  rw [rowLaw, PMF.map_comp, ← fun_enc_pi (ringEnc N K) χ]
  congr 1
  funext v
  exact List.append_nil _

/-- The word of the error row `[σ | ea | ez]`. -/
theorem trapRow_enc (σ : Rg N K) (ea ez : Matrix (Fin 1) (RingBTVW.Col k) (Rg N K)) :
    (matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (trapRowU' σ ea ez) =
      (ringEnc N K).enc σ ++ ((matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ea ++
        (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ez) := by
  show (FixedEnc.fun (α := TrapCol k) (ringEnc N K)).enc (fun col => trapRowU' σ ea ez 0 col) ++ [] =
    (ringEnc N K).enc σ ++ ((FixedEnc.fun (α := RingBTVW.Col k) (ringEnc N K)).enc (ea 0) ++ [] ++
      ((FixedEnc.fun (α := RingBTVW.Col k) (ringEnc N K)).enc (ez 0) ++ []))
  simp only [List.append_nil, fun_enc_eq]
  show (((Enum.list (α := Fin 1)).map Sum.inl ++ ((Enum.list (α := RingBTVW.Col k)).map Sum.inl ++
    (Enum.list (α := RingBTVW.Col k)).map Sum.inr).map Sum.inr).map _).flatMap _ = _
  simp [List.flatMap_append, List.map_append, List.flatMap_map, Enum.list, trapRowU',
    List.finRange_succ]

/-- The coins `rest` with the uniform `s = u₀ − σ` drawn first. -/
theorem lawRestC_eq [NeZero c.d] : lawRestC hk c =
    (PMF.uniformOfFintype (Rg N K)).bind fun s => (rowLaw (χR c) (Fin c.d)).bind fun e₀ =>
      (χR c).bind fun σ => (rowLaw (χR c) (RingBTVW.Col k)).bind fun ea =>
        (rowLaw (χR c) (RingBTVW.Col k)).bind fun ez =>
          (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d) (k := k)).bind fun Rm =>
            (χR c).bind fun e' => PMF.pure (s, e₀, trapRowU' σ ea ez, Rm, e') := by
  unfold lawRestC lawRestNF
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure]
  have h1 : ∀ σ : Rg N K, ((PMF.uniformOfFintype (Rg N K)).bind fun u₀ =>
      (rowLaw (χR c) (Fin c.d)).bind fun e₀ => (rowLaw (χR c) (RingBTVW.Col k)).bind fun ea =>
        (rowLaw (χR c) (RingBTVW.Col k)).bind fun ez =>
          (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d) (k := k)).bind fun Rm =>
            (χR c).bind fun e' => PMF.pure (u₀ - σ, e₀, trapRowU' σ ea ez, Rm, e')) =
      (PMF.uniformOfFintype (Rg N K)).bind fun s =>
      (rowLaw (χR c) (Fin c.d)).bind fun e₀ => (rowLaw (χR c) (RingBTVW.Col k)).bind fun ea =>
        (rowLaw (χR c) (RingBTVW.Col k)).bind fun ez =>
          (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d) (k := k)).bind fun Rm =>
            (χR c).bind fun e' => PMF.pure (s, e₀, trapRowU' σ ea ez, Rm, e') := fun σ =>
    bind_uniform_equiv (Equiv.subRight σ) (fun s =>
      (rowLaw (χR c) (Fin c.d)).bind fun e₀ => (rowLaw (χR c) (RingBTVW.Col k)).bind fun ea =>
        (rowLaw (χR c) (RingBTVW.Col k)).bind fun ez =>
          (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d) (k := k)).bind fun Rm =>
            (χR c).bind fun e' => PMF.pure (s, e₀, trapRowU' σ ea ez, Rm, e'))
  simp only [h1]
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun s => ?_)
  rw [PMF.bind_comm]

/-- **The word of the coins `rest`**: `N · K` fair bits (`s`), then χ coefficients for `e₀`,
`e₁ = [σ | ea | ez]`, the binary `Rᵢ`, and χ coefficients for `e'`. -/
theorem restLaw_enc [NeZero c.d] (hN : 0 < N) (hK : 0 < K) :
    (lawRestC hk c).map (restEnc c).enc =
      cat (BitString.uniformList (N * K)) (cat (catPow (catPow (μχ c) N) (Enum.list (α := Fin c.d)).length)
        (cat (cat (catPow (μχ c) N) (cat (catPow (catPow (μχ c) N) (Enum.list (α := RingBTVW.Col k)).length)
          (catPow (catPow (μχ c) N) (Enum.list (α := RingBTVW.Col k)).length)))
        (cat (catPow (μB N K) ((Enum.list (α := (Sdw (N := N) hk).Attr × RingBTVW.Col k)).length *
          (List.finRange c.d).length)) (catPow (μχ c) N)))) := by
  rw [lawRestC_eq, ← χR_enc, ← rowLaw_enc (χR c) (Fin c.d), ← rowLaw_enc (χR c) (RingBTVW.Col k),
    ← rmW_law hk c hN hK, ← unif_ring, cat_assoc, cat_assoc]
  simp only [cat_map_left, PMF.map_bind, PMF.map_comp, Function.comp_def, bind_pure_eq_map]
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun s => ?_))
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun e₀ => ?_))
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun σ => ?_))
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun ea => ?_))
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun ez => ?_))
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun Rm => ?_))
  refine Eq.trans (PMF.map_comp _ _ _) ?_
  congr 1
  funext e'
  show (ringEnc N K).enc s ++ ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc e₀ ++
    ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (trapRowU' σ ea ez) ++
      ((rmTEnc c).enc Rm ++ (ringEnc N K).enc e'))) = _
  rw [trapRow_enc]
  simp only [rmW, List.append_assoc]

/-- Uniform rows. -/
theorem unif_row (ι : Type) [Fintype ι] [DecidableEq ι] [Enum ι] :
    (PMF.uniformOfFintype (Matrix (Fin 1) ι (Rg N K))).map (matEnc (N := N) (K := K) (Fin 1) ι).enc =
      BitString.uniformList ((Enum.list (α := Fin 1)).length * ((Enum.list (α := ι)).length * (N * K))) :=
  unif_fun _ (unif_fun _ (unif_ring N K))

/-! ### The secret of hybrid 3 -/

/-- **The word of the secret of hybrid 3**: `encAttr x`, fair bits for `B₀`, `w`, `p`, the word
of the coins `rest` (`restLaw_enc`), the flooding coefficients. -/
theorem setup3_enc [NeZero c.d] (x : PUniv.Attr) :
    (setup3 hk c x).map (sec3Enc hk c).enc =
      cat (PMF.pure (encAttr x)) (cat (BitString.uniformList ((Enum.list (α := Fin 1)).length *
        ((Enum.list (α := Fin c.d)).length * (N * K))))
        (cat (BitString.uniformList ((Enum.list (α := JC (Sdw (N := N) hk))).length *
          ((Enum.list (α := Fin c.d)).length * 1)))
        (cat (BitString.uniformList (N * K)) (cat ((lawRestC hk c).map (restEnc c).enc)
          (catPow (μF K c.w) (Enum.list (α := JC (Sdw (N := N) hk) × Fin N)).length))))) := by
  rw [← unif_row, ← wLaw_eq hk c, ← unif_ring N K, ← eLaw_eq hk c, cat_pure_left]
  simp only [cat_map_left, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [setup3]
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun B₀ => ?_))
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun w => ?_))
  refine Eq.trans (PMF.map_bind _ _ _) (congrArg (PMF.bind _) (funext fun p => ?_))
  refine Eq.trans (PMF.map_bind _ _ _) ?_
  refine Eq.trans ?_ (congrArg (PMF.map _) (cat_map_left _ _ _).symm)
  refine Eq.trans ?_ (PMF.map_bind _ _ _).symm
  refine congrArg (PMF.bind _) (funext fun r => ?_)
  refine Eq.trans (congrArg (PMF.map _) (bind_pure_eq_map _ _)) ?_
  refine Eq.trans (PMF.map_comp _ _ _) ?_
  refine Eq.trans ?_ (congrArg (PMF.map _) (PMF.map_comp _ _ _).symm)
  refine Eq.trans ?_ (PMF.map_comp _ _ _).symm
  rfl

/-! ### The ideal side -/

/-- The coins of `Enc` with `s` first and the encodings' errors before `e'`. -/
theorem lawCoinsC_eq [NeZero c.d] : lawCoinsC hk c =
    (PMF.uniformOfFintype (Rg N K)).bind fun s => (rowLaw (χR c) (Fin c.d)).bind fun e₀ =>
      (χR c).bind fun σ => (rowLaw (χR c) (RingBTVW.Col k)).bind fun ea =>
        (rowLaw (χR c) (RingBTVW.Col k)).bind fun ez =>
          (lawRmBin (S := Sdw (N := N) hk) (Wd := Fin c.d) (k := k)).bind fun Rm =>
            (lawEc hk c).bind fun ej => (χR c).bind fun e' =>
              PMF.pure (⟨s, e₀, trapRowU' σ ea ez, Rm, ej, e'⟩ :
                EncCoins (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) := by
  unfold lawCoinsC lawCoins
  rw [lawRestC_eq]
  simp only [PMF.bind_bind, PMF.pure_bind]
  refine congrArg (PMF.bind _) (funext fun s => ?_)
  refine congrArg (PMF.bind _) (funext fun e₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun σ => ?_)
  refine congrArg (PMF.bind _) (funext fun ea => ?_)
  refine congrArg (PMF.bind _) (funext fun ez => ?_)
  refine congrArg (PMF.bind _) (funext fun Rm => ?_)
  rw [PMF.bind_comm]
  refine congrArg (PMF.bind _) (funext fun ej => ?_)
  rw [← bind_pure_eq_map]
  rfl

/-- **The word of the coins of `Enc`.** -/
theorem coinsLaw_enc [NeZero c.d] (hN : 0 < N) (hK : 0 < K) :
    (lawCoinsC hk c).map (coinsEnc hk c).enc =
      cat (BitString.uniformList (N * K)) (cat (catPow (catPow (μχ c) N) (Enum.list (α := Fin c.d)).length)
        (cat (cat (catPow (μχ c) N) (cat (catPow (catPow (μχ c) N) (Enum.list (α := RingBTVW.Col k)).length)
          (catPow (catPow (μχ c) N) (Enum.list (α := RingBTVW.Col k)).length)))
        (cat (catPow (μB N K) ((Enum.list (α := (Sdw (N := N) hk).Attr × RingBTVW.Col k)).length *
          (List.finRange c.d).length))
          (cat (catPow (μF K c.w) (Enum.list (α := JC (Sdw (N := N) hk) × Fin N)).length)
            (catPow (μχ c) N))))) := by
  rw [lawCoinsC_eq, ← χR_enc, ← rowLaw_enc (χR c) (Fin c.d), ← rowLaw_enc (χR c) (RingBTVW.Col k),
    ← rmW_law hk c hN hK, ← eLaw_eq hk c, ← unif_ring, cat_assoc, cat_assoc]
  simp only [cat_map_left, PMF.map_bind, PMF.map_comp, Function.comp_def, bind_pure_eq_map]
  refine congrArg (PMF.bind _) (funext fun s => ?_)
  refine congrArg (PMF.bind _) (funext fun e₀ => ?_)
  refine congrArg (PMF.bind _) (funext fun σ => ?_)
  refine congrArg (PMF.bind _) (funext fun ea => ?_)
  refine congrArg (PMF.bind _) (funext fun ez => ?_)
  refine congrArg (PMF.bind _) (funext fun Rm => ?_)
  refine congrArg (PMF.bind _) (funext fun ej => ?_)
  congr 1
  funext e'
  show (ringEnc N K).enc s ++ ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc e₀ ++
    ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc (trapRowU' σ ea ez) ++
      ((rmTEnc c).enc Rm ++ ((eEnc (N := N) hk).enc ej ++ (ringEnc N K).enc e')))) = _
  rw [trapRow_enc]
  simp only [rmW, List.append_assoc]

/-- The number of bits of the encoded ciphertexts' fields. -/
def nPsi : ℕ := (Enum.list (α := (Sdw (N := N) hk).Attr)).length * ((Enum.list (α := Fin 2)).length *
  ((Enum.list (α := RingBTVW.Col k)).length * (N * K)))
def nC0 : ℕ := (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K))
def nC1 : ℕ := (Enum.list (α := Fin 1)).length * ((Enum.list (α := TrapCol k)).length * (N * K))
def nCj : ℕ := (Enum.list (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index)).length *
  ((Enum.list (α := Fin 1)).length * ((Enum.list (α := RingBTVW.Col k)).length * (N * K)))

/-- **The uniform ciphertext**: uniform words, field by field. -/
theorem ctLaw_enc : (ctUc hk c).map (ctEnc hk c).enc =
    cat (BitString.uniformList (nPsi (N := N) hk)) (cat (BitString.uniformList (nC0 c))
      (cat (BitString.uniformList (nC1 (N := N) (K := K) (k := k))) (cat (BitString.uniformList (nCj (N := N) hk))
        (BitString.uniformList (N * K))))) := by
  rw [nPsi, nC0, nC1, nCj, ← unif_ring N K,
    ← unif_fun (α := (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index) _
      (unif_row (N := N) (K := K) (RingBTVW.Col k)),
    ← unif_row (N := N) (K := K) (TrapCol k), ← unif_row (N := N) (K := K) (Fin c.d),
    ← unif_fun (α := (Sdw (N := N) hk).Attr) _ (unif_fun (α := Fin 2) _
      (unif_fun (α := RingBTVW.Col k) _ (unif_ring N K)))]
  simp only [cat_map_left, PMF.map_bind, PMF.map_comp, Function.comp_def, bind_pure_eq_map]
  unfold ctUc ctU
  simp only [Cslib.Probability.PMF.monad_bind_eq_bind, Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.map_bind, PMF.pure_map, bind_pure_eq_map, PMF.map_comp, Function.comp_def]
  rfl

/-- **The word of the secret of the ideal side**: `encAttr x`, fair bits for `B₀`, `w`, `p`, the
coins of `Enc` (`coinsLaw_enc`), the uniform ciphertext (`ctLaw_enc`). -/
theorem setupI_enc [NeZero c.d] (x : PUniv.Attr) :
    (setupI hk c x).map (secIEnc hk c).enc =
      cat (PMF.pure (encAttr x)) (cat (BitString.uniformList ((Enum.list (α := Fin 1)).length *
        ((Enum.list (α := Fin c.d)).length * (N * K))))
        (cat (BitString.uniformList ((Enum.list (α := JC (Sdw (N := N) hk))).length *
          ((Enum.list (α := Fin c.d)).length * 1)))
        (cat (BitString.uniformList (N * K)) (cat ((lawCoinsC hk c).map (coinsEnc hk c).enc)
          ((ctUc hk c).map (ctEnc hk c).enc))))) := by
  rw [← unif_row, ← wLaw_eq hk c, ← unif_ring N K, cat_pure_left]
  simp only [cat_map_left, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [setupI]
  simp only [PMF.map_bind, PMF.pure_map, bind_pure_eq_map, PMF.map_comp, Function.comp_def]
  rfl

end AdvancedEncryption.DualUse.Prog
