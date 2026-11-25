import PE.Impl.ExpLUT.Prog.DecFinal
import PE.Impl.ExpLUT.Prog.DecCoefMath
import PE.Impl.ExpLUT.Prog.SetupGad

/-!
# The end of decryption at the dimensions `D`

The end of decryption on `RingVM` (`exec_finC`, `PE.Impl.ExpLUT.Prog.DecFinal`) decodes the value
`finVal` of word lists. Here, when the registers hold the encodings of a public key, a key, a
ciphertext (the words of `FixedEnc.fun`, in the order of `Enum`) and words of `c_F`, `A_F⁽²⁾`,
`finVal` is `decryptRaw` (`finVal_eq_decryptRaw`), so register `179` holds
`[decodeBit D (decryptRaw …)]` (**`exec_finC_D`**).

* list sums: `sum_range_enum` (a loop over the enumeration is the `Fintype` sum), `dotL_eq`,
  `conjL_eq` (with `decRM (f y) = φ (decRM y)`, the `i`-th block is `φ^[i]`);
* indexing products: `getD_map_product_F`;
* `σ_g^[i] = σ_{g^i}` inside `H` (`iterate_σ_idx_one`), `autMW` with a template of length
  `κD D 0` is `σ_{g}` (`decRM_autMW_κ0`); the gadget row words `g1W` decode to `G⁽²⁾`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo SigabaNeo.Lattices.Algo.NegaG Matrix

/-! ### Sums over enumerations -/

/-- The elements of an enumerated type, as positions of its enumeration. -/
noncomputable def enumEquiv' (α : Type) [Enum α] : Fin (Enum.list (α := α)).length ≃ α := by
  classical exact List.Nodup.getEquivOfForallMemList _ Enum.nodup Enum.complete

/-- **A loop over the enumeration is the `Fintype` sum.** -/
theorem sum_range_enum {α M : Type} [Enum α] [Fintype α] [AddCommMonoid M] (f : α → M)
    (G : ℕ → M) (hG : ∀ e (he : e < (Enum.list (α := α)).length), G e = f (Enum.list (α := α))[e]) :
    ∑ e ∈ Finset.range (Enum.list (α := α)).length, G e = ∑ a, f a := by
  rw [← (enumEquiv' α).sum_comp, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hG i i.isLt]
  rfl

theorem getD_map_of_lt_F {β γ : Type} (l : List β) (g : β → γ) (d : γ) (d' : β) {e : ℕ}
    (he : e < l.length) : (l.map g).getD e d = g (l.getD e d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using he), List.getD_eq_getElem _ _ he, List.getElem_map]

theorem dgetD_drop' {β : Type} (l : List β) (a e : ℕ) (d : β) : (l.drop a).getD e d = l.getD (a + e) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **Indexing a product.** -/
theorem getD_map_product_F {α β γ : Type} (l₁ : List α) (l₂ : List β) (g : α × β → γ) (d : γ) :
    ∀ {i e : ℕ} (hi : i < l₁.length) (he : e < l₂.length),
      ((l₁.product l₂).map g).getD (i * l₂.length + e) d = g (l₁[i], l₂[e]) := by
  induction l₁ with
  | nil => intro i e hi; simp at hi
  | cons a l ih =>
    intro i e hi he
    have hp : (a :: l).product l₂ = l₂.map (fun b => (a, b)) ++ l.product l₂ := rfl
    rw [hp, List.map_append, List.map_map]
    rcases i with _ | i
    · rw [zero_mul, zero_add, List.getD_append _ _ _ _ (by simpa using he),
        getD_map_of_lt_F _ _ _ (l₂[e]) he, List.getD_eq_getElem _ _ he]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
      have : (i + 1) * l₂.length + e - (l₂.map (g ∘ fun b => (a, b))).length = i * l₂.length + e := by
        simp; ring_nf; omega
      rw [this, ih (by simpa using hi) he]
      rfl

theorem enum_prod {α β : Type} [Enum α] [Enum β] :
    (Enum.list (α := α × β)) = (Enum.list (α := α)).product (Enum.list (α := β)) := rfl

theorem enum_sum {α β : Type} [Enum α] [Enum β] :
    (Enum.list (α := α ⊕ β)) = (Enum.list (α := α)).map Sum.inl ++ (Enum.list (α := β)).map Sum.inr :=
  rfl

theorem enum_fin (n : ℕ) : (Enum.list (α := Fin n)) = List.finRange n := rfl

/-! ### The sums of the machine as `Fintype` sums -/

section Sums

variable {N K : ℕ} [NeZero (2 ^ K - 1)]

/-- **`dotL` as a `Fintype` sum.** -/
theorem dotL_eq {α : Type} [Enum α] [Fintype α] (x kk : α → RM N K) (xs ks : List (List Bool))
    (hx : ∀ e (he : e < (Enum.list (α := α)).length), decRM N K (xs.getD e []) = x (Enum.list)[e])
    (hk : ∀ e (he : e < (Enum.list (α := α)).length), decRM N K (ks.getD e []) = kk (Enum.list)[e]) :
    dotL xs ks (Enum.list (α := α)).length = ∑ a, x a * kk a :=
  sum_range_enum _ _ fun e he => by rw [hx e he, hk e he]

/-- **`conjL` as a `Fintype` sum**, for `f` acting as `φ` on the ring. -/
theorem conjL_eq {α : Type} [Enum α] [Fintype α] (f : List Bool → List Bool) (φ : RM N K → RM N K)
    (hf : ∀ y, y.length = N * K → (f y).length = N * K ∧ decRM N K (f y) = φ (decRM N K y))
    (W : ℕ) (x : α → RM N K) (kk : Fin W → α → RM N K) (xs ks : List (List Bool))
    (hxl : xs.length = (Enum.list (α := α)).length)
    (hxw : ∀ y ∈ xs, y.length = N * K)
    (hx : ∀ e (he : e < (Enum.list (α := α)).length), decRM N K (xs.getD e []) = x (Enum.list)[e])
    (hk : ∀ i (hi : i < W) e (he : e < (Enum.list (α := α)).length),
      decRM N K (ks.getD (i * (Enum.list (α := α)).length + e) []) = kk ⟨i, hi⟩ (Enum.list)[e]) :
    conjL f xs ks (Enum.list (α := α)).length W = ∑ i : Fin W, ∑ a, φ^[i] (x a) * kk i a := by
  have hfi : ∀ i y, y.length = N * K →
      (f^[i] y).length = N * K ∧ decRM N K (f^[i] y) = φ^[i] (decRM N K y) := by
    intro i; induction i with
    | zero => intro y hy; exact ⟨hy, rfl⟩
    | succ i ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', (hf _ h1).2, h2]
      exact ⟨(hf _ h1).1, rfl⟩
  rw [conjL, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine dotL_eq (fun a => φ^[i] (x a)) (kk i) _ _ (fun e he => ?_) (fun e he => ?_)
  · have he' : e < xs.length := by omega
    have hm : xs.getD e [] ∈ xs := by rw [List.getD_eq_getElem _ _ he']; exact List.getElem_mem he'
    rw [getD_map_of_lt_F _ _ _ [] he', (hfi i _ (hxw _ hm)).2, hx e he]
  · rw [dgetD_drop', hk i i.isLt e he]

end Sums

/-- A map over a product: the blocks of the first factor. -/
theorem map_product {α β γ : Type} (l₁ : List α) (l₂ : List β) (g : α × β → γ) :
    (l₁.product l₂).map g = (l₁.map fun a => l₂.map fun b => g (a, b)).flatten := by
  induction l₁ with
  | nil => rfl
  | cons a l ih =>
    have hp : (a :: l).product l₂ = l₂.map (fun b => (a, b)) ++ l.product l₂ := rfl
    rw [hp, List.map_append, ih, List.map_map]
    rfl

theorem length_enum_prod {α β : Type} [Enum α] [Enum β] :
    (Enum.list (α := α × β)).length = (Enum.list (α := α)).length * (Enum.list (α := β)).length := by
  rw [enum_prod]; exact List.length_product _ _

/-! ### The automorphisms and the gadget row at `D` -/

/-- `σ_g` iterated is `σ_{g^i}` inside `H`. -/
theorem iterate_σ_idx_one {R : Type*} [CommRing R] (S : Setting R) (a : R) :
    ∀ i < S.E.W, (S.E.σ (S.idx 1))^[i] a = S.E.σ (S.idx i) a
  | 0, _ => by simp [S.idx_zero]
  | i + 1, hi => by
    rw [Function.iterate_succ_apply', iterate_σ_idx_one S a i (by omega), σ_idx_succ a hi]

variable (D : Dims)

/-- **`autMW` with the template `κD D 0` is `σ_g`.** -/
theorem decRM_autMW_κ0 {y : List Bool} (hy : y.length = D.N * D.K) :
    decRM D.N D.K (autMW D.N D.K (κD D 0) y) =
      (setting D).E.σ ((setting D).idx 1) (decRM D.N D.K y) := by
  rw [decRM_autMW (κD_pos D 0) hy]
  have := σ_kf D 0 (decRM D.N D.K y)
  rw [Setting.kf, pow_zero] at this
  exact this.symm

/-- The words of the gadget row `G⁽²⁾` as a function of the column. -/
def g1F (one : List Bool) (c : Col D.K) : List Bool :=
  if c.1 = 0 then List.replicate (D.N * D.K) false else gIt D.N D.K one c.2

theorem g1W_eq (one : List Bool) :
    g1W D.N D.K one = (Enum.list (α := Col D.K)).map (g1F D one) := by
  rw [enum_prod, map_product]
  simp only [enum_fin, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, g1F, g1W]
  congr 1
  · simp [List.map_const']
  · simp only [Fin.succ_zero_eq_one, one_ne_zero, ↓reduceIte, Fin.isValue]
    exact List.ext_getElem (by simp) (fun i h1 h2 => by simp)

theorem decRM_g1F (c : Col D.K) :
    decRM D.N D.K (g1F D (true :: List.replicate (D.N * D.K - 1) false) c) = (setting D).G 1 c := by
  show _ = (if (1 : Fin 2) = c.1 then (setting D).D.g c.2 else 0)
  rw [g1F]
  rcases c with ⟨r, i⟩
  fin_cases r
  · simp [decRM_replicate]
  · simp only [Fin.mk_one, one_ne_zero, ↓reduceIte, Fin.isValue]
    rw [decRM_gIt]
    rfl

theorem length_g1F (c : Col D.K) :
    (g1F D (true :: List.replicate (D.N * D.K - 1) false) c).length = D.N * D.K := by
  have hone : (true :: List.replicate (D.N * D.K - 1) false).length = D.N * D.K := by
    have : 1 ≤ D.N * D.K := Nat.one_le_iff_ne_zero.mpr (by have := D.K_pos; positivity)
    simp; omega
  rw [g1F]; split_ifs
  · simp
  · exact length_gIt hone _

/-! ### The word lists of the scheme objects -/

theorem getD_map_lt {β γ : Type} (l : List β) (g : β → γ) (d : γ) {e : ℕ} (he : e < l.length) :
    (l.map g).getD e d = g l[e] := by
  rw [List.getD_eq_getElem _ _ (by simpa using he), List.getElem_map]

/-- The words of `b`. -/
def bsW (ct : CTt D) : List (List Bool) :=
  (Enum.list (α := BCol (Wb D) D.K)).map fun c : BCol (Wb D) D.K => encRM D.N D.K (ct.b c)

/-- The words of `B⁽²⁾`. -/
def B2W (mpk : MPKt D) : List (List Bool) :=
  (Enum.list (α := BCol (Wb D) D.K)).map fun c : BCol (Wb D) D.K => encRM D.N D.K (mpk.B 1 c)

/-- The rows of the `H_k`. -/
def HpsW (mpk : MPKt D) : List (List (List Bool) × List (List Bool)) :=
  (Enum.list (α := Jh D)).map fun k : Jh D =>
    ((Enum.list (α := Col D.K)).map fun c : Col D.K => encRM D.N D.K (mpk.H k 0 c),
      (Enum.list (α := Col D.K)).map fun c : Col D.K => encRM D.N D.K (mpk.H k 1 c))

/-- The words of the helpers `h`. -/
def hsW (ct : CTt D) : List (List Bool) :=
  (Enum.list (α := Jh D × Col D.K)).map fun p : Jh D × Col D.K => encRM D.N D.K (ct.h p.1 p.2)

/-- The words of a key. -/
def ksW (k : Keyt D) : List (List Bool) :=
  (Enum.list (α := KColt D)).map fun c => encRM D.N D.K (k c)

theorem ksW_split (k : Keyt D) : ksW D k =
    (Enum.list (α := Fin (2 ^ D.b) × BCol (Wb D) D.K)).map (fun p => encRM D.N D.K (k (.inl p))) ++
      ((Enum.list (α := Fin (2 ^ D.b) × (Jh D × Col D.K))).map
          (fun p => encRM D.N D.K (k (.inr (.inl p)))) ++
        (Enum.list (α := Col D.K)).map (fun c => encRM D.N D.K (k (.inr (.inr c))))) := by
  rw [ksW, enum_sum, enum_sum]
  simp only [List.map_append, List.map_map]
  rfl

theorem length_col : (Enum.list (α := Col D.K)).length = 2 * D.K := by
  rw [length_enum_prod, enum_fin, enum_fin, List.length_finRange, List.length_finRange]

theorem decRM_sub_enc (a b : Rg D) :
    decRM D.N D.K (subRMW D.N D.K (encRM D.N D.K a) (encRM D.N D.K b)) = a - b := by
  rw [decRM_subRMW (length_encRM _ _ _) (length_encRM _ _ _), decRM_encRM D.K_pos,
    decRM_encRM D.K_pos]

/-- The inputs of the end of decryption at `D`: the registers hold the words of `mpk`, `k_F`,
`ct` and words of `c_F`, `A_F⁽²⁾` (`cFs`, `AF1s`). -/
structure FinD (w : St) (mpk : MPKt D) (F : BP Pos) (k : Keyt D) (ct : CTt D)
    (cFs AF0s AF1s : List (List Bool)) : Prop where
  all : FinAll D.N D.K w (bsW D ct) (B2W D mpk) (HpsW D mpk) (hsW D ct) cFs AF0s AF1s (ksW D k)
    (encRM D.N D.K (mpk.d 0)) (encRM D.N D.K (mpk.d 1))
  r3 : w 3 = true :: List.replicate (D.N * D.K - 1) false
  r12 : (w 12).length = 2 ^ D.b
  r17 : (w 17).length = (Enum.list (α := BCol (Wb D) D.K)).length
  r18 : (w 18).length = (Enum.list (α := Jh D × Col D.K)).length
  r20 : (w 20).length = κD D 0
  r72 : w 72 = encRM D.N D.K ct.cm
  cF : ∀ e (he : e < (Enum.list (α := Col D.K)).length),
    decRM D.N D.K (cFs.getD e []) = evalCiphertext (helperMap D) mpk F ct (Enum.list)[e]
  AF1 : ∀ e (he : e < (Enum.list (α := Col D.K)).length),
    decRM D.N D.K (AF1s.getD e []) = keyPK (helperMap D) mpk F 1 (Enum.list)[e]

/-! ### Indexing the key -/

theorem lt_mul_of {i e n W : ℕ} (hi : i < W) (he : e < n) : i * n + e < W * n :=
  calc i * n + e < i * n + n := by omega
    _ = (i + 1) * n := by ring
    _ ≤ W * n := Nat.mul_le_mul_right _ hi

theorem key_getD_β (k : Keyt D) {i e : ℕ} (hi : i < 2 ^ D.b)
    (he : e < (Enum.list (α := BCol (Wb D) D.K)).length) :
    decRM D.N D.K ((ksW D k).getD (i * (Enum.list (α := BCol (Wb D) D.K)).length + e) []) =
      k (.inl (⟨i, hi⟩, (Enum.list (α := BCol (Wb D) D.K))[e])) := by
  rw [ksW_split, List.getD_append _ _ _ _ (by
    rw [List.length_map, length_enum_prod, enum_fin, List.length_finRange]; exact lt_mul_of hi he)]
  show decRM D.N D.K ((((List.finRange (2 ^ D.b)).product
    (Enum.list (α := BCol (Wb D) D.K))).map _).getD _ _) = _
  rw [getD_map_product_F _ _ _ _ (by simpa using hi) he, decRM_encRM D.K_pos]
  simp

theorem key_getD_η (k : Keyt D) {i e : ℕ} (hi : i < 2 ^ D.b)
    (he : e < (Enum.list (α := Jh D × Col D.K)).length) :
    decRM D.N D.K (((ksW D k).drop (2 ^ D.b * (Enum.list (α := BCol (Wb D) D.K)).length)).getD
        (i * (Enum.list (α := Jh D × Col D.K)).length + e) []) =
      k (.inr (.inl (⟨i, hi⟩, (Enum.list (α := Jh D × Col D.K))[e]))) := by
  rw [ksW_split, List.drop_left' (by
    rw [List.length_map, length_enum_prod, enum_fin, List.length_finRange]),
    List.getD_append _ _ _ _ (by
    rw [List.length_map, length_enum_prod (α := Fin (2 ^ D.b)) (β := Jh D × Col D.K), enum_fin,
      List.length_finRange]; exact lt_mul_of hi he)]
  show decRM D.N D.K ((((List.finRange (2 ^ D.b)).product
    (Enum.list (α := Jh D × Col D.K))).map _).getD _ _) = _
  rw [getD_map_product_F _ _ _ _ (by simpa using hi) he, decRM_encRM D.K_pos]
  simp

theorem key_getD_c (k : Keyt D) {e : ℕ} (he : e < (Enum.list (α := Col D.K)).length) :
    decRM D.N D.K ((((ksW D k).drop (2 ^ D.b * (Enum.list (α := BCol (Wb D) D.K)).length)).drop
        (2 ^ D.b * (Enum.list (α := Jh D × Col D.K)).length)).getD e []) =
      k (.inr (.inr (Enum.list (α := Col D.K))[e])) := by
  rw [ksW_split, List.drop_left' (by
    rw [List.length_map, length_enum_prod, enum_fin, List.length_finRange]),
    List.drop_left' (by rw [List.length_map, length_enum_prod (α := Fin (2 ^ D.b))
      (β := Jh D × Col D.K), enum_fin, List.length_finRange]),
    getD_map_lt _ _ _ he, decRM_encRM D.K_pos]

/-! ### The vectors `x` -/

theorem length_xB (ct : CTt D) (mpk : MPKt D) :
    (List.zipWith (subRMW D.N D.K) (bsW D ct) (B2W D mpk)).length =
      (Enum.list (α := BCol (Wb D) D.K)).length := by
  unfold bsW B2W; rw [List.length_zipWith, List.length_map, List.length_map, min_self]

theorem xB_getD (ct : CTt D) (mpk : MPKt D) {e : ℕ}
    (he : e < (Enum.list (α := BCol (Wb D) D.K)).length) :
    decRM D.N D.K ((List.zipWith (subRMW D.N D.K) (bsW D ct) (B2W D mpk)).getD e []) =
      ct.b (Enum.list (α := BCol (Wb D) D.K))[e] - mpk.B 1 (Enum.list (α := BCol (Wb D) D.K))[e] := by
  rw [List.getD_eq_getElem _ _ (by rw [length_xB]; exact he), List.getElem_zipWith]
  unfold bsW B2W
  rw [List.getElem_map, List.getElem_map]
  exact decRM_sub_enc D _ _

theorem xB_len (ct : CTt D) (mpk : MPKt D) :
    ∀ y ∈ List.zipWith (subRMW D.N D.K) (bsW D ct) (B2W D mpk), y.length = D.N * D.K := by
  intro y hy
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hy
  rw [List.getElem_zipWith]
  unfold bsW
  rw [List.getElem_map]
  exact length_subRMW D.N D.K (length_encRM _ _ _) _

theorem H1s_eq (mpk : MPKt D) : ((HpsW D mpk).map Prod.snd).flatten =
    (Enum.list (α := Jh D × Col D.K)).map
      (fun p : Jh D × Col D.K => encRM D.N D.K (mpk.H p.1 1 p.2)) := by
  rw [enum_prod (α := Jh D) (β := Col D.K), map_product, HpsW, List.map_map]
  rfl

theorem G1s_eq (one : List Bool) :
    (List.replicate (Enum.list (α := Jh D)).length (g1W D.N D.K one)).flatten =
      (Enum.list (α := Jh D × Col D.K)).map (fun p : Jh D × Col D.K => g1F D one p.2) := by
  rw [enum_prod (α := Jh D) (β := Col D.K), map_product, g1W_eq, ← List.map_const']

/-- The vector of part `η`. -/
def xHW (mpk : MPKt D) (ct : CTt D) : List (List Bool) :=
  List.zipWith (subRMW D.N D.K) (hsW D ct) (List.zipWith (subRMW D.N D.K)
    ((HpsW D mpk).map Prod.snd).flatten
    (List.replicate (Enum.list (α := Jh D)).length
      (g1W D.N D.K (true :: List.replicate (D.N * D.K - 1) false))).flatten)

theorem xHW_eq (mpk : MPKt D) (ct : CTt D) : xHW D mpk ct =
    (Enum.list (α := Jh D × Col D.K)).map (fun p : Jh D × Col D.K =>
      subRMW D.N D.K (encRM D.N D.K (ct.h p.1 p.2)) (subRMW D.N D.K
        (encRM D.N D.K (mpk.H p.1 1 p.2))
        (g1F D (true :: List.replicate (D.N * D.K - 1) false) p.2))) := by
  rw [xHW, H1s_eq, G1s_eq, hsW, List.zipWith_map, List.zipWith_self, List.zipWith_map,
    List.zipWith_self]

theorem length_xH (mpk : MPKt D) (ct : CTt D) :
    (xHW D mpk ct).length = (Enum.list (α := Jh D × Col D.K)).length := by
  rw [xHW_eq, List.length_map]

theorem xH_len (mpk : MPKt D) (ct : CTt D) : ∀ y ∈ xHW D mpk ct, y.length = D.N * D.K := by
  intro y hy
  rw [xHW_eq] at hy
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hy
  exact length_subRMW D.N D.K (length_encRM _ _ _) _

theorem xH_getD (mpk : MPKt D) (ct : CTt D) {e : ℕ}
    (he : e < (Enum.list (α := Jh D × Col D.K)).length) :
    decRM D.N D.K ((xHW D mpk ct).getD e []) =
      ct.h (Enum.list (α := Jh D × Col D.K))[e].1 (Enum.list (α := Jh D × Col D.K))[e].2 -
        (mpk.H (Enum.list (α := Jh D × Col D.K))[e].1 1 (Enum.list (α := Jh D × Col D.K))[e].2 -
          (setting D).G 1 (Enum.list (α := Jh D × Col D.K))[e].2) := by
  rw [xHW_eq, getD_map_lt _ _ _ he]
  have hg := length_g1F D (Enum.list (α := Jh D × Col D.K))[e].2
  rw [decRM_subRMW (length_encRM _ _ _) (length_subRMW D.N D.K (length_encRM _ _ _) _),
    decRM_subRMW (length_encRM _ _ _) hg, decRM_encRM D.K_pos, decRM_encRM D.K_pos, decRM_g1F]

/-! ### `finVal` is `μ'` -/

theorem hf_aut (hN : 0 < D.N) (y : List Bool) (hy : y.length = D.N * D.K) :
    (autMW D.N D.K (κD D 0) y).length = D.N * D.K ∧
      decRM D.N D.K (autMW D.N D.K (κD D 0) y) =
        (setting D).E.σ ((setting D).idx 1) (decRM D.N D.K y) :=
  ⟨length_autMW D.N D.K _ y hN, decRM_autMW_κ0 D hy⟩

/-- **The key sums of the machine are those of `decryptRaw`.** -/
theorem finVal_eq_decryptRaw {w : St} {mpk : MPKt D} {F : BP Pos} {k : Keyt D} {ct : CTt D}
    {cFs AF0s AF1s : List (List Bool)} (h : FinD D w mpk F k ct cFs AF0s AF1s) :
    finVal D.N D.K w (bsW D ct) (B2W D mpk) (HpsW D mpk) (hsW D ct) cFs AF1s (ksW D k)
        (encRM D.N D.K (mpk.d 1)) = decryptRaw (helperMap D) mpk F k ct := by
  have hN : 0 < D.N := D.N_pos
  have hφ : ∀ (i : Fin (2 ^ D.b)) (a : Rg D),
      ((setting D).E.σ ((setting D).idx 1))^[i.val] a = (setting D).E.σ ((setting D).idx i.val) a :=
    fun i a => iterate_σ_idx_one (setting D) a i.val i.isLt
  -- part β
  have eB : conjL (autMW D.N D.K (κD D 0))
      (List.zipWith (subRMW D.N D.K) (bsW D ct) (B2W D mpk)) (ksW D k)
        (Enum.list (α := BCol (Wb D) D.K)).length (2 ^ D.b) =
      ∑ i : Fin (2 ^ D.b), ∑ c : BCol (Wb D) D.K,
        (setting D).E.σ ((setting D).idx i) (ct.b c - mpk.B 1 c) * k (.inl (i, c)) := by
    refine (conjL_eq (f := autMW D.N D.K (κD D 0)) ((setting D).E.σ ((setting D).idx 1))
      (hf_aut D hN) (2 ^ D.b) (fun c : BCol (Wb D) D.K => ct.b c - mpk.B 1 c)
      (fun i (c : BCol (Wb D) D.K) => k (.inl (i, c))) _ _
      (length_xB D ct mpk) (xB_len D ct mpk) (fun e he => xB_getD D ct mpk he)
      (fun i hi e he => key_getD_β D k hi he)).trans ?_
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by rw [hφ]
  -- part η
  have eH : conjL (autMW D.N D.K (κD D 0)) (xHW D mpk ct)
      ((ksW D k).drop (2 ^ D.b * (Enum.list (α := BCol (Wb D) D.K)).length))
        (Enum.list (α := Jh D × Col D.K)).length (2 ^ D.b) =
      ∑ i : Fin (2 ^ D.b), ∑ p : Jh D × Col D.K,
        (setting D).E.σ ((setting D).idx i)
          (ct.h p.1 p.2 - (mpk.H p.1 1 p.2 - (setting D).G 1 p.2)) * k (.inr (.inl (i, p))) := by
    refine (conjL_eq (f := autMW D.N D.K (κD D 0)) ((setting D).E.σ ((setting D).idx 1))
      (hf_aut D hN) (2 ^ D.b) (fun p : Jh D × Col D.K =>
        ct.h p.1 p.2 - (mpk.H p.1 1 p.2 - (setting D).G 1 p.2))
      (fun i (p : Jh D × Col D.K) => k (.inr (.inl (i, p)))) _ _
      (length_xH D mpk ct) (xH_len D mpk ct) (fun e he => xH_getD D mpk ct he)
      (fun i hi e he => key_getD_η D k hi he)).trans ?_
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by rw [hφ]
  -- part c_F
  have hA := h.all
  have hFl : (List.zipWith (subRMW D.N D.K) cFs AF1s).length = (Enum.list (α := Col D.K)).length := by
    rw [List.length_zipWith, hA.cFl, hA.A1l, min_self, length_col]
  have eF : dotL (List.zipWith (subRMW D.N D.K) cFs AF1s)
      (((ksW D k).drop (2 ^ D.b * (Enum.list (α := BCol (Wb D) D.K)).length)).drop
        (2 ^ D.b * (Enum.list (α := Jh D × Col D.K)).length)) (2 * D.K) =
      ∑ c : Col D.K, (evalCiphertext (helperMap D) mpk F ct c - keyPK (helperMap D) mpk F 1 c) *
        k (.inr (.inr c)) := by
    rw [← length_col D]
    refine dotL_eq _ _ _ _ (fun e he => ?_) (fun e he => key_getD_c D k he)
    have he1 : e < cFs.length := by rw [hA.cFl, ← length_col D]; exact he
    have he2 : e < AF1s.length := by rw [hA.A1l, ← length_col D]; exact he
    rw [List.getD_eq_getElem _ _ (by rw [hFl]; exact he), List.getElem_zipWith,
      decRM_subRMW (hA.cFw _ (List.getElem_mem he1)) (hA.A1w _ (List.getElem_mem he2)),
      ← List.getD_eq_getElem _ [] he1, ← List.getD_eq_getElem _ [] he2, h.cF e he, h.AF1 e he]
    rfl
  -- assembly
  have hl74 : (w 74).length = (Enum.list (α := Jh D)).length := by
    rw [← hA.Hl, HpsW, List.length_map]
  have hdr := decryptRaw_eq (helperMap D) mpk F k ct
  rw [hdr, finVal, h.r72, h.r20, h.r12, h.r17, h.r18, hl74, h.r3, decRM_encRM D.K_pos,
    decRM_encRM D.K_pos]
  have hxH : List.zipWith (subRMW D.N D.K) (hsW D ct) (List.zipWith (subRMW D.N D.K)
      ((HpsW D mpk).map Prod.snd).flatten (List.replicate (Enum.list (α := Jh D)).length
        (g1W D.N D.K (true :: List.replicate (D.N * D.K - 1) false))).flatten) = xHW D mpk ct := rfl
  rw [hxH, eB, eH, eF]
  have e2 : ∀ (i : Fin (2 ^ D.b)) (p : Jh D × Col D.K),
      (setting D).E.σ ((setting D).idx i) (ct.h p.1 p.2 - (mpk.H p.1 1 p.2 - (setting D).G 1 p.2)) =
        (setting D).E.σ ((setting D).idx i) (ct.h p.1 p.2 - mpk.H p.1 1 p.2 + (setting D).G 1 p.2) :=
    fun i p => by congr 1; ring
  simp only [e2]
  rw [add_assoc]
  rfl

/-- **The end of decryption at `D`**: register `179` holds the decoded bit of `decryptRaw`. -/
theorem exec_finC_D {w : St} {mpk : MPKt D} {F : BP Pos} {k : Keyt D} {ct : CTt D}
    {cFs AF0s AF1s : List (List Bool)} (h : FinD D w mpk F k ct cFs AF0s AF1s) :
    (exec D.N D.K finC w) 179 = [decodeBit D (decryptRaw (helperMap D) mpk F k ct)] := by
  have hK : 2 ≤ D.K := D.hK
  rw [exec_finC D.N_pos hK w h.all, finVal_eq_decryptRaw D h, decodeBit,
    coefG_of_lt _ D.N_pos]

end AdvancedEncryption.ExpLUT.Prog
