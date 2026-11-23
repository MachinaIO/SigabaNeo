import PE.Impl.ExpLUT.Eval

/-!
# The predicate encryption scheme of §5.1

The scheme of ePrint 2026/2539 §5.1 as deterministic functions of explicit coins (the laws of the
coins are `PE.Impl.ExpLUT.Laws`, key generation by box rejection is `PE.Impl.ExpLUT.KeyGen`).

* Index types: `Wb` the columns of `Ā` (so `B⁽¹⁾ ∈ R^{1×m_B}` with columns `BCol = Wb ⊕ Fin τ`,
  `m_B = m̄ + τ`); `J` the helpers, with `je k` the exponent of `k` in `H` (`k = g^{je k}`) and
  `fwd t`, `inv t` the helpers of `g_t` and `g_t^{-1}` (`HelperMap`); `Pos` the attribute
  positions; attributes `x : Pos → ℕ` with symbols `x_t`, encoded as `ν_t = X^{w x_t}` for the
  width `w`.
* **Setup** (`setup`, coins `SetupCoins`): `B⁽¹⁾ = [Ā | g − Ā T]` (`trapRow`), `B⁽²⁾`, `H_k`,
  `a_t`, `A₀`, `A^in_{t,r,j,i}`, `A^aut_{t,r,j,i}`, `d`; `msk = (mpk, T)`.
* **Enc** (`encrypt`, coins `EncCoins`): `b = sB + e_b`, `h_k = sH_k − s_k G + e_k`, the digit
  encodings of `C_{g_t}` (eq. (2)) under `s_{g_t}`, the bottom rows `−s̄ a_t + X^{w x_t} sG + e_t` of
  `C^in_t` and their digit encodings, `c₀ = s(A₀ − G) + e₀`, `c_m = s dᵀ + e_m + ⌊q/2⌉ m`.
* **KeyGen**, the matrices (eq. (3)): `A_F = EvalPK(F, mpk)` (`keyPK`) and
  `M_F = [L | δ₁ ⊗ A_F⁽¹⁾]` (`keyMat`) with rows indexed by the exponents `i < W` and columns
  `KCol`: the blocks `β_i = δ_iᵀ ⊗ σ_i(B⁽¹⁾)`, `η_{i,k} = δ_iᵀ ⊗ σ_i(H_k⁽¹⁾) − δ_{i·k}ᵀ ⊗ G⁽¹⁾`, and
  the last `2τ` columns; the target `d₁ δ₁` (`keyTarget`); a key `k_F` is valid if
  `M_F k_Fᵀ = (d₁ δ₁)ᵀ` (`ValidKey`).
* **Dec** (`decryptRaw`, `decrypt`): `c_F = EvalCT(F, mpk, ct)`, `y_F` and `κ_F` (`decRow`,
  `decConst`), `μ' = c_m − d₂ − (y_F − κ_F) k_Fᵀ`, decoded by an abstract `decode`.
-/

namespace AdvancedEncryption.ExpLUT

open SigabaNeo.Lattices Matrix

variable {R : Type*} [CommRing R] (S : Setting R)

/-- The columns of `B`: those of `Ā`, then the `τ` gadget columns. -/
abbrev BCol (Wb : Type*) (τ : ℕ) := Wb ⊕ Fin τ

/-- The helpers: their exponents in `H`, and the helpers of the binary basis and of its inverses. -/
structure HelperMap (J : Type*) where
  /-- The exponent of the helper `k` (`k = g^{je k}`). -/
  je : J → ℕ
  /-- The helper of `g_t`. -/
  fwd : Fin S.b → J
  /-- The helper of `g_t^{-1}`. -/
  inv : Fin S.b → J
  je_fwd : ∀ t, je (fwd t) = 2 ^ (t : ℕ)
  je_inv : ∀ t, je (inv t) = S.E.W - 2 ^ (t : ℕ)

/-- The row of `δ₁`: the exponent `0`. -/
def Setting.row0 : Fin S.E.W := ⟨0, S.E.W_pos⟩

/-- The row `i · k` of `H`: the exponent `(i + je k) mod W`. -/
def HelperMap.mulRow {S : Setting R} {J : Type*} (M : HelperMap S J) (i : Fin S.E.W) (k : J) :
    Fin S.E.W :=
  ⟨(i + M.je k) % S.E.W, Nat.mod_lt _ S.E.W_pos⟩

variable (Wb J Pos : Type*) [Fintype Wb] [Fintype J] [DecidableEq J]

/-- The master public key. -/
structure MPK where
  /-- `B = [B⁽¹⁾; B⁽²⁾]`. -/
  B : Matrix (Fin 2) (BCol Wb S.τ) R
  /-- `H_k`, `k ∈ J`. -/
  H : J → Matrix (Fin 2) (Col S.τ) R
  /-- `a_t`: the first rows of the attribute ciphertexts. -/
  a : Pos → Col S.τ → R
  /-- `A₀`. -/
  A0 : Matrix (Fin 2) (Col S.τ) R
  /-- `A^in_{t, (r, j, i)}`. -/
  Ain : Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R
  /-- `A^aut_{t, (r, j, i)}`, `t < b`. -/
  Aaut : Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R
  /-- `d = (d₁, d₂)`. -/
  d : Fin 2 → R

/-- The master secret key: the public key and the TrapGen trapdoor `T`. -/
structure MSK where
  /-- The public key. -/
  mpk : MPK S Wb J Pos
  /-- `T ∈ R^{m̄ × τ}` (binary). -/
  T : Matrix Wb (Fin S.τ) R

/-- The coins of `Setup`. -/
structure SetupCoins where
  /-- `Ā` (uniform). -/
  Abar : Wb → R
  /-- `T` (binary). -/
  T : Matrix Wb (Fin S.τ) R
  /-- `B⁽²⁾` (uniform). -/
  B2 : BCol Wb S.τ → R
  /-- `H_k` (uniform). -/
  H : J → Matrix (Fin 2) (Col S.τ) R
  /-- `a_t` (uniform). -/
  a : Pos → Col S.τ → R
  /-- `A₀` (uniform). -/
  A0 : Matrix (Fin 2) (Col S.τ) R
  /-- `A^in` (uniform). -/
  Ain : Pos → Dig S.τ → Matrix (Fin 2) (Col S.τ) R
  /-- `A^aut` (uniform). -/
  Aaut : Fin S.b → Dig S.τ → Matrix (Fin 2) (Col S.τ) R
  /-- `d` (uniform). -/
  d : Fin 2 → R

/-- The coins of `Enc`. -/
structure EncCoins where
  /-- The secret `s̄`. -/
  s : R
  /-- The error of `b`. -/
  eb : BCol Wb S.τ → R
  /-- The errors of the helpers. -/
  eh : J → Col S.τ → R
  /-- The errors of the digit encodings of `C_{g_t}` (flooding). -/
  eaut : Fin S.b → Dig S.τ → Col S.τ → R
  /-- The errors of the attribute ciphertexts `C^in_t` (flooding). -/
  ein : Pos → Col S.τ → R
  /-- The errors of the digit encodings of `C^in_t` (flooding). -/
  edin : Pos → Dig S.τ → Col S.τ → R
  /-- The error of `c₀` (flooding). -/
  e0 : Col S.τ → R
  /-- The error of `c_m`. -/
  em : R

/-- A ciphertext. -/
structure Ciphertext where
  /-- `b = sB + e_b`. -/
  b : BCol Wb S.τ → R
  /-- The helpers `h_k`. -/
  h : J → Col S.τ → R
  /-- The digit encodings of `C_{g_t}` (the RHS data, without `C_{g_t}`, which is recomputed). -/
  caut : Fin S.b → Dig S.τ → Col S.τ → R
  /-- The bottom rows of `C^in_t` (the top rows `a_t` are in `mpk`). -/
  cinBot : Pos → Col S.τ → R
  /-- The digit encodings of `C^in_t`. -/
  cin : Pos → Dig S.τ → Col S.τ → R
  /-- `c₀`. -/
  c0 : Col S.τ → R
  /-- `c_m`. -/
  cm : R

/-- The columns of `M_F` (and of keys): the blocks `β_i` (`i < W`, columns of `B`), the blocks
`η_{i,k}` (`i < W`, `k ∈ J`, `2τ` columns), and the last `2τ` columns. -/
abbrev KCol (τ W : ℕ) := (Fin W × BCol Wb τ) ⊕ (Fin W × J × Col τ) ⊕ Col τ

variable {S Wb J Pos}

/-! ### Setup -/

/-- `B⁽¹⁾ = [Ā | g − Ā T]`. -/
def trapRow (Abar : Wb → R) (T : Matrix Wb (Fin S.τ) R) : BCol Wb S.τ → R :=
  Sum.elim Abar fun c => S.D.g c - ∑ w, Abar w * T w c

/-- **Setup**. -/
def setup (r : SetupCoins S Wb J Pos) : MPK S Wb J Pos × MSK S Wb J Pos :=
  let mpk : MPK S Wb J Pos :=
    { B := Matrix.of ![trapRow r.Abar r.T, r.B2]
      H := r.H, a := r.a, A0 := r.A0, Ain := r.Ain, Aaut := r.Aaut, d := r.d }
  (mpk, ⟨mpk, r.T⟩)

/-! ### Encryption -/

/-- The gadget ciphertext `C^in_t = [a_t; bottom row]`. -/
def cinMat (a bot : Col S.τ → R) : Matrix (Fin 2) (Col S.τ) R := Matrix.of ![a, bot]

/-- The gadget ciphertext `C_{g_t}` of eq. (2), from `H_{g_t^{-1}}` and `h_{g_t^{-1}}`. -/
def autGC (M : HelperMap S J) (H : J → Matrix (Fin 2) (Col S.τ) R) (h : J → Col S.τ → R)
    (t : Fin S.b) : Matrix (Fin 2) (Col S.τ) R :=
  gcAut S (S.kf t) (H (M.inv t)) (h (M.inv t))

/-- The helpers `h_k = s H_k − s_k G + e_k`. -/
def helpers (M : HelperMap S J) (mpk : MPK S Wb J Pos) (r : EncCoins S Wb J Pos) :
    J → Col S.τ → R :=
  fun k => sec r.s ᵥ* mpk.H k - sec (S.E.σ (S.idx (M.je k)) r.s) ᵥ* S.G + r.eh k

/-- The bottom rows of `C^in_t`: `−s̄ a_t + X^{w x_t} s G + e_t`. -/
def cinBots (w : ℕ) (mpk : MPK S Wb J Pos) (x : Pos → ℕ) (r : EncCoins S Wb J Pos) :
    Pos → Col S.τ → R :=
  fun t => -(r.s • mpk.a t) + (S.E.X ^ (w * x t) • sec r.s) ᵥ* S.G + r.ein t

/-- **Enc**: the ciphertext of `m` for the attribute `x`, with the coins `r` (`half = ⌊q/2⌉`). -/
def encrypt (M : HelperMap S J) (w : ℕ) (half : R) (mpk : MPK S Wb J Pos) (x : Pos → ℕ) (m : R)
    (r : EncCoins S Wb J Pos) : Ciphertext S Wb J Pos :=
  { b := sec r.s ᵥ* mpk.B + r.eb
    h := helpers M mpk r
    caut := fun t d => sec (S.E.σ (S.kf t) r.s) ᵥ* mpk.Aaut t d -
      (digits S (autGC M mpk.H (helpers M mpk r) t) d • sec (S.E.σ (S.kf t) r.s)) ᵥ* S.G + r.eaut t d
    cinBot := cinBots w mpk x r
    cin := fun t d => sec r.s ᵥ* mpk.Ain t d -
      (digits S (cinMat (mpk.a t) (cinBots w mpk x r t)) d • sec r.s) ᵥ* S.G + r.edin t d
    c0 := sec r.s ᵥ* mpk.A0 - sec r.s ᵥ* S.G + r.e0
    cm := sec r.s ⬝ᵥ mpk.d + r.em + half * m }

/-! ### The evaluation on the components of `mpk` and `ct` -/

/-- A family over `Fin b`, extended by `0` to `ℕ`. -/
def finExt {α : Type*} [Zero α] (f : Fin S.b → α) (t : ℕ) : α := if h : t < S.b then f ⟨t, h⟩ else 0

/-- The public data of the evaluation. -/
def evalPub (M : HelperMap S J) (mpk : MPK S Wb J Pos) : EvalPub S Pos :=
  { A0 := mpk.A0
    Ain := mpk.Ain
    aut := ⟨finExt fun t => mpk.H (M.fwd t), finExt fun t => mpk.H (M.inv t), finExt mpk.Aaut⟩ }

/-- The ciphertext data of the evaluation. -/
def evalData (M : HelperMap S J) (mpk : MPK S Wb J Pos) (ct : Ciphertext S Wb J Pos) :
    EvalCTData S Pos :=
  { c0 := ct.c0
    Cin := fun t => cinMat (mpk.a t) (ct.cinBot t)
    cin := ct.cin
    aut := ⟨finExt fun t => ct.h (M.fwd t), finExt fun t => ct.h (M.inv t), finExt ct.caut⟩ }

/-! ### Key generation: the matrices -/

/-- `A_F = EvalPK(F, mpk)`. -/
def keyPK (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) : Matrix (Fin 2) (Col S.τ) R :=
  evalPK F (evalPub M mpk)

/-- **`M_F = [L | δ₁ ⊗ A_F⁽¹⁾]`** (eq. (3)). -/
def keyMat (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) :
    Matrix (Fin S.E.W) (KCol Wb J S.τ S.E.W) R :=
  Matrix.of fun i' c => match c with
    | .inl (i, c) => if i' = i then S.E.σ (S.idx i) (mpk.B 0 c) else 0
    | .inr (.inl (i, k, c)) => (if i' = i then S.E.σ (S.idx i) (mpk.H k 0 c) else 0) -
        if i' = M.mulRow i k then S.G 0 c else 0
    | .inr (.inr c) => if i' = S.row0 then keyPK M mpk F 0 c else 0

/-- The target `d₁ δ₁`. -/
def keyTarget (mpk : MPK S Wb J Pos) : Fin S.E.W → R := fun i => if i = S.row0 then mpk.d 0 else 0

/-- A valid key for `F`: `M_F k_Fᵀ = (d₁ δ₁)ᵀ`. -/
def ValidKey (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) (k : KCol Wb J S.τ S.E.W → R) :
    Prop :=
  keyMat M mpk F *ᵥ k = keyTarget mpk

/-! ### Decryption -/

/-- `c_F = EvalCT(F, mpk, ct)`. -/
def evalCiphertext (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (ct : Ciphertext S Wb J Pos) : Col S.τ → R :=
  evalCT F (evalPub M mpk) (evalData M mpk ct)

/-- `y_F = ((σ_i(b))_i, (σ_i(h_k))_{i,k}, c_F)`. -/
def decRow (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) (ct : Ciphertext S Wb J Pos) :
    KCol Wb J S.τ S.E.W → R
  | .inl (i, c) => S.E.σ (S.idx i) (ct.b c)
  | .inr (.inl (i, k, c)) => S.E.σ (S.idx i) (ct.h k c)
  | .inr (.inr c) => evalCiphertext M mpk F ct c

/-- `κ_F = ((σ_i(B⁽²⁾))_i, (σ_i(H_k⁽²⁾) − G⁽²⁾)_{i,k}, A_F⁽²⁾)`. -/
def decConst (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) : KCol Wb J S.τ S.E.W → R
  | .inl (i, c) => S.E.σ (S.idx i) (mpk.B 1 c)
  | .inr (.inl (i, k, c)) => S.E.σ (S.idx i) (mpk.H k 1 c) - S.G 1 c
  | .inr (.inr c) => keyPK M mpk F 1 c

/-- **Dec**, before decoding: `μ' = c_m − d₂ − (y_F − κ_F) k_Fᵀ`. -/
def decryptRaw (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos) (k : KCol Wb J S.τ S.E.W → R)
    (ct : Ciphertext S Wb J Pos) : R :=
  ct.cm - mpk.d 1 - (decRow M mpk F ct - decConst M mpk F) ⬝ᵥ k

/-- **Dec**: `μ'` decoded (the coefficient-wise rounding of `μ' / ⌊q/2⌉` mod 2, abstractly). -/
def decrypt {Msg : Type*} (decode : R → Msg) (M : HelperMap S J) (mpk : MPK S Wb J Pos) (F : BP Pos)
    (k : KCol Wb J S.τ S.E.W → R) (ct : Ciphertext S Wb J Pos) : Msg :=
  decode (decryptRaw M mpk F k ct)

end AdvancedEncryption.ExpLUT
