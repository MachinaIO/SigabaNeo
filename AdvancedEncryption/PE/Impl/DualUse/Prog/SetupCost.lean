import PE.Impl.DualUse.Prog.SetupTime3

/-!
# Linear bounds on the time functions of the setups

The time functions of the setup programs (`Bnd.T`, `countT`, `tTail5`) are nested closures; their
exact values at concrete sizes are too large terms to evaluate. Every one of them is **linear in
the sizes**: `Lin T w E` says `T x S ≤ w · (x + S + E)`. Linear bounds compose along the
combinators (`lin_seq`, `lin_count`, `lin_ite`, `lin_rep`), with `w` and `E` explicit numbers, so a
setup time is bounded by a small arithmetic expression (`lin_bChi`, `lin_bTail3`, `lin_bTailI`,
`lin_tTail5`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-- `T x S ≤ w · (x + S + E)`. -/
def Lin (T : ℕ → ℕ → ℕ) (w E : ℕ) : Prop := ∀ x S, T x S ≤ w * (x + S + E)

theorem Lin.mono {T : ℕ → ℕ → ℕ} {w E w' E' : ℕ} (h : Lin T w E) (hw : w ≤ w') (hE : E ≤ E') :
    Lin T w' E' := fun x S =>
  (h x S).trans (Nat.mul_le_mul hw (by omega))

theorem lin_tBit : Lin tBit 2 3 := fun x S => by unfold tBit; omega

theorem lin_tCoin : Lin tCoin 6 3 := fun x S => by unfold tCoin; omega

theorem lin_seq {T U : ℕ → ℕ → ℕ} {w₁ E₁ w₂ E₂ : ℕ} (hT : Lin T w₁ E₁) (hU : Lin U w₂ E₂)
    (a s : ℕ) : Lin (fun x S => T x S + U (x + a) (S + s)) (w₁ + w₂) (E₁ + E₂ + a + s) :=
  fun x S => by
    have h1 := (hT x S).trans (Nat.mul_le_mul_left w₁ (show x + S + E₁ ≤ x + S + (E₁ + E₂ + a + s)
      by omega))
    have h2 := (hU (x + a) (S + s)).trans (Nat.mul_le_mul_left w₂
      (show x + a + (S + s) + E₂ ≤ x + S + (E₁ + E₂ + a + s) by omega))
    show T x S + U (x + a) (S + s) ≤ _
    rw [Nat.add_mul]; omega

theorem lin_count {T : ℕ → ℕ → ℕ} {w E : ℕ} (hT : Lin T w E) (n a s : ℕ) :
    Lin (countT n a s T) (8 * n + 8 + n * (w + 3)) (n * a + n * s + E + 3) := fun x S => by
  set Y := x + S + (n * a + n * s + E + 3)
  have hT' := (hT (x + n * a) (S + n * s)).trans (Nat.mul_le_mul_left w
    (show x + n * a + (S + n * s) + E ≤ Y by omega))
  have e1 : (2 * n + 1) * (4 * (x + S) + 12) ≤ (8 * n + 4) * Y := by
    calc (2 * n + 1) * (4 * (x + S) + 12) ≤ (2 * n + 1) * (4 * Y) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = (8 * n + 4) * Y := by ring
  have e2 : n * (2 * (x + n * a + (S + n * s)) + 3 + T (x + n * a) (S + n * s) + 1) ≤
      n * ((w + 3) * Y) := Nat.mul_le_mul_left _ (by rw [Nat.add_mul]; omega)
  have e3 : n * ((w + 3) * Y) = n * (w + 3) * Y := by ring
  unfold countT
  have : (8 * n + 8 + n * (w + 3)) * Y = (8 * n + 4) * Y + 4 * Y + n * (w + 3) * Y := by ring
  omega

theorem lin_ite {T U : ℕ → ℕ → ℕ} {w₁ E₁ w₂ E₂ : ℕ} (hT : Lin T w₁ E₁) (hU : Lin U w₂ E₂) :
    Lin (fun x S => max (T x S) (U x S) + 1) (w₁ + w₂ + 1) (E₁ + E₂ + 1) := fun x S => by
  have h1 := (hT x S).trans (Nat.mul_le_mul_left w₁ (show x + S + E₁ ≤ x + S + (E₁ + E₂ + 1)
    by omega))
  have h2 := (hU x S).trans (Nat.mul_le_mul_left w₂ (show x + S + E₂ ≤ x + S + (E₁ + E₂ + 1)
    by omega))
  show max (T x S) (U x S) + 1 ≤ _
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  have := max_le (h1.trans (Nat.le_add_right _ (w₂ * (x + S + (E₁ + E₂ + 1)))))
    (h2.trans (Nat.le_add_left _ (w₁ * (x + S + (E₁ + E₂ + 1)))))
  omega

/-! ### Bundled bounds -/

theorem lin_Bseq {B C : Bnd} {w₁ E₁ w₂ E₂ : ℕ} (hB : Lin B.T w₁ E₁) (hC : Lin C.T w₂ E₂) :
    Lin (B.seq C).T (w₁ + w₂) (E₁ + E₂ + B.a + B.s) := lin_seq hB hC B.a B.s

theorem lin_Bcount {B : Bnd} {w E : ℕ} (hB : Lin B.T w E) (n : ℕ) :
    Lin (B.count n).T (8 * n + 8 + n * (w + 3)) (n * B.a + n * B.s + E + 3) :=
  lin_count hB n B.a B.s

theorem lin_Bite {B C : Bnd} {w₁ E₁ w₂ E₂ : ℕ} (hB : Lin B.T w₁ E₁) (hC : Lin C.T w₂ E₂) :
    Lin (B.ite C).T (w₁ + w₂ + 1) (E₁ + E₂ + 1) := lin_ite hB hC

theorem lin_Bprim (a s : ℕ) : Lin (Bnd.prim a s).T 2 3 := lin_tBit

theorem lin_Brep {B : Bnd} {w E : ℕ} (hB : Lin B.T w E) :
    ∀ n, Lin (B.rep n).T (n * w + 2) (n * (E + B.a + B.s) + 3)
  | 0 => by show Lin (Bnd.prim 0 0).T _ _; simpa using lin_Bprim 0 0
  | n + 1 => by
    have h := lin_Bseq hB (lin_Brep hB n)
    refine h.mono (by ring_nf; omega) (by ring_nf; omega)

/-! ### The blocks of the setups -/

theorem lin_bCoin : Lin bCoin.T 6 3 := lin_tCoin

theorem lin_bCoins (n : ℕ) : Lin (bCoins n).T (8 * n + 8 + n * (6 + 3)) (n * 1 + n * 0 + 3 + 3) :=
  lin_Bcount lin_bCoin n

theorem lin_bZeros (n : ℕ) : Lin (bZeros n).T (8 * n + 8 + n * (2 + 3)) (n * 1 + n * 0 + 3 + 3) :=
  lin_Bcount (lin_Bprim 1 0) n

theorem lin_bWord : ∀ n, Lin (bWord n).T (2 * n + 2) (4 * n + 3)
  | 0 => lin_Bprim 0 0
  | n + 1 => (lin_Bseq (lin_Bprim 1 0) (lin_bWord n)).mono (by ring_nf; omega)
      (by simp [Bnd.prim]; omega)

theorem lin_bLeaf (K L : ℕ) : Lin (bLeaf K L).T (2 + ((2 * L + 2) + (8 * (K - L) + 8 + (K - L) * 5)))
    (3 + ((4 * L + 3) + ((K - L) * 1 + (K - L) * 0 + 3 + 3) + L + 0) + 0 + 0) := by
  have h := lin_Bseq (lin_Bprim 0 0) (lin_Bseq (lin_bWord L) (lin_Bcount (lin_Bprim 1 0) (K - L)))
  refine h.mono (by ring_nf; omega) ?_
  simp only [bWord_a, bWord_s, Bnd.prim]
  omega
where
  bWord_a : ∀ n, (bWord n).a = n
    | 0 => rfl
    | n + 1 => by simp [bWord, Bnd.seq, Bnd.prim, bWord_a n]; omega
  bWord_s : ∀ n, (bWord n).s = 0
    | 0 => rfl
    | n + 1 => by simp [bWord, Bnd.seq, Bnd.prim, bWord_s n]

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

theorem lin_bChain (K L : ℕ) {w E : ℕ} (hL : Lin (bLeaf K L).T w E) :
    ∀ f, Lin (bChain K L f).T ((f + 1) * w + 3 * f) ((f + 1) * E + 4 * f)
  | 0 => by simpa [bChain] using hL
  | f + 1 => by
    have h := lin_Bite hL (lin_Bseq (lin_Bprim 0 0) (lin_bChain K L hL f))
    refine h.mono (by ring_nf; omega) ?_
    simp only [Bnd.prim]; ring_nf; omega

theorem Bnd.rep_a (B : Bnd) : ∀ n, (B.rep n).a = n * B.a
  | 0 => by simp [Bnd.rep, Bnd.prim]
  | n + 1 => by simp only [Bnd.rep, Bnd.seq, Bnd.rep_a B n]; ring

theorem Bnd.rep_s (B : Bnd) : ∀ n, (B.rep n).s = n * B.s
  | 0 => by simp [Bnd.rep, Bnd.prim]
  | n + 1 => by simp only [Bnd.rep, Bnd.seq, Bnd.rep_s B n]; ring

theorem lin_bCoin2 : Lin bCoin2.T 6 3 := lin_tCoin

theorem lin_bStep : Lin bStep.T (2 + 2 + 1 + 2) (3 + 3 + 1 + 3 + 0 + 1) := by
  have h := lin_Bseq (lin_Bite (lin_Bprim 0 1) (lin_Bprim 0 0)) (lin_Bprim 0 0)
  simpa [bStep, Bnd.ite, Bnd.prim] using h

theorem bLeaf_a (K L : ℕ) (h : L ≤ K) : (bLeaf K L).a = K := by
  simp only [bLeaf, Bnd.seq, Bnd.count, Bnd.prim, lin_bLeaf.bWord_a]; omega

theorem bLeaf_s (K L : ℕ) : (bLeaf K L).s = 0 := by
  simp [bLeaf, Bnd.seq, Bnd.count, Bnd.prim, lin_bLeaf.bWord_s]

theorem bChain_a (K L : ℕ) (h : L ≤ K) : ∀ f, (bChain K L f).a = K
  | 0 => bLeaf_a K L h
  | f + 1 => by simp only [bChain, Bnd.ite, Bnd.seq, Bnd.prim, bLeaf_a K L h, bChain_a K L h f]; simp

theorem bChain_s (K L : ℕ) : ∀ f, (bChain K L f).s = 0
  | 0 => bLeaf_s K L
  | f + 1 => by simp only [bChain, Bnd.ite, Bnd.seq, Bnd.prim, bLeaf_s K L, bChain_s K L f]; simp

theorem bChi_a : bChi.a = Params.Kp := by
  have h : 6 ≤ Params.Kp := by rw [Params.Kp_def]; norm_num
  simp only [bChi, bCbd, Bnd.seq, Bnd.rep_a, bChain_a _ _ h, bCoin2, bStep, Bnd.ite, Bnd.prim]
  simp

theorem bChi_s : bChi.s = 64 := by
  simp only [bChi, bCbd, Bnd.seq, Bnd.rep_s, bChain_s, bCoin2, bStep, Bnd.ite, Bnd.prim]
  simp

set_option maxRecDepth 100000 in
/-- **The χ sampler of `confP`** is linear. -/
theorem lin_bChi : Lin bChi.T (2 ^ 40) (2 ^ 40) := by
  have hC := lin_bChain Params.Kp 6 (lin_bLeaf Params.Kp 6) (16 + 16)
  have hD : Lin ((((Bnd.prim 0 0).ite (Bnd.prim 0 0)).seq (Bnd.prim 0 0))).T (2 + 2 + 1 + 2)
      (3 + 3 + 1 + 3 + 0 + 0) := by
    have h := lin_Bseq (lin_Bite (lin_Bprim 0 0) (lin_Bprim 0 0)) (lin_Bprim 0 0)
    simpa [Bnd.ite, Bnd.prim] using h
  have h := lin_Bseq (lin_Brep lin_bCoin2 (16 + 16)) (lin_Bseq (lin_Brep (lin_Bprim 0 1) 16)
    (lin_Bseq (lin_Brep lin_bStep 16) (lin_Bseq (lin_Brep hD 16) hC)))
  refine h.mono ?_ ?_ <;>
    simp only [Bnd.rep_a, Bnd.rep_s, bCoin2, bStep, Bnd.ite, Bnd.seq, Bnd.prim, Params.Kp_def] <;>
    norm_num

end AdvancedEncryption.DualUse.Prog

/-! ### Linear bounds as data

`LB` records a weight and an offset; `LB.seq`, `LB.cnt` follow `lin_Bseq`, `lin_Bcount`, so the
linear bounds of the setup tails are explicit terms (`lbRest`, `lbTail3`, `lbTailI`), proved
generically (`lin_bRest`, `lin_bTail3`, `lin_bTailI`) and evaluated at `confP` by arithmetic only. -/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Encode SigabaNeo.Lattices
open AdvancedEncryption.RingBTVW AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

/-- A weight and an offset. -/
structure LB where
  w : ℕ
  E : ℕ

/-- `B.T` has the linear bound `l`. -/
def HasLB (B : Bnd) (l : LB) : Prop := Lin B.T l.w l.E

def LB.seq (l m : LB) (B : Bnd) : LB := ⟨l.w + m.w, l.E + m.E + B.a + B.s⟩
def LB.cnt (l : LB) (n : ℕ) (B : Bnd) : LB := ⟨8 * n + 8 + n * (l.w + 3), n * B.a + n * B.s + l.E + 3⟩
def LB.prim : LB := ⟨2, 3⟩
def LB.coin : LB := ⟨6, 3⟩

theorem HasLB.seq {B C : Bnd} {l m : LB} (hB : HasLB B l) (hC : HasLB C m) :
    HasLB (B.seq C) (l.seq m B) := lin_Bseq hB hC

theorem HasLB.cnt {B : Bnd} {l : LB} (hB : HasLB B l) (n : ℕ) : HasLB (B.count n) (l.cnt n B) :=
  lin_Bcount hB n

theorem hasLB_prim (a s : ℕ) : HasLB (Bnd.prim a s) LB.prim := lin_Bprim a s
theorem hasLB_coin : HasLB bCoin LB.coin := lin_bCoin

/-- The bound of `n` fair bits. -/
def lbCoins (n : ℕ) : LB := LB.coin.cnt n bCoin
/-- The bound of `n` zeros. -/
def lbZeros (n : ℕ) : LB := LB.prim.cnt n (Bnd.prim 1 0)

theorem hasLB_coins (n : ℕ) : HasLB (bCoins n) (lbCoins n) := hasLB_coin.cnt n
theorem hasLB_zeros (n : ℕ) : HasLB (bZeros n) (lbZeros n) := (hasLB_prim 1 0).cnt n

def lbEntB (N K : ℕ) : LB := LB.coin.seq (lbZeros (N * K - 1)) bCoin
def lbEntF (K w : ℕ) : LB := (lbCoins (min w K)).seq (lbZeros (K - w)) (bCoins (min w K))

theorem hasLB_entB (N K : ℕ) : HasLB (bEntB N K) (lbEntB N K) := hasLB_coin.seq (hasLB_zeros _)
theorem hasLB_entF (K w : ℕ) : HasLB (bEntF K w) (lbEntF K w) :=
  (hasLB_coins _).seq (hasLB_zeros _)

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Bχ : Bnd) (lχ : LB)

/-- The bound of the coins `rest`. -/
def lbRest : LB :=
  (lbCoins (N * K)).seq ((lχ.cnt ((Enum.list (α := Fin c.d)).length * N) Bχ).seq
    (((lχ.cnt N Bχ).seq ((lχ.cnt ((Enum.list (α := RingBTVW.Col k)).length * N) Bχ).seq
        (lχ.cnt ((Enum.list (α := RingBTVW.Col k)).length * N) Bχ)
        (Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)))
        (Bχ.count N)).seq
      (((lbEntB N K).cnt (nR hk c) (bEntB N K)).seq (lχ.cnt N Bχ) ((bEntB N K).count (nR hk c)))
      ((Bχ.count N).seq ((Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)).seq
        (Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)))))
    (Bχ.count ((Enum.list (α := Fin c.d)).length * N)))
    (bCoins (N * K))

theorem hasLB_rest (hχ : HasLB Bχ lχ) : HasLB (bRest hk c Bχ) (lbRest hk c Bχ lχ) :=
  (hasLB_coins _).seq ((hχ.cnt _).seq (((hχ.cnt N).seq
    ((hχ.cnt ((Enum.list (α := RingBTVW.Col k)).length * N)).seq
      (hχ.cnt ((Enum.list (α := RingBTVW.Col k)).length * N)))).seq
    (((hasLB_entB N K).cnt (nR hk c)).seq (hχ.cnt N))))

/-- The bound of the random part of the secret of hybrid 3. -/
def lbTail3 : LB :=
  (lbCoins ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))).seq
    ((lbCoins (nW hk c)).seq ((lbCoins (N * K)).seq ((lbRest hk c Bχ lχ).seq
      ((lbEntF K c.w).cnt (nE (N := N) hk) (bEntF K c.w)) (bRest hk c Bχ)) (bCoins (N * K)))
      (bCoins (nW hk c)))
    (bCoins ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K))))

theorem hasLB_tail3 (hχ : HasLB Bχ lχ) : HasLB (bTail3 hk c Bχ) (lbTail3 hk c Bχ lχ) :=
  (hasLB_coins _).seq ((hasLB_coins _).seq ((hasLB_coins _).seq ((hasLB_rest hk c Bχ lχ hχ).seq
    ((hasLB_entF K c.w).cnt _))))

/-- The bound of the coins of `Enc`. -/
def lbEncCoins : LB :=
  (lbCoins (N * K)).seq ((lχ.cnt ((Enum.list (α := Fin c.d)).length * N) Bχ).seq
    (((lχ.cnt N Bχ).seq ((lχ.cnt ((Enum.list (α := RingBTVW.Col k)).length * N) Bχ).seq
        (lχ.cnt ((Enum.list (α := RingBTVW.Col k)).length * N) Bχ)
        (Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)))
        (Bχ.count N)).seq
      (((lbEntB N K).cnt (nR hk c) (bEntB N K)).seq (((lbEntF K c.w).cnt (nE (N := N) hk)
        (bEntF K c.w)).seq (lχ.cnt N Bχ) ((bEntF K c.w).count (nE (N := N) hk)))
        ((bEntB N K).count (nR hk c)))
      ((Bχ.count N).seq ((Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)).seq
        (Bχ.count ((Enum.list (α := RingBTVW.Col k)).length * N)))))
    (Bχ.count ((Enum.list (α := Fin c.d)).length * N)))
    (bCoins (N * K))

theorem hasLB_encCoins (hχ : HasLB Bχ lχ) : HasLB (bEncCoins hk c Bχ) (lbEncCoins hk c Bχ lχ) :=
  (hasLB_coins _).seq ((hχ.cnt _).seq (((hχ.cnt N).seq
    ((hχ.cnt ((Enum.list (α := RingBTVW.Col k)).length * N)).seq
      (hχ.cnt ((Enum.list (α := RingBTVW.Col k)).length * N)))).seq
    (((hasLB_entB N K).cnt (nR hk c)).seq (((hasLB_entF K c.w).cnt (nE (N := N) hk)).seq
      (hχ.cnt N)))))

/-- The bound of the uniform ciphertext. -/
def lbCt : LB :=
  (lbCoins (nPsi (N := N) hk)).seq ((lbCoins (nC0 (N := N) (K := K) c)).seq
    ((lbCoins (nC1 (N := N) (K := K) (k := k))).seq ((lbCoins (nCj (N := N) hk)).seq
      (lbCoins (N * K)) (bCoins (nCj (N := N) hk))) (bCoins (nC1 (N := N) (K := K) (k := k))))
      (bCoins (nC0 (N := N) (K := K) c)))
    (bCoins (nPsi (N := N) hk))

theorem hasLB_ct : HasLB (bCt hk c) (lbCt hk c) :=
  (hasLB_coins _).seq ((hasLB_coins _).seq ((hasLB_coins _).seq ((hasLB_coins _).seq
    (hasLB_coins _))))

/-- The bound of the random part of the secret of the ideal side. -/
def lbTailI : LB :=
  (lbCoins ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)))).seq
    ((lbCoins (nW hk c)).seq ((lbCoins (N * K)).seq ((lbEncCoins hk c Bχ lχ).seq (lbCt hk c)
      (bEncCoins hk c Bχ)) (bCoins (N * K))) (bCoins (nW hk c)))
    (bCoins ((Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K))))

theorem hasLB_tailI (hχ : HasLB Bχ lχ) : HasLB (bTailI hk c Bχ) (lbTailI hk c Bχ lχ) :=
  (hasLB_coins _).seq ((hasLB_coins _).seq ((hasLB_coins _).seq
    ((hasLB_encCoins hk c Bχ lχ hχ).seq (hasLB_ct hk c))))

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Encode SigabaNeo.Lattices
open AdvancedEncryption.RingBTVW AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

/-! ### The setup of hybrid 5 -/

section Tail5

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The linear bound of `tEntB`. -/
theorem lin_tEntB (N K : ℕ) :
    Lin (tEntB N K) (6 + (8 * (N * K - 1) + 8 + (N * K - 1) * (2 + 3)))
      (3 + ((N * K - 1) * 1 + (N * K - 1) * 0 + 3 + 3) + 1 + 0) :=
  lin_seq lin_tCoin (lin_count lin_tBit (N * K - 1) 1 0) 1 0

/-- The linear bound of `tEntF`. -/
theorem lin_tEntF (K w : ℕ) :
    Lin (tEntF K w) (8 * min w K + 8 + min w K * (6 + 3) + (8 * (K - w) + 8 + (K - w) * (2 + 3)))
      (min w K * 1 + min w K * 0 + 3 + 3 + ((K - w) * 1 + (K - w) * 0 + 3 + 3) + min w K + 0) :=
  lin_seq (lin_count lin_tCoin (min w K) 1 0) (lin_count lin_tBit (K - w) 1 0) (min w K) 0

/-- The weight of the random part of the secret of hybrid 5. -/
def wTail5 : ℕ :=
  (8 * (N * K) + 8 + N * K * (6 + 3)) + (8 * nW hk c + 8 + nW hk c * (6 + 3)) +
    (8 * nR hk c + 8 + nR hk c * ((6 + (8 * (N * K - 1) + 8 + (N * K - 1) * (2 + 3))) + 3)) +
    (8 * nE (N := N) hk + 8 + nE (N := N) hk * ((8 * min c.w K + 8 + min c.w K * (6 + 3) +
      (8 * (K - c.w) + 8 + (K - c.w) * (2 + 3))) + 3))

/-- The offset of the random part of the secret of hybrid 5. -/
def eTail5 : ℕ :=
  (N * K * 1 + N * K * 0 + 3 + 3) + (nW hk c * 1 + nW hk c * 0 + 3 + 3) +
    (nR hk c * (1 + (N * K - 1)) + nR hk c * (0 + 0) +
      (3 + ((N * K - 1) * 1 + (N * K - 1) * 0 + 3 + 3) + 1 + 0) + 3) +
    (nE (N := N) hk * (min c.w K + (K - c.w)) + nE (N := N) hk * (0 + 0) +
      (min c.w K * 1 + min c.w K * 0 + 3 + 3 + ((K - c.w) * 1 + (K - c.w) * 0 + 3 + 3) + min c.w K + 0)
      + 3) + N * K + nW hk c + nR hk c * (1 + (N * K - 1))

theorem lin_tTail5 : Lin (tTail5 hk c) (wTail5 hk c) (eTail5 hk c) := fun x S => by
  have h1 := lin_count lin_tCoin (N * K) 1 0 x S
  have h2 := lin_count lin_tCoin (nW hk c) 1 0 (x + N * K) (S + 0)
  have h3 := lin_count (lin_tEntB N K) (nR hk c) (1 + (N * K - 1)) (0 + 0)
    (x + N * K + nW hk c) (S + 0 + 0)
  have h4 := lin_count (lin_tEntF K c.w) (nE (N := N) hk) (min c.w K + (K - c.w)) (0 + 0)
    (x + N * K + nW hk c + nR hk c * (1 + (N * K - 1))) (S + 0 + 0 + nR hk c * (0 + 0))
  unfold tTail5 tCoins
  set Y := x + S + eTail5 hk c with hY
  have k1 := h1.trans (Nat.mul_le_mul_left _ (show _ ≤ Y by rw [hY]; unfold eTail5; omega))
  have k2 := h2.trans (Nat.mul_le_mul_left _ (show _ ≤ Y by rw [hY]; unfold eTail5; omega))
  have k3 := h3.trans (Nat.mul_le_mul_left _ (show _ ≤ Y by rw [hY]; unfold eTail5; omega))
  have k4 := h4.trans (Nat.mul_le_mul_left _ (show _ ≤ Y by rw [hY]; unfold eTail5; omega))
  have e : wTail5 hk c * Y = (8 * (N * K) + 8 + N * K * (6 + 3)) * Y +
      (8 * nW hk c + 8 + nW hk c * (6 + 3)) * Y +
      (8 * nR hk c + 8 + nR hk c * ((6 + (8 * (N * K - 1) + 8 + (N * K - 1) * (2 + 3))) + 3)) * Y +
      (8 * nE (N := N) hk + 8 + nE (N := N) hk * ((8 * min c.w K + 8 + min c.w K * (6 + 3) +
        (8 * (K - c.w) + 8 + (K - c.w) * (2 + 3))) + 3)) * Y := by
    unfold wTail5; ring
  omega

end Tail5

/-! ### Scratch thresholds -/

theorem Bnd.rep_S₀_le (B : Bnd) : ∀ n, (B.rep n).S₀ ≤ B.S₀
  | 0 => Nat.zero_le _
  | n + 1 => max_le le_rfl (Bnd.rep_S₀_le B n)

theorem bChain_S₀_le (K L : ℕ) : ∀ f, (bChain K L f).S₀ ≤ K
  | 0 => by simp [bChain, bLeaf, Bnd.seq, Bnd.count, Bnd.prim, bWord_S₀]
  | f + 1 => by
    simp only [bChain, Bnd.ite, Bnd.seq, Bnd.prim]
    have := bChain_S₀_le K L f
    have : (bLeaf K L).S₀ ≤ K := by simp [bLeaf, Bnd.seq, Bnd.count, Bnd.prim, bWord_S₀]
    omega
where
  bWord_S₀ : ∀ n, (bWord n).S₀ = 0
    | 0 => rfl
    | n + 1 => by simp [bWord, Bnd.seq, Bnd.prim, bWord_S₀ n]

theorem bChi_S₀ : bChi.S₀ ≤ Params.Kp := by
  have h1 := Bnd.rep_S₀_le bCoin2 (16 + 16)
  have h2 := Bnd.rep_S₀_le (Bnd.prim 0 1) 16
  have h3 := Bnd.rep_S₀_le bStep 16
  have h4 := Bnd.rep_S₀_le (((Bnd.prim 0 0).ite (Bnd.prim 0 0)).seq (Bnd.prim 0 0)) 16
  have h5 := bChain_S₀_le Params.Kp 6 (16 + 16)
  have hK : 1 ≤ Params.Kp := by rw [Params.Kp_def]; norm_num
  simp only [bChi, bCbd, Bnd.seq, bCoin2, bStep, Bnd.ite, Bnd.prim, max_self] at *
  omega

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-! ### Only the growth of the χ sampler enters the bounds -/

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (lχ : LB)

theorem lbTail3_congr {Bχ : Bnd} {A S : ℕ} (hA : Bχ.a = A) (hS : Bχ.s = S) :
    lbTail3 hk c Bχ lχ = lbTail3 hk c (Bnd.prim A S) lχ := by
  simp only [lbTail3, lbRest, LB.seq, LB.cnt, bRest, Bnd.seq, Bnd.count, Bnd.prim, hA, hS]

theorem lbTailI_congr {Bχ : Bnd} {A S : ℕ} (hA : Bχ.a = A) (hS : Bχ.s = S) :
    lbTailI hk c Bχ lχ = lbTailI hk c (Bnd.prim A S) lχ := by
  simp only [lbTailI, lbEncCoins, LB.seq, LB.cnt, bEncCoins, Bnd.seq, Bnd.count, Bnd.prim, hA, hS]

end AdvancedEncryption.DualUse.Prog

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Encode SigabaNeo.Lattices
open AdvancedEncryption.RingBTVW AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k) (Bχ : Bnd)

/-- The counts of the setups, summed. -/
def cntSum : ℕ :=
  (Enum.list (α := Fin 1)).length * ((Enum.list (α := Fin c.d)).length * (N * K)) + nW hk c +
    N * K + (Enum.list (α := Fin c.d)).length * N + N + 2 * ((Enum.list (α := RingBTVW.Col k)).length * N)
    + nR hk c + nE (N := N) hk + K + c.w + nPsi (N := N) hk + nC0 (N := N) (K := K) c +
    nC1 (N := N) (K := K) (k := k) + nCj (N := N) hk + 1

theorem bTail3_S₀ : (bTail3 hk c Bχ).S₀ ≤ Bχ.S₀ + cntSum hk c := by
  simp only [bTail3, bRest, Bnd.seq, Bnd.count, bCoins, bZeros, bEntB, bEntF, bCoin, Bnd.prim,
    cntSum, max_le_iff]
  and_intros <;> omega

theorem bTailI_S₀ : (bTailI hk c Bχ).S₀ ≤ Bχ.S₀ + cntSum hk c := by
  simp only [bTailI, bEncCoins, bCt, Bnd.seq, Bnd.count, bCoins, bZeros, bEntB, bEntF, bCoin,
    Bnd.prim, cntSum, max_le_iff]
  and_intros <;> omega

end AdvancedEncryption.DualUse.Prog
