import PE.Impl.ExpLUT.Laws
import PE.Impl.ExpLUT.KeyGen
import PE.Impl.ExpLUT.NegacyclicNorm
import PE.BranchingProgram
import SigabaNeoStd.Lattices.Algo.MersenneWords
import SigabaNeoStd.Encode.Ring
import CslibFrontier.Probability.BitString
import SigabaNeo.Trusted.Machine

/-!
# The words of the ExpLUT scheme (package F: formats)

The concrete instance of the scheme of §5 (`PE.Impl.ExpLUT.Scheme`) that the machines implement,
and the bit words of its keys, ciphertexts and predicates.

**Dimensions** (`Dims`): the ring `Rg D = ℤ_{2^K − 1}[X]/(X^N + 1)`, `N = 2^e`, with the
automorphisms of `expRingMersenne` (`W = 2^b`, `W⁻¹ = 2^{K − b}`), the binary gadget digits
(`τ = K`), the canonical `H` (`idx j = g^j`): `setting D`. The columns of `Ā` are `Wb D = Fin mb`,
the helpers `J = Fin b × Fin 2` (`(t, 0)`: `g_t`, exponent `2^t`; `(t, 1)`: `g_t⁻¹`, exponent
`W − 2^t`; `helperMap D`), the positions `Pos = Fin 16` (the symbols of the width `w8`).

**Ring elements** are `N` blocks of `K` bits, least significant first, each the canonical word of
its coefficient in `[0, 2^K − 1)` (`rEnc D`, `encRM`; the all-ones word never occurs in an output).
Matrices and families are written in the order of the explicit enumerations (`Enum`) of their index
types, records as the concatenations of their fields:

* `mpkEnc`: `B` (`Fin 2 × BCol`, `BCol = Wb ⊕ Fin K`), `H` (`J → Fin 2 × Col`), `a`
  (`Pos → Col`), `A₀`, `A^in` (`Pos → Dig → Fin 2 × Col`), `A^aut` (`Fin b → Dig → Fin 2 × Col`),
  `d` (`Fin 2`), with `Col = Fin 2 × Fin K`, `Dig = Fin 2 × Col × Fin K`;
* `mskEnc`: `mpk`, then `T` (`Wb × Fin K`);
* `ctEnc`: `b` (`BCol`), `h` (`J → Col`), `c^aut` (`Fin b → Dig → Col`), the bottom rows of
  `C^in` (`Pos → Col`), `c^in` (`Pos → Dig → Col`), `c₀` (`Col`), `c_m`;
* `skEnc`: `mpk`, then the key `k_F` (`KCol = (Fin W × BCol) ⊕ (Fin W × J × Col) ⊕ Col`).

**Predicate words** (`predWord F`, `predLen = 211 · 2^22` bits): the 15 transition tables, then the
output table, each indexed by `u = z + 2^14 a` (`z` the 14-bit state, `a` the 8-bit symbol), the
index of the lookup tables of §4.4 (`L_i(z + w x)`): entry `(i, u)` is the 14-bit state at bit
`14 (2^22 i + u)`, least significant first; output bit `u` is at `210 · 2^22 + u`.
`progOf C` reads a word back (`progOf_predWord`). `bpOf F` is the program as a branching program of
the scheme (`T = 16`, `w = 2^14`, `|Σ| = 2^8`, read map `i ↦ i`), well formed for `W = 2^b ≥ 2^22`
(`wf_bpOf`), with `eval (bpOf F) x = [F(x)]` (`eval_bpOf`).

**Attributes**: the universe's 128 bits (`encAttribute w8`, 16 symbols of 8 bits, most significant
first); `symOf w t` reads symbol `t` (`symOf_encAttribute`). **Messages**: one bit `[μ]`, the ring
element `msgR μ ∈ {0, 1}`, `half = 2^{K − 1}`.

**Laws realizable from fair coins.** `ℤ_{2^K − 1}` has an odd number of elements, so no machine
with a bounded clock samples it uniformly. The public matrices of `Setup` are drawn from `unifW D`:
`N K` fair bits read by `decRM` (`0` has probability `2^{1−K}`, the other residues `2^{−K}`, per
coefficient), `setupCoinsLawW D υ χT` is `setupCoinsLaw` with every uniform entry replaced by
independent `υ` entries. The machines' `Setup` realizes `setupCoinsLawW D (unifW D) χT`; its
statistical distance to `setupCoinsLaw` is at most (number of public coefficients) `· 2^{−K}`.
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo Matrix Cslib
open AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram

/-! ### Dimensions and the setting -/

/-- The dimensions of the instance: `N = 2^e`, `q = 2^K − 1`, `W = 2^b`, `m̄ = mb`. -/
structure Dims where
  /-- `N = 2^e`. -/
  e : ℕ
  /-- `q = 2^K − 1`, `τ = K`. -/
  K : ℕ
  /-- `W = 2^b`. -/
  b : ℕ
  /-- `m̄`: the columns of `Ā`. -/
  mb : ℕ
  hK : 2 ≤ K
  hb : b ≤ K
  /-- `2W ∣ N` (the canonical `H`). -/
  h2 : 2 * 2 ^ b ∣ 2 ^ e
  hlt : 2 ^ b < 2 ^ e

variable (D : Dims)

/-- `N`. -/
abbrev Dims.N : ℕ := 2 ^ D.e

/-- The modulus `2^K − 1`. -/
abbrev Dims.q : ℕ := 2 ^ D.K - 1

theorem Dims.one_lt_q : 1 < D.q := by
  have : 4 ≤ 2 ^ D.K := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ D.K := Nat.pow_le_pow_right (by norm_num) D.hK
  simp only [Dims.q]; omega

instance : NeZero D.q := ⟨by have := D.one_lt_q; omega⟩

/-- The ring `ℤ_{2^K − 1}[X]/(X^N + 1)`. -/
abbrev Rg := Negacyclic (ZMod D.q) D.N

theorem Dims.K_pos : 0 < D.K := by have := D.hK; omega

theorem Dims.N_pos : 0 < D.N := by positivity

theorem Dims.W_dvd : 2 ^ D.b ∣ D.N := (Dvd.intro_left 2 rfl).trans D.h2

theorem Dims.q_le : D.q ≤ 2 ^ D.K := Nat.sub_le _ _

/-- The ring with automorphisms. -/
noncomputable def expRing : ExpRing (Rg D) :=
  expRingMersenne D.K D.N D.b D.hb D.N_pos D.W_dvd D.hlt

/-- **The setting**: canonical `H`, binary digits, `τ = K`. -/
noncomputable def setting : Setting (Rg D) :=
  canonSetting (expRing D) rfl D.h2 (binaryDigits D.N D.q D.K D.q_le) (binaryDigits_g D.q_le)

@[simp] theorem setting_τ : (setting D).τ = D.K := rfl
@[simp] theorem setting_b : (setting D).b = D.b := rfl
@[simp] theorem setting_W : (setting D).E.W = 2 ^ D.b := rfl
@[simp] theorem setting_n : (setting D).E.n = D.N := rfl

/-- The columns of `Ā`. -/
abbrev Wb := Fin D.mb

/-- The helpers: `(t, 0)` is `g_t`, `(t, 1)` is `g_t⁻¹`. -/
abbrev Jh := Fin D.b × Fin 2

/-- The attribute positions: the 16 symbols of 8 bits. -/
abbrev Pos := Fin w8.len

theorem w8_len : w8.len = 16 := rfl

/-- The exponents of the helpers. -/
def je (k : Jh D) : ℕ := if k.2 = 0 then 2 ^ (k.1 : ℕ) else 2 ^ D.b - 2 ^ (k.1 : ℕ)

/-- **The helper map**. -/
def helperMap : HelperMap (setting D) (Jh D) where
  je := je D
  fwd t := (t, 0)
  inv t := (t, 1)
  je_fwd t := by simp [je]
  je_inv t := by simp [je]

/-- The width of the states, `w = 2^14`. -/
abbrev wSt : ℕ := 2 ^ stateBits

/-- `⌊q/2⌉ = 2^{K − 1}`. -/
noncomputable def half : Rg D := algebraMap (ZMod D.q) (Rg D) (2 ^ (D.K - 1))

/-- The message bit as a ring element. -/
noncomputable def msgR (μ : Bool) : Rg D := if μ then 1 else 0

/-- The scheme's objects at the dimensions `D`. -/
abbrev MPKt := MPK (setting D) (Wb D) (Jh D) (Pos)
abbrev MSKt := MSK (setting D) (Wb D) (Jh D) (Pos)
abbrev CTt := Ciphertext (setting D) (Wb D) (Jh D) (Pos)
abbrev KColt := KCol (Wb D) (Jh D) D.K (2 ^ D.b)
abbrev Keyt := KColt D → Rg D
abbrev SKt := MPKt D × Keyt D

/-! ### Encodings -/

/-- **Ring elements**: `N` canonical blocks of `K` bits. -/
def rEnc : FixedEnc (Rg D) (D.N * D.K) where
  enc := encRM D.N D.K
  inj a a' h := by
    rw [← decRM_encRM D.K_pos a, ← decRM_encRM D.K_pos a', h]
  length := length_encRM D.N D.K

theorem rEnc_enc (a : Rg D) : (rEnc D).enc a = encRM D.N D.K a := rfl

/-- Functions into the ring. -/
abbrev vecE (r : Type) [Enum r] := FixedEnc.fun (α := r) (rEnc D)

/-- Matrices over the ring, row-major. -/
abbrev matE (r s : Type) [Enum r] [Enum s] :=
  FixedEnc.fun (α := r) (FixedEnc.fun (α := s) (rEnc D))

/-- **Public keys**: `B`, `H`, `a`, `A₀`, `A^in`, `A^aut`, `d`. -/
def mpkEnc :=
  ((matE D (Fin 2) (BCol (Wb D) D.K)).prod
    ((FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).prod
    ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).prod
    ((matE D (Fin 2) (Col D.K)).prod
    ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).prod
    ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).prod
      (vecE D (Fin 2)))))))).comap
    (fun m : MPKt D => (m.B, m.H, m.a, m.A0, m.Ain, m.Aaut, m.d)) (fun x y h => by
      cases x; cases y
      injection h with h1 h; injection h with h2 h; injection h with h3 h
      injection h with h4 h; injection h with h5 h; injection h with h6 h7
      subst h1 h2 h3 h4 h5 h6 h7; rfl)

/-- **Master secret keys**: the public key, then the trapdoor `T`. -/
def mskEnc :=
  ((mpkEnc D).prod (matE D (Wb D) (Fin D.K))).comap (fun m : MSKt D => (m.mpk, m.T))
    (fun x y h => by
      cases x; cases y
      injection h with h1 h2
      subst h1 h2; rfl)

/-- **Ciphertexts**: `b`, `h`, `c^aut`, the bottom rows of `C^in`, `c^in`, `c₀`, `c_m`. -/
def ctEnc :=
  ((vecE D (BCol (Wb D) D.K)).prod
    ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).prod
    ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).prod
    ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).prod
    ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).prod
    ((vecE D (Col D.K)).prod (rEnc D))))))).comap
    (fun c : CTt D => (c.b, c.h, c.caut, c.cinBot, c.cin, c.c0, c.cm)) (fun x y h => by
      cases x; cases y
      injection h with h1 h; injection h with h2 h; injection h with h3 h
      injection h with h4 h; injection h with h5 h; injection h with h6 h7
      subst h1 h2 h3 h4 h5 h6 h7; rfl)

/-- **Keys**: the key vector over `KCol`. -/
abbrev keyEnc := vecE D (KColt D)

/-- **Secret keys of predicates**: the public key (needed by `Dec`), then the key `k_F`. -/
def skEnc := (mpkEnc D).prod (keyEnc D)

/-! ### Predicate words -/

/-- The bits of the lookup width: `u = z + 2^14 a < 2^22`. -/
abbrev lutBits : ℕ := stateBits + 8

/-- A 14-bit state as 14 bits, least significant first. -/
def stEnc : FixedEnc ProgState stateBits where
  enc z := toBits stateBits z.val
  inj z z' h := by
    have := congrArg val h
    rw [val_toBits, val_toBits, Nat.mod_eq_of_lt z.isLt, Nat.mod_eq_of_lt z'.isLt] at this
    exact Fin.ext this
  length z := by simp [toBits]

/-- One bit. -/
def bitEnc : FixedEnc Bool 1 where
  enc a := [a]
  inj _ _ h := List.singleton_inj.mp h
  length _ := rfl

/-- The state of the index `u`: its low 14 bits. -/
def zOf (u : Fin (2 ^ lutBits)) : ProgState := ⟨u.val % 2 ^ stateBits, Nat.mod_lt _ (by norm_num)⟩

/-- The symbol of the index `u`: its high 8 bits. -/
def aOf (u : Fin (2 ^ lutBits)) : Symbol w8 :=
  ⟨u.val / 2 ^ stateBits, by have := u.isLt; simp only [w8, lutBits, stateBits] at *; omega⟩

/-- The index `u = z + 2^14 a`. -/
def uOf (z : ProgState) (a : Symbol w8) : Fin (2 ^ lutBits) :=
  ⟨z.val + 2 ^ stateBits * a.val, by
    have := z.isLt; have := a.isLt; simp only [w8, lutBits, stateBits] at *; omega⟩

theorem zOf_uOf (z : ProgState) (a : Symbol w8) : zOf (uOf z a) = z := by
  apply Fin.ext; have := z.isLt; simp only [zOf, uOf, stateBits] at *; omega

theorem aOf_uOf (z : ProgState) (a : Symbol w8) : aOf (uOf z a) = a := by
  apply Fin.ext; have := z.isLt; simp only [aOf, uOf, stateBits] at *; omega

/-- The steps of a program, `15 = w8.len − 1`. -/
abbrev Stp := Fin (w8.len - 1)

/-- The encoding of the 15 transition tables. -/
abbrev tabEnc := FixedEnc.fun (α := Stp) (FixedEnc.fun (α := Fin (2 ^ lutBits)) stEnc)

/-- The encoding of the output table. -/
abbrev outEnc := FixedEnc.fun (α := Fin (2 ^ lutBits)) bitEnc

/-- The length of a predicate word: `15 · 14 · 2^22 + 2^22 = 211 · 2^22`. -/
def predLen : ℕ := 211 * 2 ^ 22

/-- The transition tables of a program, indexed by `u`. -/
def tabsOf (F : Program w8) : Stp → Fin (2 ^ lutBits) → ProgState := fun i u => F.step i (zOf u) (aOf u)

/-- The output table of a program, indexed by `u`. -/
def outsOf (F : Program w8) : Fin (2 ^ lutBits) → Bool := fun u => F.out (zOf u) (aOf u)

/-- **The word of a program.** -/
def predWord (F : Program w8) : List Bool := tabEnc.enc (tabsOf F) ++ outEnc.enc (outsOf F)

theorem len_fin (n : ℕ) : (Enum.list (α := Fin n)).length = n := List.length_finRange

theorem length_fun2 {β : Type} {k : ℕ} (e : FixedEnc β k) (n m : ℕ) (t : Fin n → Fin m → β) :
    ((FixedEnc.fun (α := Fin n) (FixedEnc.fun (α := Fin m) e)).enc t).length = n * (m * k) := by
  rw [FixedEnc.length, len_fin, len_fin]

theorem length_fun1 {β : Type} {k : ℕ} (e : FixedEnc β k) (n : ℕ) (t : Fin n → β) :
    ((FixedEnc.fun (α := Fin n) e).enc t).length = n * k := by
  rw [FixedEnc.length, len_fin]

theorem stp_len : w8.len - 1 = 15 := rfl

theorem length_tabEnc (t : Stp → Fin (2 ^ lutBits) → ProgState) :
    (tabEnc.enc t).length = 210 * 2 ^ 22 :=
  (length_fun2 stEnc (w8.len - 1) (2 ^ lutBits) t).trans (by norm_num [w8, Width.len, lutBits, stateBits])

theorem length_outEnc (o : Fin (2 ^ lutBits) → Bool) : (outEnc.enc o).length = 2 ^ 22 :=
  (length_fun1 bitEnc (2 ^ lutBits) o).trans (by norm_num [lutBits, stateBits])

theorem length_predWord (F : Program w8) : (predWord F).length = predLen := by
  rw [predWord, List.length_append, length_tabEnc, length_outEnc, predLen]; norm_num


/-- The 14-bit state at bit `p`, least significant first. -/
def readSt (C : List Bool) (p : ℕ) : ProgState :=
  ⟨val ((C.drop p).take stateBits) % 2 ^ stateBits, Nat.mod_lt _ (by norm_num)⟩

/-- **The program of a word.** -/
def progOf (C : List Bool) : Program w8 where
  step i z a := readSt C (stateBits * (2 ^ lutBits * i.val + (uOf z a).val))
  out z a := C.getD (210 * 2 ^ 22 + (uOf z a).val) false

theorem readSt_enc (C : List Bool) (p : ℕ) (z : ProgState)
    (h : (C.drop p).take stateBits = stEnc.enc z) : readSt C p = z := by
  apply Fin.ext
  simp only [readSt, h, stEnc, val_toBits, Nat.mod_eq_of_lt z.isLt]

/-- A window inside the first `M` bits. -/
theorem take_drop_sub {L : List Bool} {c n : ℕ} (M : ℕ) (h : c + n ≤ M) :
    (L.drop c).take n = ((L.take M).drop c).take n := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- The block of entry `(i, u)` of a family of tables. -/
theorem fun2_block {β : Type} {k : ℕ} (e : FixedEnc β k) (n m : ℕ) (t : Fin n → Fin m → β)
    (i : Fin n) (u : Fin m) :
    (((FixedEnc.fun (α := Fin n) (FixedEnc.fun (α := Fin m) e)).enc t).drop
      (k * (m * i.val + u.val))).take k = e.enc (t i u) := by
  have hi := i.isLt
  have hu := u.isLt
  have h1 := FixedEnc.fun_block (α := Fin n) (FixedEnc.fun (α := Fin m) e) t i.val
    (by rw [len_fin]; exact hi)
  have h2 := FixedEnc.fun_block (α := Fin m) e (t i) u.val (by rw [len_fin]; exact hu)
  rw [Enum.getElem_fin] at h1 h2
  have hL := len_fin m
  have e' : k * (m * i.val + u.val) =
      i.val * ((Enum.list (α := Fin m)).length * k) + u.val * k := by rw [hL]; ring
  have hk : u.val * k + k ≤ (Enum.list (α := Fin m)).length * k := by
    have : u.val + 1 ≤ m := hu
    rw [hL]; nlinarith
  rw [e', ← List.drop_drop, take_drop_sub _ hk, h1, h2]

/-- Bit `u` of a table of bits. -/
theorem fun1_bit (n : ℕ) (o : Fin n → Bool) (u : Fin n) :
    ((FixedEnc.fun (α := Fin n) bitEnc).enc o).getD u.val false = o u := by
  have h := FixedEnc.fun_block (α := Fin n) bitEnc o u.val (by rw [len_fin]; exact u.isLt)
  rw [Enum.getElem_fin, mul_one] at h
  have h' := congrArg (fun l => l[0]?) h
  simp only [List.getElem?_take, List.getElem?_drop] at h'
  rw [List.getD_eq_getElem?_getD]
  simp only [Nat.add_zero, show (0 : ℕ) < 1 from Nat.one_pos, ite_true] at h'
  rw [h']; rfl

/-- **A word reads back its program.** -/
theorem progOf_predWord (F : Program w8) : progOf (predWord F) = F := by
  have htl := length_tabEnc (tabsOf F)
  obtain ⟨step, out⟩ := F
  simp only [progOf, Program.mk.injEq]
  constructor
  · funext i z a
    apply readSt_enc
    have hu := (uOf z a).isLt
    have hi := i.isLt
    have hp : stateBits * (2 ^ lutBits * i.val + (uOf z a).val) + stateBits ≤
        (tabEnc.enc (tabsOf ⟨step, out⟩)).length := by
      rw [htl]; simp only [stp_len, lutBits, stateBits] at hi hu ⊢; omega
    rw [predWord, List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega),
      fun2_block stEnc (w8.len - 1) (2 ^ lutBits) (tabsOf ⟨step, out⟩) i (uOf z a)]
    simp only [tabsOf, zOf_uOf, aOf_uOf]
  · funext z a
    rw [predWord, List.getD_append_right _ _ _ _ (by rw [htl]; omega), htl,
      Nat.add_sub_cancel_left, fun1_bit]
    simp only [outsOf, zOf_uOf, aOf_uOf]


/-! ### Programs as branching programs of the scheme -/

/-- A number as a state (low 14 bits). -/
def toSt (z : ℕ) : ProgState := ⟨z % 2 ^ stateBits, Nat.mod_lt _ (by norm_num)⟩

/-- A number as a symbol (low 8 bits). -/
def toSym (a : ℕ) : Symbol w8 := ⟨a % 2 ^ 8, Nat.mod_lt _ (by norm_num)⟩

theorem toSt_val (z : ProgState) : toSt z.val = z := Fin.ext (Nat.mod_eq_of_lt z.isLt)

theorem toSym_val (a : Symbol w8) : toSym a.val = a := Fin.ext (Nat.mod_eq_of_lt a.isLt)

/-- The tables of the scheme's branching program: the transition tables for , then the
output table as  (: authorized). -/
def bpStep (F : Program w8) (i z a : ℕ) : ℕ :=
  if hi : i < 15 then (F.step ⟨i, hi⟩ (toSt z) (toSym a)).val
  else if F.out (toSt z) (toSym a) then 1 else 0

/-- **The program as a branching program of the scheme**: `T = 16`, `w = 2^14`, `|Σ| = 2^8`,
step `i` reads symbol `i`. -/
def bpOf (F : Program w8) : BP Pos where
  T := 16
  w := wSt
  nsym := 2 ^ 8
  read i := ⟨i % 16, Nat.mod_lt _ (by decide)⟩
  step := bpStep F

/-- The symbols of an attribute as numbers. -/
def attrN (x : Attribute w8) : Pos → ℕ := fun t => (x t).val

theorem attrN_lt (F : Program w8) (x : Attribute w8) (t : Pos) : attrN x t < (bpOf F).nsym :=
  (x t).isLt

theorem wf_bpOf (F : Program w8) {W : ℕ} (hW : 2 ^ 22 ≤ W) : (bpOf F).WF W where
  T_pos := by show 0 < 16; norm_num
  w_pos := by show 0 < 2 ^ stateBits; positivity
  le_W := by show 2 ^ stateBits * 2 ^ 8 ≤ W; rw [← pow_add]; exact hW
  step_lt i z a hi hz ha := by
    simp only [bpOf] at hi hz ha ⊢
    unfold bpStep
    rw [dif_pos (by omega)]
    exact Fin.isLt _

/-- Iterating a function of the index. -/
def natFold {α : Type} (g : ℕ → α → α) (a : α) : ℕ → α
  | 0 => a
  | m + 1 => g m (natFold g a m)

theorem foldl_natFold {α : Type} (g : ℕ → α → α) (a : α) :
    ∀ m : ℕ, Fin.foldl m (fun z (i : Fin m) => g i.val z) a = natFold g a m
  | 0 => by simp [natFold]
  | m + 1 => by
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [foldl_natFold g a m]; rfl

/-- The step function of a program on numbered steps. -/
def stepN (F : Program w8) (x : Attribute w8) (j : ℕ) (z : ProgState) : ProgState :=
  if h : j < 15 then F.step ⟨j, h⟩ z (x ⟨j, by simp [w8, Width.len]; omega⟩) else z

theorem run_eq_natFold (F : Program w8) (x : Attribute w8) :
    F.run x = natFold (stepN F x) 0 15 := by
  rw [← foldl_natFold]
  unfold Program.run
  congr 1
  funext z i
  have hi : i.val < 15 := i.isLt
  simp only [stepN, dif_pos hi]

theorem state_bpOf (F : Program w8) (x : Attribute w8) :
    ∀ i ≤ 15, (bpOf F).state (attrN x) i = (natFold (stepN F x) 0 i).val
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := state_bpOf F x i (by omega)
    change (bpOf F).step i ((bpOf F).state (attrN x) i) (attrN x ((bpOf F).read i)) = _
    rw [ih]
    simp only [natFold]
    have e : x ⟨i % 16, Nat.mod_lt _ (by decide)⟩ = x ⟨i, by simp [w8, Width.len]; omega⟩ :=
      congrArg x (Fin.ext (Nat.mod_eq_of_lt (by omega)))
    simp only [bpOf, bpStep, attrN, dif_pos (show i < 15 by omega), stepN, toSt_val, e, toSym_val]

/-- **The scheme's branching program computes the program's output**: `F(x) = 0` iff the output
bit is `false`. -/
theorem eval_bpOf (F : Program w8) (x : Attribute w8) :
    (bpOf F).eval (attrN x) = if F.output x then 1 else 0 := by
  have h15 := state_bpOf F x 15 le_rfl
  change (bpOf F).step 15 ((bpOf F).state (attrN x) 15) (attrN x ((bpOf F).read 15)) = _
  rw [h15]
  simp only [bpOf, bpStep, attrN, lt_irrefl, dite_false, toSt_val, toSym_val]
  rw [Program.output, run_eq_natFold]
  rfl

/-! ### The laws the machines realize -/

/-- The "uniform" law of a ring element realizable from fair coins: `N K` fair bits read by
`decRM` (per coefficient, `0` has probability `2^{1−K}`, the other residues `2^{−K}`). -/
noncomputable def unifW : PMF (Rg D) := (BitString.uniformList (D.N * D.K)).map (decRM D.N D.K)

/-- **The coins of `Setup` from fair coins**: `setupCoinsLaw` with every uniform entry replaced by
independent `υ` entries (`υ = unifW D` for the machines), `T` from `χT`. Same order of sampling. -/
noncomputable def setupCoinsLawW (υ χT : PMF (Rg D)) :
    PMF (SetupCoins (setting D) (Wb D) (Jh D) Pos) :=
  (iidLaw υ (Wb D)).bind fun Abar =>
  (iidFam χT (Wb D) (Fin D.K)).bind fun T =>
  (iidLaw υ (BCol (Wb D) D.K)).bind fun B2 =>
  (Cslib.Probability.PMF.pi fun _ : Jh D => iidFam υ (Fin 2) (Col D.K)).bind fun H =>
  (iidFam υ Pos (Col D.K)).bind fun a =>
  (iidFam υ (Fin 2) (Col D.K)).bind fun A0 =>
  (Cslib.Probability.PMF.pi fun _ : Pos => Cslib.Probability.PMF.pi fun _ : Dig D.K =>
    iidFam υ (Fin 2) (Col D.K)).bind fun Ain =>
  (Cslib.Probability.PMF.pi fun _ : Fin D.b => Cslib.Probability.PMF.pi fun _ : Dig D.K =>
    iidFam υ (Fin 2) (Col D.K)).bind fun Aaut =>
  (iidLaw υ (Fin 2)).map fun d => ⟨Abar, T, B2, H, a, A0, Ain, Aaut, d⟩

/-- **The law of `Setup`** realized by the machines. -/
noncomputable def setupLawW (χT : PMF (Rg D)) : PMF (MPKt D × MSKt D) :=
  (setupCoinsLawW D (unifW D) χT).map setup

/-- **The law of `Enc`** realized by the machines (the scheme's `encLaw`; all its laws are
dyadic when `χs`, `χ`, `χfl` are). -/
noncomputable def encLawW (χs χ χfl : PMF (Rg D)) (mpk : MPKt D) (x : Attribute w8) (μ : Bool) :
    PMF (CTt D) :=
  encLaw (setting D) (Wb D) (Jh D) Pos χs χ χfl (helperMap D) wSt (half D) mpk (attrN x) (msgR D μ)

/-- The predicates of the class: the words of `predLen` bits. -/
abbrev ValidC (C : List Bool) : Prop := C.length = predLen

/-- The key boxes of one try of box rejection: the big box as the image of `mB` fair bits, and
the small box. -/
structure KeyBoxes where
  /-- The number of coins of the big box. -/
  mB : ℕ
  /-- The big box. -/
  emb : (Fin mB → Bool) ↪ (PIdx (Wb D) (Jh D) D.K (2 ^ D.b) → Rg D)
  /-- The small box. -/
  Small : Finset (PIdx (Wb D) (Jh D) D.K (2 ^ D.b) → Rg D)

variable {D} in
/-- The big box. -/
def KeyBoxes.Big (kb : KeyBoxes D) : Finset (PIdx (Wb D) (Jh D) D.K (2 ^ D.b) → Rg D) :=
  Finset.univ.map kb.emb

variable {D} in
theorem KeyBoxes.hBig (kb : KeyBoxes D) : kb.Big.Nonempty := Finset.univ_nonempty.map

/-- **The law of `KeyGen`** realized by the machines: for a predicate word of `predLen` bits, the
public key and a key of one try of box rejection with the real trapdoor of `msk` for the branching
program of the word (`keyGenLaw`, binary gadget decomposition `gadDec`); the zero key otherwise. -/
noncomputable def keyLawW (kb : KeyBoxes D) (msk : MSKt D) (C : List Bool) : PMF (SKt D) :=
  haveI := Classical.dec (ValidC C)
  if ValidC C then
    (keyGenLaw (S := setting D) kb.Big kb.Small kb.hBig gadDec (helperMap D) msk
      (bpOf (progOf C))).map fun k => (msk.mpk, k)
  else PMF.pure (msk.mpk, 0)

/-- The decoding of a message bit: coefficient `0` of `μ'` within `[2^{K−2}, 3 · 2^{K−2})`. -/
def decodeBit (a : Rg D) : Bool :=
  decide (2 ^ (D.K - 2) ≤ (a.coeffs ⟨0, D.N_pos⟩).val ∧
    (a.coeffs ⟨0, D.N_pos⟩).val < 3 * 2 ^ (D.K - 2))

/-- **The output of `Dec`** the machines compute: the decoded bit for predicate words of `predLen`
bits, `[false]` otherwise. -/
noncomputable def decOutW (sk : SKt D) (C : List Bool) (ct : CTt D) : List Bool :=
  haveI := Classical.dec (ValidC C)
  if ValidC C then
    [decodeBit D (decryptRaw (helperMap D) sk.1 (bpOf (progOf C)) sk.2 ct)]
  else [false]

/-- The parameters' word given to every algorithm. -/
def pwW : List Bool := paramsWord (univ w8) params

/-- **The specification of a `Setup` machine.** -/
def SetupSpec (χT : PMF (Rg D)) (M : Machine) : Prop :=
  M.run (encodeTuple [pwW]) =
    (setupLawW D χT).map fun v => encodeTuple [(mpkEnc D).enc v.1, (mskEnc D).enc v.2]

/-- **The specification of an `Enc` machine.** -/
def EncSpec (χs χ χfl : PMF (Rg D)) (M : Machine) : Prop :=
  ∀ (mpk : MPKt D) (x : Attribute w8) (μ : Bool),
    M.run (encodeTuple [pwW, (mpkEnc D).enc mpk, encAttribute w8 x, [μ]]) =
      (encLawW D χs χ χfl mpk x μ).map fun ct => encodeTuple [(ctEnc D).enc ct]

/-- **The specification of a `KeyGen` machine** (predicates of at most `L` bits, `L ≥ predLen`). -/
def KeySpec (kb : KeyBoxes D) (L : ℕ) (M : Machine) : Prop :=
  ∀ (msk : MSKt D) (C : List Bool), C.length ≤ L →
    M.run (encodeTuple [pwW, (mskEnc D).enc msk, C]) =
      (keyLawW D kb msk C).map fun sk => encodeTuple [(skEnc D).enc sk]

/-- **The specification of a `Dec` machine** (deterministic). -/
def DecSpec (L : ℕ) (M : Machine) : Prop :=
  M.Deterministic ∧ ∀ (sk : SKt D) (C : List Bool) (ct : CTt D), C.length ≤ L →
    M.run (encodeTuple [pwW, (skEnc D).enc sk, C, (ctEnc D).enc ct]) =
      PMF.pure (encodeTuple [decOutW D sk C ct])

end AdvancedEncryption.ExpLUT.Prog
