import Solution.Pre2Lwe
import Solution.Decode

/-!
# The Pre2 reduction: arithmetic

On an LWE word (`q`, `Aᵀ`, `b`) and a number `x < M = 2 · R^{nk} · N^k` (with `R = κ_R + 1` and
`N = (q − 1)/2 + 1`), the reduction reads off a bit `h`, a matrix `R ∈ [0, κ_R]^{n×k}` and a row
`T ∈ [0, N)^k` as the mixed-radix digits of `x`, and writes the Pre2 word
`(2Aᵀ + h·R, 2bᵀ − 2T)` (`build`). Everything is read from the word, including `q`.

* `dec`: the digits as an equivalence `Fin M ≃ Bool × R-matrices × T-rows`.
* `build_encLWE`: on an encoded LWE pair, `build` writes `hybLWE` at the digits of `x`.
-/

namespace TestCase.EvLWE

open SigabaNeo.Lattices

open TestCase TestCase.EvLWE Cslib Cslib.Crypto Cslib.Probability
open scoped ENNReal Matrix

section
variable (κ : ℕ)

/-! ### What the reduction computes -/

def aAt (word : List Bool) (i j : ℕ) : ℕ := entryAt κ word (1 + i * k κ + j)
def bAt (word : List Bool) (j : ℕ) : ℕ := entryAt κ word (1 + n κ * k κ + j)
def NTw (word : List Bool) : ℕ := (qOf κ word - 1) / 2 + 1
def RRc : ℕ := κR κ + 1
def bigT (word : List Bool) : ℕ := NTw κ word ^ k κ
def bigR : ℕ := RRc κ ^ (n κ * k κ)
def bigRT (word : List Bool) : ℕ := bigR κ * bigT κ word
def Mval (word : List Bool) : ℕ := 2 * bigRT κ word
def hbit (word : List Bool) (x : ℕ) : Bool := decide (bigRT κ word ≤ x)
def rDig (word : List Bool) (x i j : ℕ) : ℕ :=
  x % bigRT κ word / bigT κ word / RRc κ ^ (i * k κ + j) % RRc κ
def tDig (word : List Bool) (x j : ℕ) : ℕ :=
  x % bigRT κ word % bigT κ word / NTw κ word ^ j % NTw κ word
def pEntry (word : List Bool) (x i j : ℕ) : ℕ :=
  (2 * aAt κ word i j + (if hbit κ word x then rDig κ word x i j else 0)) % qOf κ word
def auxEntry (word : List Bool) (x j : ℕ) : ℕ :=
  (2 * bAt κ word j + 2 * (qOf κ word - tDig κ word x j)) % qOf κ word

/-- The Pre2 word the reduction writes. -/
def build (word : List Bool) (x : ℕ) : List Bool :=
  encEntries (W κ) (qOf κ word ::
    (((List.range (n κ)).flatMap fun i => (List.range (k κ)).map (pEntry κ word x i)) ++
      (List.range (ell κ)).flatMap fun _ => (List.range (k κ)).map (auxEntry κ word x)))

/-! ### Digits -/

/-- `M` at the true modulus. -/
noncomputable def Mq : ℕ := 2 * (bigR κ * NT κ ^ k κ)

noncomputable def rEquiv : Fin (bigR κ) ≃ RMat κ :=
  finFunctionFinEquiv.symm.trans
    ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl _)).trans (Equiv.curry _ _ _))

noncomputable def tEquiv : Fin (NT κ ^ k κ) ≃ TMat κ :=
  finFunctionFinEquiv.symm.trans (Equiv.funUnique (Fin (ell κ)) _).symm

/-- The digits of `x`. -/
noncomputable def dec : Fin (Mq κ) ≃ Bool × RMat κ × TMat κ :=
  finProdFinEquiv.symm.trans (finTwoEquiv.prodCongr
    (finProdFinEquiv.symm.trans ((rEquiv κ).prodCongr (tEquiv κ))))

theorem dec_fst_val (x : Fin (Mq κ)) :
    (dec κ x).1 = (x.val / (bigR κ * NT κ ^ k κ) == 1) := by
  show ((⟨x.val / (bigR κ * NT κ ^ k κ), _⟩ : Fin 2) == 1) = _
  rfl

theorem dec_fst (x : Fin (Mq κ)) :
    (dec κ x).1 = decide (bigR κ * NT κ ^ k κ ≤ x.val) := by
  have hx := x.isLt
  unfold Mq at hx
  rw [dec_fst_val]
  have hpos : 0 < bigR κ * NT κ ^ k κ := by
    unfold bigR RRc; positivity
  rcases Nat.lt_or_ge x.val (bigR κ * NT κ ^ k κ) with h | h
  · have : x.val / (bigR κ * NT κ ^ k κ) = 0 := Nat.div_eq_of_lt h
    simp [this, Nat.not_le.mpr h]
  · have : x.val / (bigR κ * NT κ ^ k κ) = 1 := by
      apply le_antisymm
      · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpos).mpr (by omega))
      · exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    simp [this, h]

theorem dec_R (x : Fin (Mq κ)) (i : Fin (n κ)) (j : Fin (k κ)) :
    ((dec κ x).2.1 i j : ℕ) =
      x.val % (bigR κ * NT κ ^ k κ) / NT κ ^ k κ / RRc κ ^ (i.val * k κ + j.val) % RRc κ := by
  rw [show i.val * k κ + j.val = j.val + k κ * i.val by ring]
  rfl

theorem dec_T (x : Fin (Mq κ)) (i : Fin (ell κ)) (j : Fin (k κ)) :
    ((dec κ x).2.2 i j : ℕ) = x.val % (bigR κ * NT κ ^ k κ) % NT κ ^ k κ / NT κ ^ j.val % NT κ :=
  rfl

/-! ### Reading an encoded LWE pair -/

theorem entryAt_encSample (L : List ℕ) (hL : ∀ x ∈ L, x < 2 ^ W κ) (idx : ℕ)
    (h : idx < L.length + 1) : entryAt κ (encSample κ L) idx = (q κ :: L).getD idx 0 := by
  have hlen : idx < (q κ :: L).length := by simpa using h
  unfold entryAt encSample
  rw [binaryEntry_encEntries _ _ hlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
    Option.getD_some]
  apply Nat.mod_eq_of_lt
  cases idx with
  | zero => simpa using q_lt_W κ
  | succ i => simp only [List.getElem_cons_succ]; exact hL _ (List.getElem_mem _)

theorem matVals_lt {r c : ℕ} (M : Matrix (Fin r) (Fin c) (ZMod (q κ))) :
    ∀ x ∈ matVals M, x < 2 ^ W κ := by
  intro x hx
  simp only [matVals, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, _, _, _, rfl⟩ := hx
  exact val_lt_W κ _

def aMat (pair : LWEPair κ) : Matrix (Fin (n κ)) (Fin (k κ)) (ZMod (q κ)) :=
  Matrix.of fun i j => pair.1 j i 0

def bMat (pair : LWEPair κ) : Matrix (Fin 1) (Fin (k κ)) (ZMod (q κ)) :=
  Matrix.of fun _ j => pair.2 j 0

theorem encLWE_eq (pair : LWEPair κ) :
    encLWE κ pair = encSample κ (matVals (aMat κ pair) ++ matVals (bMat κ pair)) := rfl

theorem entryAt_encLWE (pair : LWEPair κ) (idx : ℕ) (h : idx < n κ * k κ + k κ + 1) :
    entryAt κ (encLWE κ pair) idx =
      (q κ :: (matVals (aMat κ pair) ++ matVals (bMat κ pair))).getD idx 0 := by
  rw [encLWE_eq]
  apply entryAt_encSample
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx <;> exact matVals_lt κ _ x hx
  · rw [List.length_append, length_matVals, length_matVals]; omega

theorem qOf_encLWE (pair : LWEPair κ) : qOf κ (encLWE κ pair) = q κ := by
  unfold qOf; rw [entryAt_encLWE _ _ 0 (by omega)]; rfl

theorem aAt_encLWE (pair : LWEPair κ) (i : Fin (n κ)) (j : Fin (k κ)) :
    aAt κ (encLWE κ pair) i j = (pair.1 j i 0).val := by
  unfold aAt
  have hi := i.isLt; have hj := j.isLt
  have hij : i.val * k κ + j.val < n κ * k κ := by nlinarith
  rw [entryAt_encLWE _ _ _ (by omega),
    show 1 + i.val * k κ + j.val = (i.val * k κ + j.val) + 1 by ring, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by rw [length_matVals]; exact hij), getD_matVals]
  rfl

theorem bAt_encLWE (pair : LWEPair κ) (j : Fin (k κ)) :
    bAt κ (encLWE κ pair) j = (pair.2 j 0).val := by
  unfold bAt
  have hj := j.isLt
  rw [entryAt_encLWE _ _ _ (by omega),
    show 1 + n κ * k κ + j.val = (n κ * k κ + j.val) + 1 by ring, List.getD_cons_succ,
    List.getD_append_right _ _ _ _ (by rw [length_matVals]; omega), length_matVals,
    show n κ * k κ + j.val - n κ * k κ = j.val by omega]
  have := getD_matVals (bMat κ pair) 0 j
  rwa [show ((0 : Fin 1) : ℕ) = 0 from rfl, zero_mul, zero_add] at this

theorem NTw_encLWE (pair : LWEPair κ) : NTw κ (encLWE κ pair) = NT κ := by
  unfold NTw; rw [qOf_encLWE]

theorem bigRT_encLWE (pair : LWEPair κ) :
    bigRT κ (encLWE κ pair) = bigR κ * NT κ ^ k κ := by
  unfold bigRT bigT; rw [NTw_encLWE]

theorem Mval_encLWE (pair : LWEPair κ) : Mval κ (encLWE κ pair) = Mq κ := by
  unfold Mval Mq; rw [bigRT_encLWE]

theorem hbit_encLWE (pair : LWEPair κ) (x : Fin (Mq κ)) :
    hbit κ (encLWE κ pair) x.val = (dec κ x).1 := by
  unfold hbit; rw [bigRT_encLWE, dec_fst]

theorem rDig_encLWE (pair : LWEPair κ) (x : Fin (Mq κ)) (i : Fin (n κ)) (j : Fin (k κ)) :
    rDig κ (encLWE κ pair) x.val i j = (dec κ x).2.1 i j := by
  unfold rDig; rw [bigRT_encLWE, dec_R]; unfold bigT; rw [NTw_encLWE]

theorem tDig_encLWE (pair : LWEPair κ) (x : Fin (Mq κ)) (i : Fin (ell κ)) (j : Fin (k κ)) :
    tDig κ (encLWE κ pair) x.val j = (dec κ x).2.2 i j := by
  unfold tDig; rw [bigRT_encLWE, dec_T]; unfold bigT; rw [NTw_encLWE]

/-! ### The written word -/

theorem NT_le_q : NT κ ≤ q κ := by
  have : 1 ≤ q κ := (Fact.out : (q κ).Prime).one_lt.le
  unfold NT; omega

theorem build_encLWE (pair : LWEPair κ) (x : Fin (Mq κ)) :
    build κ (encLWE κ pair) x.val = hybLWE κ pair (dec κ x).1 (dec κ x).2.1 (dec κ x).2.2 := by
  unfold build hybLWE pre2Word encSample
  rw [qOf_encLWE]
  congr 2
  rw [matVals_eq_range _ (pEntry κ (encLWE κ pair) x.val) ?_,
    matVals_eq_range _ (fun _ => auxEntry κ (encLWE κ pair) x.val) ?_]
  · intro i j
    unfold auxEntry
    have ht := ((dec κ x).2.2 i j).isLt
    have hq := NT_le_q κ
    rw [bAt_encLWE, qOf_encLWE, tDig_encLWE κ pair x i, ← ZMod.val_natCast]
    congr 1
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), ZMod.natCast_self,
      ZMod.natCast_zmod_val]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, bEquiv_apply, Tq,
      Matrix.map_apply]
    push_cast
    ring
  · intro i j
    unfold pEntry
    rw [aAt_encLWE, qOf_encLWE, hbit_encLWE, rDig_encLWE, ← ZMod.val_natCast]
    congr 1
    simp only [Matrix.add_apply, pofEquiv_apply]
    split_ifs <;> simp [Rq]

end

end TestCase.EvLWE
