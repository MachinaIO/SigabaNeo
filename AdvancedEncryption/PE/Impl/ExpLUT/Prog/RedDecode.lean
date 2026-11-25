import PE.Impl.RingBTVW.Prog.DecodeWord
import PE.Impl.ExpLUT.AH.CircBridge
import SigabaNeoStd.Machines.Prog.FrameParseX

/-!
# The decoder of the reduction machine (package G2)

The registry encodes a ring-level pair `v = (a, b)` over `ℤ_q[X]/(X^N + 1)` as cslib's
Module-LWE word (`encodeRing`): the framed expanded matrix of `a`, then the framed coefficients
of `b`. The generic frame parser `SigabaNeo.Tape.XProg.decodeMX false K T n` emits the first entry
of every row and every number, padded to `K` bits:

* `decodeW_encodeRingQ` (any `q ≤ 2^K`): on `encodeRing v` it outputs `true`, the coefficient words
  `coefW K (aᵢ)` (`K` bits per coefficient, least significant first), then those of the `bᵢ`;
* `coefW_eq_encRM`: for `q = 2^K − 1` these are the canonical ring words `encRM N K` of package E;
* `length_encodeRingQ_le`: the words are at most `encLen m N K` bits.

At the dimensions `D` (`circParamsD D`, `rowsD D` rows): the decoder `decR D n`, the state word
`dwR D w` of an instance word, **`run_decR`** (`decR D n` outputs `dwR D (enc D i)` on the word of
every instance), **`dwR_enc`** (`true`, the canonical words of the `aᵣ`, then of the `vᵣ`, in the
registry's row order `ρ D`), `instR` (the instance of a state word, by `decRM` of its blocks) and
**`instR_dwR`**.
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape Cslib
open Turing.MultiTapeTM (frame encList encNat encPair encBits)
open AdvancedEncryption.RingBTVW.Prog (lowBits length_bits_le padK_bits headD_ofFn flatMap_ofFn_mul
  length_frame length_flatMap_le encLen)

section Generic

variable {N K m q : ℕ} [NeZero q]

/-- The rows of the expanded matrix of a ring-level pair, entries in binary. -/
def ringRowsQ (v : (Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N)) :
    List (List (List Bool)) :=
  (List.ofFn fun p : Fin (m * N) => List.ofFn fun c : Fin (1 * N) =>
    (Cslib.Crypto.expandModuleMatrix (coeffPair v).1 p c).val).map (List.map Nat.bits)

/-- The coefficients of the values of a ring-level pair, in binary. -/
def ringNumsQ (v : (Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N)) :
    List (List Bool) :=
  (List.ofFn fun c : Fin (m * N) => (Cslib.Crypto.flattenPolyVec (coeffPair v).2 c).val).map Nat.bits

theorem encodeRing_eqQ (v : (Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N)) :
    encodeRing v = frame ((ringRowsQ v).flatMap FPS.rowW) ++ (ringNumsQ v).flatMap frame := by
  simp only [encodeRing, Cslib.Crypto.ModuleLWE.encodeSample, Turing.MultiTapeTM.encPair_apply,
    Cslib.Crypto.ModuleSIS.encodeMatrix, Cslib.Crypto.SIS.encodeMatrix, ringRowsQ, ringNumsQ,
    List.flatMap_map, FPS.rowW]
  rfl

/-- The coefficient words of a ring element: `K` bits per coefficient, least significant first. -/
def coefW (K : ℕ) (a : Negacyclic (ZMod q) N) : List Bool :=
  (List.finRange N).flatMap fun j => lowBits K (a.coeffs j).val

theorem encE_false_val (hq : q ≤ 2 ^ K) (x : ZMod q) : encE false K x.val.bits = lowBits K x.val := by
  simp only [encE, Bool.false_eq_true, ↓reduceIte]
  exact padK_bits ((ZMod.val_lt x).trans_le hq)

variable (v : (Fin m → Negacyclic (ZMod q) N) × (Fin m → Negacyclic (ZMod q) N))

/-- **The first entries of the rows** of the expanded matrix, emitted: the words of the `aᵢ`. -/
theorem rows_emitQ (hq : q ≤ 2 ^ K) :
    (ringRowsQ v).flatMap (fun r => encE false K (r.headD [])) =
      (List.finRange m).flatMap fun i => coefW K (v.1 i) := by
  rw [ringRowsQ, List.flatMap_map, flatMap_ofFn_mul]
  congr 1; funext i
  rw [coefW]
  congr 1; funext j
  have hN : 0 < 1 * N := by have := j.isLt; omega
  rw [List.map_ofFn, headD_ofFn _ _ hN, Function.comp_apply,
    show (⟨0, hN⟩ : Fin (1 * N)) = finProdFinEquiv ((0 : Fin 1), (⟨0, by omega⟩ : Fin N)) from
      Fin.ext (by simp [finProdFinEquiv_apply_val]),
    Cslib.Crypto.expandModuleMatrix_apply, encE_false_val hq]
  have h0 : (⟨0, by omega⟩ : Fin N) ≤ j := Fin.mk_le_mk.mpr (Nat.zero_le _)
  simp [coeffPair, rotMatrix, h0]

/-- **The values, emitted**: the words of the `bᵢ`. -/
theorem nums_emitQ (hq : q ≤ 2 ^ K) :
    (ringNumsQ v).flatMap (encE false K) = (List.finRange m).flatMap fun i => coefW K (v.2 i) := by
  rw [ringNumsQ, List.flatMap_map, flatMap_ofFn_mul]
  congr 1; funext i
  rw [coefW]
  congr 1; funext j
  simp [encE_false_val hq, Cslib.Crypto.flattenPolyVec, coeffPair]

theorem length_ringRowsQ : (ringRowsQ v).length = m * N := by simp [ringRowsQ]
theorem length_ringNumsQ : (ringNumsQ v).length = m * N := by simp [ringNumsQ]

theorem mem_ringRowsQ (hq : q ≤ 2 ^ K) {r : List (List Bool)} (hr : r ∈ ringRowsQ v) :
    r.length = N ∧ ∀ u ∈ r, u.length ≤ K := by
  simp only [ringRowsQ, List.mem_map, List.mem_ofFn] at hr
  obtain ⟨_, ⟨p, rfl⟩, rfl⟩ := hr
  refine ⟨by simp, fun u hu => ?_⟩
  simp only [List.mem_map, List.mem_ofFn] at hu
  obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := hu
  exact length_bits_le ((ZMod.val_lt _).trans_le hq)

theorem mem_ringNumsQ (hq : q ≤ 2 ^ K) {u : List Bool} (hu : u ∈ ringNumsQ v) : u.length ≤ K := by
  simp only [ringNumsQ, List.mem_map, List.mem_ofFn] at hu
  obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := hu
  exact length_bits_le ((ZMod.val_lt _).trans_le hq)

/-- **The parser on an encoded ring-level pair** (`2 m N K` output bits): `true`, the coefficient
words of the `aᵢ`, then those of the `bᵢ`. -/
theorem decodeW_encodeRingQ (hq : q ≤ 2 ^ K) :
    Prog.decodeW false K (2 * m * N * K) (encodeRing v) =
      true :: ((List.finRange m).flatMap (fun i => coefW K (v.1 i)) ++
        (List.finRange m).flatMap fun i => coefW K (v.2 i)) := by
  have hT : 2 * m * N * K = ((ringRowsQ v).length + (ringNumsQ v).length) * K := by
    rw [length_ringRowsQ, length_ringNumsQ]; ring
  rw [hT, encodeRing_eqQ, Prog.decodeW_word, rows_emitQ v hq, nums_emitQ v hq]
  · intro r hr h0
    obtain ⟨hl, _⟩ := mem_ringRowsQ v hq hr
    have : 0 < (ringRowsQ v).length := List.length_pos_of_mem hr
    rw [length_ringRowsQ] at this
    subst h0
    simp only [List.length_nil] at hl
    subst hl
    simp at this
  · intro r hr
    obtain ⟨_, h⟩ := mem_ringRowsQ v hq hr
    cases r with
    | nil => simp
    | cons u r => exact h u List.mem_cons_self
  · intro u hu; exact mem_ringNumsQ v hq hu

theorem length_encodeRingQ_le (hq : q ≤ 2 ^ K) : (encodeRing v).length ≤ encLen m N K := by
  rw [encodeRing_eqQ, List.length_append, length_frame, encLen]
  have h1 : ((ringRowsQ v).flatMap FPS.rowW).length ≤
      (ringRowsQ v).length * (2 * (N * (2 * K + 1)) + 1) := by
    refine length_flatMap_le _ _ _ fun r hr => ?_
    obtain ⟨hl, hu⟩ := mem_ringRowsQ v hq hr
    rw [FPS.rowW, length_frame]
    have := length_flatMap_le frame (2 * K + 1) r fun u hu' => by
      rw [length_frame]; have := hu u hu'; omega
    rw [hl] at this
    omega
  have h2 : ((ringNumsQ v).flatMap frame).length ≤ (ringNumsQ v).length * (2 * K + 1) :=
    length_flatMap_le _ _ _ fun u hu => by rw [length_frame]; have := mem_ringNumsQ v hq hu; omega
  rw [length_ringRowsQ] at h1
  rw [length_ringNumsQ] at h2
  omega

end Generic

/-! ### Words of ring elements -/

theorem lowBits_eq_toBits : ∀ (K n : ℕ), lowBits K n = toBits K n
  | 0, _ => rfl
  | K + 1, n => by
    rw [AdvancedEncryption.RingBTVW.Prog.lowBits_succ, toBits, lowBits_eq_toBits K (n / 2),
      Nat.testBit_zero]

theorem flatMap_finRange_concatN : ∀ {m : ℕ} (g : Fin m → List Bool),
    (List.finRange m).flatMap g = concatN m (fun r => if h : r < m then g ⟨r, h⟩ else [])
  | 0, _ => rfl
  | m + 1, g => by
    rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map,
      flatMap_finRange_concatN (fun i => g i.castSucc), concatN]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Fin.last, lt_add_one,
      ↓reduceDIte]
    congr 1
    refine concatN_congr fun i hi => ?_
    simp only [hi, ↓reduceDIte, show i < m + 1 by omega]
    rfl

/-- **The coefficient words modulo `2^K − 1` are the canonical words.** -/
theorem coefW_eq_encRM {N K : ℕ} [NeZero (2 ^ K - 1)] (a : Negacyclic (ZMod (2 ^ K - 1)) N) :
    coefW K a = encRM N K a := by
  rw [coefW, flatMap_finRange_concatN, encRM]
  refine concatN_congr fun i hi => ?_
  simp only [hi, ↓reduceDIte, encM, NegaG.coefG, lowBits_eq_toBits]

/-! ### The decoder at the dimensions `D` -/

variable (D : Dims)

/-- The rows of the reduction's circular instances. -/
noncomputable abbrev rowsD : ℕ := (circParamsD D).rows

theorem rowsD_eq : rowsD D = mCirc D + D.K * (D.b * 2) := by
  show mCirc D + D.K * (jList D).length = _
  rw [length_jList]

/-- The number of bits the decoder outputs after its marker. -/
noncomputable def decT : ℕ := 2 * rowsD D * D.N * D.K

/-- **The decoder** for instance words of at most `n` bits. -/
noncomputable def decR (n : ℕ) : Machine := Tape.XProg.decodeMX false D.K (decT D) n

/-- **The state word of an instance word.** -/
noncomputable def dwR (w : List Bool) : List Bool := Prog.decodeW false D.K (decT D) w

instance : NeZero D.q := ⟨by have := D.one_lt_q; omega⟩

theorem q_le_two_pow : D.q ≤ 2 ^ D.K := Nat.sub_le _ _

/-- **The decoder outputs the state word** of the word of every instance (instance words of at most
`n` bits). -/
theorem run_decR (n : ℕ) (hn : encLen (rowsD D) D.N D.K ≤ n) (i : CInst D) :
    (decR D n).run (enc D i) = PMF.pure (dwR D (enc D i)) :=
  Tape.XProg.run_decodeMX false D.K (decT D) n _
    ((length_encodeRingQ_le (toPair D i) (q_le_two_pow D)).trans hn)

theorem tapes_decR (n : ℕ) : (decR D n).tapes = 14 := rfl

/-- The canonical words of a family of ring elements, one after the other. -/
def wordsOf (n : ℕ) (f : Fin n → Rg D) : List Bool :=
  concatN n fun r => if h : r < n then encRM D.N D.K (f ⟨r, h⟩) else []

theorem length_wordsOf (n : ℕ) (f : Fin n → Rg D) : (wordsOf D n f).length = n * (D.N * D.K) :=
  length_concatN fun r hr => by simp only [hr, ↓reduceDIte, length_encRM]

/-- **The state word of an instance**: `true`, the canonical words of the public parts of the rows
(in the registry's order), then those of the values. -/
theorem dwR_enc (i : CInst D) :
    dwR D (enc D i) = true :: (wordsOf D (rowsD D) (toPair D i).1 ++ wordsOf D (rowsD D) (toPair D i).2) := by
  rw [dwR, enc, decT, decodeW_encodeRingQ (toPair D i) (q_le_two_pow D), wordsOf, wordsOf,
    flatMap_finRange_concatN, flatMap_finRange_concatN]
  congr 2 <;> refine concatN_congr fun r hr => ?_ <;> simp only [hr, ↓reduceDIte, coefW_eq_encRM]

/-- The `r`-th ring element of a word of canonical words. -/
def ringAt (w : List Bool) (r : ℕ) : Rg D := decRM D.N D.K (block (D.N * D.K) r w)

theorem ringAt_wordsOf (n : ℕ) (f : Fin n → Rg D) (r : Fin n) : ringAt D (wordsOf D n f) r = f r := by
  rw [ringAt, wordsOf, block_concatN (fun j hj => by simp only [hj, ↓reduceDIte, length_encRM])]
  simp only [r.isLt, ↓reduceIte, ↓reduceDIte, Fin.eta, decRM_encRM D.K_pos]

theorem length_dwR_enc (i : CInst D) :
    (dwR D (enc D i)).length = 1 + 2 * (rowsD D * (D.N * D.K)) := by
  rw [dwR_enc, List.length_cons, List.length_append, length_wordsOf, length_wordsOf]; ring

theorem head_dwR_enc (i : CInst D) : (dwR D (enc D i)).head? = some true := by
  rw [dwR_enc]; rfl

theorem ringAt_append_left (u v : List Bool) (r : ℕ) (hr : r * (D.N * D.K) + D.N * D.K ≤ u.length) :
    ringAt D (u ++ v) r = ringAt D u r := by
  unfold ringAt block
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- **The instance of a state word**: the ring elements of its blocks. -/
noncomputable def instR (w : List Bool) : CInst D :=
  ofPair D (fun r => ringAt D w.tail r, fun r => ringAt D (w.tail.drop (rowsD D * (D.N * D.K))) r)

/-- **The instance of the state word of an instance.** -/
theorem instR_dwR (i : CInst D) : instR D (dwR D (enc D i)) = i := by
  rw [dwR_enc, instR, List.tail_cons, List.drop_left' (length_wordsOf D _ _)]
  conv_rhs => rw [← ofPair_toPair D i]
  have h1 : ∀ r : Fin (rowsD D), ringAt D (wordsOf D (rowsD D) (toPair D i).1 ++
      wordsOf D (rowsD D) (toPair D i).2) r = (toPair D i).1 r := fun r => by
    rw [ringAt_append_left D _ _ _ (by
      rw [length_wordsOf, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ r.isLt), ringAt_wordsOf]
  simp only [h1, ringAt_wordsOf]

/-! ### The decoder at the concrete parameters -/

set_option exponentiation.threshold 1000

theorem encLen_le_gen {r N K : ℕ} (hr : r ≤ 2 ^ 51) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) :
    encLen r N K ≤ 2 ^ 120 := by
  unfold encLen
  calc 2 * (r * N * (2 * (N * (2 * K + 1)) + 1)) + 1 + r * N * (2 * K + 1)
      ≤ 2 * (2 ^ 51 * 2 ^ 24 * (2 * (2 ^ 24 * (2 * 2 ^ 16 + 1)) + 1)) + 1 +
          2 ^ 51 * 2 ^ 24 * (2 * 2 ^ 16 + 1) := by gcongr
    _ ≤ 2 ^ 120 := by norm_num

theorem decTime_le_gen {n K T : ℕ} (hn : n ≤ 2 ^ 120) (hK : K ≤ 2 ^ 16) (hT : T ≤ 2 ^ 92) :
    (2 * n + 2) + ((2 * K + 1) * (4 * (n + K + T + 1) + 12) +
        ((2 * (T + 1) + 1) * (4 * (n + K + T + 1) + 12) +
          (14 * (2 * (n + K + T + 1 + 14) + 5) +
            (2 * (n + K + T + 1) + 3) * (4 + 25 * n + 4 * n * K)))) +
        (2 * (n + K + T + 1) + 2) ≤ 2 ^ 270 := by
  calc _ ≤ (2 * 2 ^ 120 + 2) + ((2 * 2 ^ 16 + 1) * (4 * (2 ^ 120 + 2 ^ 16 + 2 ^ 92 + 1) + 12) +
        ((2 * (2 ^ 92 + 1) + 1) * (4 * (2 ^ 120 + 2 ^ 16 + 2 ^ 92 + 1) + 12) +
          (14 * (2 * (2 ^ 120 + 2 ^ 16 + 2 ^ 92 + 1 + 14) + 5) +
            (2 * (2 ^ 120 + 2 ^ 16 + 2 ^ 92 + 1) + 3) *
              (4 + 25 * 2 ^ 120 + 4 * 2 ^ 120 * 2 ^ 16)))) +
        (2 * (2 ^ 120 + 2 ^ 16 + 2 ^ 92 + 1) + 2) := by gcongr
    _ ≤ 2 ^ 270 := by norm_num

theorem rowsD_Dc_le : rowsD Dc ≤ 2 ^ 51 := by
  rw [rowsD_eq]
  have h1 := mCirc_Dc_le
  have h2 : Dc.K ≤ 2 ^ 16 := Params.Kc_le
  have h3 : Dc.b = 22 := Dc_b
  rw [h3]
  have : Dc.K * (22 * 2) ≤ 2 ^ 16 * 44 := Nat.mul_le_mul_right _ h2
  omega

/-- The input bound of the decoder at `Dc`. -/
noncomputable def nDc : ℕ := encLen (rowsD Dc) Dc.N Dc.K

theorem encLen_le_nDc : encLen (rowsD Dc) Dc.N Dc.K ≤ nDc := by
  unfold nDc; exact le_rfl

theorem Dc_N : Dc.N = 2 ^ 24 := rfl

theorem nDc_le : nDc ≤ 2 ^ 120 := by
  unfold nDc
  exact encLen_le_gen rowsD_Dc_le Dc_N.le Params.Kc_le

theorem decT_le_gen {r N K : ℕ} (hr : r ≤ 2 ^ 51) (hN : N ≤ 2 ^ 24) (hK : K ≤ 2 ^ 16) :
    2 * r * N * K ≤ 2 ^ 92 :=
  calc 2 * r * N * K ≤ 2 * 2 ^ 51 * 2 ^ 24 * 2 ^ 16 := by gcongr
    _ = 2 ^ 92 := by norm_num

theorem decT_le {D : Dims} (hr : rowsD D ≤ 2 ^ 51) (hN : D.N ≤ 2 ^ 24) (hK : D.K ≤ 2 ^ 16) :
    decT D ≤ 2 ^ 92 := by
  unfold decT; exact decT_le_gen hr hN hK

theorem decT_Dc_le : decT Dc ≤ 2 ^ 92 := decT_le rowsD_Dc_le Dc_N.le Params.Kc_le

/-- **The time of the decoder at `Dc`**: at most `2^270` steps. -/
theorem time_decR_Dc : (decR Dc nDc).time ≤ 2 ^ 270 :=
  (Tape.XProg.time_decodeMX_le false Dc.K (decT Dc) nDc).trans
    (decTime_le_gen nDc_le Params.Kc_le decT_Dc_le)

/-- **The states of the decoder at `Dc`**: at most `2^16`. -/
theorem states_decR_Dc : (decR Dc nDc).states ≤ 2 ^ 16 := by
  have hK : Dc.K < 2 ^ 93 := lt_of_le_of_lt Params.Kc_le (by norm_num)
  have hT : decT Dc + 1 < 2 ^ 93 := by have := decT_Dc_le; omega
  refine (Tape.XProg.states_decodeMX_le false hK hT).trans (by norm_num)

end AdvancedEncryption.ExpLUT.Prog
