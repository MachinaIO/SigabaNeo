import PE.Impl.RingBTVW.Prog.DecTightLib
import PE.Impl.RingBTVW.Prog.DecGenCost
import SigabaNeoStd.Lattices.ProgAlgo.SimStepT
/-!
# The end of decryption, per tape

`ub_decFinB` bounds `decFinB` from one bound on every tape: `decFP` (three matrix products, three
ring sums) is charged `6000 · (M + 1)^8`. Here, from tape `0` below `F0` and tape `2` (the word of
`c_f̂`) below `2k N K`, every other tape blank (the per-tape output of the `c_f̂` block):

* the six reads append exactly their lengths (`ph_getAt'`), the templates are exact;
* **`ph_decFP'`**: `decFP` composed from the certified summaries of `matMulP`, `addRWP`, `subRWP`
  (`SpecT`, `StepT`): `(2U + 3) · (wMV d + wMV nT + wMV 2k + 3 (29 N K + 28 N + 7))`, `U` the
  longest of its `101` tapes, `wMV n ≈ 22 n N² K²` (`n` ring products);
* **`ph_decFinB'`**: the whole block, the rounding test `ballP` still uniform (`419 (M + 1)^3`) at
  the small bound `M` of the store.
-/

namespace AdvancedEncryption.RingBTVW.Prog

theorem ite_mono'' {c : Prop} [Decidable c] {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    (if c then a else b) ≤ (if c then a' else b') := by
  split <;> assumption
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.XProg SigabaNeo.Tape.Sym SigabaNeo.Tape.Prog.SpecT
open scoped SigabaNeo.Tape.Prog

/-- The per-tape bounds around `decFP` (its own `101` tapes): the words, the templates, the
outputs `o…`, every other tape below `U`. -/
def dfV (K N d nT k U o26 o27 o36 o37 o38 o39 : ℕ) : Fin 101 → ℕ := fun t =>
  if t.val = 2 then 2 * k * (N * K) else if t.val = 30 then d * (N * K)
  else if t.val = 31 then d * (N * K) else if t.val = 32 then nT * (N * K)
  else if t.val = 33 then nT * (N * K) else if t.val = 34 then 2 * k * (N * K)
  else if t.val = 35 then N * K else if t.val = 26 then o26 else if t.val = 27 then o27
  else if t.val = 36 then o36 else if t.val = 37 then o37 else if t.val = 38 then o38
  else if t.val = 39 then o39 else if t.val = 6 then K else if t.val = 7 then N
  else if t.val = 8 then N * K else if t.val = 13 then 2 * k else if t.val = 14 then 1
  else if t.val = 15 then 1 else if t.val = 16 then d else if t.val = 17 then nT
  else if t.val = 29 then N * K else U

section D
variable {K N d nT k U o26 o27 o36 o37 o38 o39 : ℕ}

macro "df_tac " j:ident : tactic => `(tactic| (fin_cases $j:ident <;> simp [ProgKeyR.mmR, ProgKeyR.bzR, ProgKeyR.plR, dfV, bnd, aGet, σMat, σMat', σRing, σRing', pTop, pmnNK, pnlNK, pK, pN, pNK, pm, pn, pl, pmlNK, mo, pEval, mEval, vars, top] <;> (try ring_nf at *) <;> (try exact le_rfl) <;> omega))

theorem df_mono {o26 o27 o36 o37 o38 o39 p26 p27 p36 p37 p38 p39 : ℕ} (h1 : o26 ≤ p26)
    (h2 : o27 ≤ p27) (h3 : o36 ≤ p36) (h4 : o37 ≤ p37) (h5 : o38 ≤ p38) (h6 : o39 ≤ p39) :
    dfV K N d nT k U o26 o27 o36 o37 o38 o39 ≤ dfV K N d nT k U p26 p27 p36 p37 p38 p39 := fun t => by
  simp only [dfV]; repeat (first | exact le_rfl | assumption | apply ite_mono'')

theorem df_mat1_in (hU : o36 ≤ U) (j : Fin 59) :
    dfV K N d nT k U o26 o27 o36 o37 o38 o39 (ProgKeyR.mmR 36 30 31 14 16 15 29 j) ≤
      bnd (vars U N K 1 d 1 0) (σMat ++ List.replicate 49 pTop) j := by df_tac j
theorem df_mat1_out (j : Fin 59) :
    bnd (vars U N K 1 d 1 0) (σMat' ++ List.replicate 59 pTop) j ≤
      dfV K N d nT k U o26 o27 (N * K) o37 o38 o39 (ProgKeyR.mmR 36 30 31 14 16 15 29 j) := by df_tac j
theorem df_mat2_in (hU : o37 ≤ U) (j : Fin 59) :
    dfV K N d nT k U o26 o27 o36 o37 o38 o39 (ProgKeyR.mmR 37 32 33 14 17 15 29 j) ≤
      bnd (vars U N K 1 nT 1 0) (σMat ++ List.replicate 49 pTop) j := by df_tac j
theorem df_mat2_out (j : Fin 59) :
    bnd (vars U N K 1 nT 1 0) (σMat' ++ List.replicate 59 pTop) j ≤
      dfV K N d nT k U o26 o27 o36 (N * K) o38 o39 (ProgKeyR.mmR 37 32 33 14 17 15 29 j) := by df_tac j
theorem df_mat3_in (hU : o38 ≤ U) (j : Fin 59) :
    dfV K N d nT k U o26 o27 o36 o37 o38 o39 (ProgKeyR.mmR 38 2 34 14 13 15 29 j) ≤
      bnd (vars U N K 1 (2 * k) 1 0) (σMat ++ List.replicate 49 pTop) j := by df_tac j
theorem df_mat3_out (j : Fin 59) :
    bnd (vars U N K 1 (2 * k) 1 0) (σMat' ++ List.replicate 59 pTop) j ≤
      dfV K N d nT k U o26 o27 o36 o37 (N * K) o39 (ProgKeyR.mmR 38 2 34 14 13 15 29 j) := by df_tac j
theorem df_add1_in (hU : o26 ≤ U) (j : Fin 28) :
    dfV K N d nT k U o26 o27 (N * K) (N * K) o38 o39 (ProgKeyR.bzR 26 36 37 6 7 j) ≤
      bnd (vars U N K 0 0 0 0) (σRing ++ List.replicate 23 pTop) j := by df_tac j
theorem df_add1_out (j : Fin 28) :
    bnd (vars U N K 0 0 0 0) (σRing' ++ List.replicate 28 pTop) j ≤
      dfV K N d nT k U (N * K) o27 (N * K) (N * K) o38 o39 (ProgKeyR.bzR 26 36 37 6 7 j) := by df_tac j
theorem df_add2_in (hU : o27 ≤ U) (j : Fin 28) :
    dfV K N d nT k U (N * K) o27 o36 o37 (N * K) o39 (ProgKeyR.bzR 27 26 38 6 7 j) ≤
      bnd (vars U N K 0 0 0 0) (σRing ++ List.replicate 23 pTop) j := by df_tac j
theorem df_add2_out (j : Fin 28) :
    bnd (vars U N K 0 0 0 0) (σRing' ++ List.replicate 28 pTop) j ≤
      dfV K N d nT k U (N * K) (N * K) o36 o37 (N * K) o39 (ProgKeyR.bzR 27 26 38 6 7 j) := by df_tac j
theorem df_sub_in (hU : o39 ≤ U) (j : Fin 28) :
    dfV K N d nT k U o26 (N * K) o36 o37 o38 o39 (ProgKeyR.bzR 39 35 27 6 7 j) ≤
      bnd (vars U N K 0 0 0 0) (σRing ++ List.replicate 23 pTop) j := by df_tac j
theorem df_sub_out (j : Fin 28) :
    bnd (vars U N K 0 0 0 0) (σRing' ++ List.replicate 28 pTop) j ≤
      dfV K N d nT k U o26 (N * K) o36 o37 o38 (N * K) (ProgKeyR.bzR 39 35 27 6 7 j) := by df_tac j

end D

/-- The steps of `matMulP` on `1 × n` by `n × 1` (`boundsT_matMulP`). -/
def wMV (N K n : ℕ) : ℕ :=
  1 * n * 1 * (22 * N ^ 2 * K ^ 2 + 97 * N ^ 2 * K + 61 * N ^ 2 + 105 * (N * K) + 117 * N +
    23 * K + 73) + 1 * n * 1 ^ 2 * (3 * (N * K) + 4) + 1 * n * (3 * (N * K) + 4) +
    1 * 1 * (9 * (N * K) + 15) + 8 * 1 + 5

theorem pEval_wMat (U N K n : ℕ) :
    (2 * top (vars U N K 1 n 1 0) + 3) * pEval (vars U N K 1 n 1 0) SigabaNeo.Tape.Prog.SpecT.wMat = (2 * U + 3) * wMV N K n := by
  simp [top, SigabaNeo.Tape.Prog.SpecT.wMat, pEval, mEval, vars, wMV]; ring

theorem pEval_wAdd (U N K : ℕ) :
    (2 * top (vars U N K 0 0 0 0) + 3) * pEval (vars U N K 0 0 0 0) wAdd =
      (2 * U + 3) * (29 * (N * K) + 28 * N + 7) := by
  simp [top, wAdd, pEval, mEval, vars]; ring

theorem df_le {K N d nT k U o26 o27 o36 o37 o38 o39 : ℕ} (h1 : 2 * k * (N * K) ≤ U) (h2 : d * (N * K) ≤ U)
    (h3 : nT * (N * K) ≤ U) (h4 : N * K ≤ U) (h5 : o26 ≤ U) (h6 : o27 ≤ U) (h7 : o36 ≤ U)
    (h8 : o37 ≤ U) (h9 : o38 ≤ U) (h10 : o39 ≤ U) (h11 : K ≤ U) (h12 : N ≤ U) (h13 : 2 * k ≤ U)
    (h14 : 1 ≤ U) (h15 : d ≤ U) (h16 : nT ≤ U) (t : Fin 101) :
    dfV K N d nT k U o26 o27 o36 o37 o38 o39 t ≤ U := by
  fin_cases t <;> simp [dfV] <;> omega

theorem df_rest {K N d nT k U o26 o27 o36 o37 o38 o39 p26 p27 p36 p37 p38 p39 : ℕ} (t : Fin 101)
    (h26 : o26 ≤ p26 ∨ t.val ≠ 26) (h27 : o27 ≤ p27 ∨ t.val ≠ 27) (h36 : o36 ≤ p36 ∨ t.val ≠ 36)
    (h37 : o37 ≤ p37 ∨ t.val ≠ 37) (h38 : o38 ≤ p38 ∨ t.val ≠ 38) (h39 : o39 ≤ p39 ∨ t.val ≠ 39) :
    dfV K N d nT k U o26 o27 o36 o37 o38 o39 t ≤ dfV K N d nT k U p26 p27 p36 p37 p38 p39 t := by
  fin_cases t <;> simp_all [dfV]

theorem inj_mm1 : Function.Injective (ProgKeyR.mmR 36 30 31 14 16 15 29) := by decide
theorem inj_mm2 : Function.Injective (ProgKeyR.mmR 37 32 33 14 17 15 29) := by decide
theorem inj_mm3 : Function.Injective (ProgKeyR.mmR 38 2 34 14 13 15 29) := by decide
theorem inj_bz1 : Function.Injective (ProgKeyR.bzR 26 36 37 6 7) := by decide
theorem inj_bz2 : Function.Injective (ProgKeyR.bzR 27 26 38 6 7) := by decide
theorem inj_bz3 : Function.Injective (ProgKeyR.bzR 39 35 27 6 7) := by decide

set_option maxHeartbeats 1000000 in
/-- **`decFP` per tape**: three certified matrix products and three ring sums, each primitive
charged the longest of its `101` tapes. -/
theorem ph_decFP' (K N d nT k U : ℕ) (h1 : 2 * k * (N * K) ≤ U) (h2 : d * (N * K) ≤ U)
    (h3 : nT * (N * K) ≤ U) (h4 : N * K ≤ U) (h11 : K ≤ U) (h12 : N ≤ U) (h13 : 2 * k ≤ U)
    (h14 : 1 ≤ U) (h15 : d ≤ U) (h16 : nT ≤ U) :
    Ph (.prog ProgKeyR.decFP) (dfV K N d nT k U U U U U U U)
      ((2 * U + 3) * wMV N K d + ((2 * U + 3) * wMV N K nT + ((2 * U + 3) * wMV N K (2 * k) +
        ((2 * U + 3) * (29 * (N * K) + 28 * N + 7) + ((2 * U + 3) * (29 * (N * K) + 28 * N + 7) +
          (2 * U + 3) * (29 * (N * K) + 28 * N + 7))))))
      (dfV K N d nT k U (N * K) (N * K) (N * K) (N * K) (N * K) (N * K)) := by
  have hle := fun {o26 o27 o36 o37 o38 o39 : ℕ} (a : o26 ≤ U) (b : o27 ≤ U) (c : o36 ≤ U)
      (e : o37 ≤ U) (f : o38 ≤ U) (g : o39 ≤ U) (t : Fin 101) =>
    df_le (K := K) (N := N) (d := d) (nT := nT) (k := k) (o26 := o26) (o27 := o27) (o36 := o36)
      (o37 := o37) (o38 := o38) (o39 := o39) h1 h2 h3 h4 a b c e f g h11 h12 h13 h14 h15 h16 t
  have q1 := ph_mapSound (u := ProgKeyR.mmR 36 30 31 14 16 15 29) inj_mm1
    SigabaNeo.Tape.Prog.StepT.sMat (vars U N K 1 d 1 0) (dfV K N d nT k U U U U U U U)
    (dfV K N d nT k U U U (N * K) U U U) (df_mat1_in le_rfl)
    (fun t => hle le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl t) df_mat1_out
    (fun t ht => df_rest t (.inl le_rfl) (.inl le_rfl) (.inr fun e => ht 0 (Fin.ext (by rw [e]; rfl))) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl))
  rw [pEval_wMat] at q1
  have q2 := ph_mapSound (u := ProgKeyR.mmR 37 32 33 14 17 15 29) inj_mm2
    SigabaNeo.Tape.Prog.StepT.sMat (vars U N K 1 nT 1 0) (dfV K N d nT k U U U (N * K) U U U)
    (dfV K N d nT k U U U (N * K) (N * K) U U) (df_mat2_in le_rfl)
    (fun t => hle le_rfl le_rfl h4 le_rfl le_rfl le_rfl t) df_mat2_out
    (fun t ht => df_rest t (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inr fun e => ht 0 (Fin.ext (by rw [e]; rfl))) (.inl le_rfl) (.inl le_rfl))
  rw [pEval_wMat] at q2
  have q3 := ph_mapSound (u := ProgKeyR.mmR 38 2 34 14 13 15 29) inj_mm3
    SigabaNeo.Tape.Prog.StepT.sMat (vars U N K 1 (2 * k) 1 0) (dfV K N d nT k U U U (N * K) (N * K) U U)
    (dfV K N d nT k U U U (N * K) (N * K) (N * K) U) (df_mat3_in le_rfl)
    (fun t => hle le_rfl le_rfl h4 h4 le_rfl le_rfl t) df_mat3_out
    (fun t ht => df_rest t (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inr fun e => ht 0 (Fin.ext (by rw [e]; rfl))) (.inl le_rfl))
  rw [pEval_wMat] at q3
  have q4 := ph_mapSound (u := ProgKeyR.bzR 26 36 37 6 7) inj_bz1
    SigabaNeo.Tape.Prog.StepT.sAdd (vars U N K 0 0 0 0) (dfV K N d nT k U U U (N * K) (N * K) (N * K) U)
    (dfV K N d nT k U (N * K) U (N * K) (N * K) (N * K) U) (df_add1_in le_rfl)
    (fun t => hle le_rfl le_rfl h4 h4 h4 le_rfl t) df_add1_out
    (fun t ht => df_rest t (.inr fun e => ht 0 (Fin.ext (by rw [e]; rfl))) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl))
  rw [pEval_wAdd] at q4
  have q5 := ph_mapSound (u := ProgKeyR.bzR 27 26 38 6 7) inj_bz2
    SigabaNeo.Tape.Prog.StepT.sAdd (vars U N K 0 0 0 0) (dfV K N d nT k U (N * K) U (N * K) (N * K) (N * K) U)
    (dfV K N d nT k U (N * K) (N * K) (N * K) (N * K) (N * K) U) (df_add2_in le_rfl)
    (fun t => hle h4 le_rfl h4 h4 h4 le_rfl t) df_add2_out
    (fun t ht => df_rest t (.inl le_rfl) (.inr fun e => ht 0 (Fin.ext (by rw [e]; rfl))) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl))
  rw [pEval_wAdd] at q5
  have q6 := ph_mapSound (u := ProgKeyR.bzR 39 35 27 6 7) inj_bz3
    SigabaNeo.Tape.Prog.StepT.sSub (vars U N K 0 0 0 0) (dfV K N d nT k U (N * K) (N * K) (N * K) (N * K) (N * K) U)
    (dfV K N d nT k U (N * K) (N * K) (N * K) (N * K) (N * K) (N * K)) (df_sub_in le_rfl)
    (fun t => hle h4 h4 h4 h4 h4 le_rfl t) df_sub_out
    (fun t ht => df_rest t (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inl le_rfl) (.inr fun e => ht 0 (Fin.ext (by rw [e]; rfl))))
  rw [pEval_wAdd] at q6
  exact ph_seqP q1 (ph_seqP q2 (ph_seqP q3 (ph_seqP q4 (ph_seqP q5 q6))))

/-! ### Reading a block, per tape -/

theorem ph_getAt' (o L : ℕ) {k : ℕ} {src dst tmp a b : Fin k} (h1 : tmp ≠ a) (h2 : tmp ≠ b)
    (h3 : tmp ≠ dst) (h4 : a ≠ dst) (h5 : b ≠ dst) (β : Fin k → ℕ) :
    Ph (getAt o L src dst tmp a b) β (getT o L (supB β))
      (fun t => if t = dst then β dst + L else if t = tmp ∨ t = a ∨ t = b then supB β + 1 + L
        else β t) := by
  intro ℓ hℓ
  have hp := ph_getAt o L (src := src) (dst := dst) h1 h2 β ℓ hℓ
  refine ⟨hp.1, fun t => ?_⟩
  dsimp only
  split_ifs with hd hab
  · subst hd
    show SigabaNeo.Tape.Prog.lenBoundT (.prim (.clear tmp)) _ t ≤ _
    simp only [SigabaNeo.Tape.Prog.lenBoundT, Prim.lenT, Function.update_apply, if_neg (Ne.symm h3), ne_eq, h3.symm, not_false_eq_true]
    rw [lenBoundT_prefP_dst L h4 h5]
    have hX : (SigabaNeo.Tape.Prog.seq (.prim (.copy tmp src)) (SigabaNeo.Tape.Prog.tailsP tmp o)).Preserves t :=
      ⟨by simp [SigabaNeo.Tape.Prog.Preserves, Prim.writes]; exact fun e => h3 e.symm, preserves_tailsP h3 o⟩
    show SigabaNeo.Tape.Prog.lenBoundT _ ℓ t + L ≤ _
    rw [SigabaNeo.Tape.Prog.lenBoundT_of_preserves t _ hX ℓ]
    exact Nat.add_le_add_right (hℓ t) L
  · have := hp.2 t; simp only at this
    rcases hab with rfl | rfl | rfl <;> simpa using this
  · have := hp.2 t; simp only at this
    push Not at hab
    rwa [if_neg (by simp [hd, hab.1, hab.2.1, hab.2.2])] at this

/-! ### The outer bounds -/

/-- Before the templates: tape `2`, the words `30 … 35`, every other tape below `U`. -/
def dgV (U a2 a30 a31 a32 a33 a34 a35 : ℕ) : Fin 256 → ℕ := fun t =>
  if t.val = 2 then a2 else if t.val = 30 then a30 else if t.val = 31 then a31
  else if t.val = 32 then a32 else if t.val = 33 then a33 else if t.val = 34 then a34
  else if t.val = 35 then a35 else U

/-- With the words and the templates. -/
def dtV (K N d nT k U a2 : ℕ) : Fin 256 → ℕ := fun t =>
  if t.val = 2 then a2 else if t.val = 30 then d * (N * K)
  else if t.val = 31 then d * (N * K) else if t.val = 32 then nT * (N * K)
  else if t.val = 33 then nT * (N * K) else if t.val = 34 then 2 * k * (N * K)
  else if t.val = 35 then N * K else if t.val = 6 then K else if t.val = 7 then N
  else if t.val = 8 then N * K else if t.val = 10 then 1 else if t.val = 13 then 2 * k
  else if t.val = 14 then 1 else if t.val = 15 then 1 else if t.val = 16 then d
  else if t.val = 17 then nT else if t.val = 29 then N * K else U

section G
variable {U a2 a30 a31 a32 a33 a34 a35 S L U' : ℕ}

macro "g_tac" : tactic => `(tactic| (intro t; fin_cases t <;> simp [dgV] <;> omega))

theorem g30 (hs : supB (dgV U a2 a30 a31 a32 a33 a34 a35) ≤ S) (hU : U ≤ U') (hS : S + 1 + L ≤ U') :
    (fun t : Fin 256 => if t = 30 then dgV U a2 a30 a31 a32 a33 a34 a35 30 + L
      else if t = 102 ∨ t = 103 ∨ t = 104 then supB (dgV U a2 a30 a31 a32 a33 a34 a35) + 1 + L
      else dgV U a2 a30 a31 a32 a33 a34 a35 t) ≤ dgV U' a2 (a30 + L) a31 a32 a33 a34 a35 := by g_tac
theorem g31 (hs : supB (dgV U a2 a30 a31 a32 a33 a34 a35) ≤ S) (hU : U ≤ U') (hS : S + 1 + L ≤ U') :
    (fun t : Fin 256 => if t = 31 then dgV U a2 a30 a31 a32 a33 a34 a35 31 + L
      else if t = 102 ∨ t = 103 ∨ t = 104 then supB (dgV U a2 a30 a31 a32 a33 a34 a35) + 1 + L
      else dgV U a2 a30 a31 a32 a33 a34 a35 t) ≤ dgV U' a2 a30 (a31 + L) a32 a33 a34 a35 := by g_tac
theorem g32 (hs : supB (dgV U a2 a30 a31 a32 a33 a34 a35) ≤ S) (hU : U ≤ U') (hS : S + 1 + L ≤ U') :
    (fun t : Fin 256 => if t = 32 then dgV U a2 a30 a31 a32 a33 a34 a35 32 + L
      else if t = 102 ∨ t = 103 ∨ t = 104 then supB (dgV U a2 a30 a31 a32 a33 a34 a35) + 1 + L
      else dgV U a2 a30 a31 a32 a33 a34 a35 t) ≤ dgV U' a2 a30 a31 (a32 + L) a33 a34 a35 := by g_tac
theorem g33 (hs : supB (dgV U a2 a30 a31 a32 a33 a34 a35) ≤ S) (hU : U ≤ U') (hS : S + 1 + L ≤ U') :
    (fun t : Fin 256 => if t = 33 then dgV U a2 a30 a31 a32 a33 a34 a35 33 + L
      else if t = 102 ∨ t = 103 ∨ t = 104 then supB (dgV U a2 a30 a31 a32 a33 a34 a35) + 1 + L
      else dgV U a2 a30 a31 a32 a33 a34 a35 t) ≤ dgV U' a2 a30 a31 a32 (a33 + L) a34 a35 := by g_tac
theorem g34 (hs : supB (dgV U a2 a30 a31 a32 a33 a34 a35) ≤ S) (hU : U ≤ U') (hS : S + 1 + L ≤ U') :
    (fun t : Fin 256 => if t = 34 then dgV U a2 a30 a31 a32 a33 a34 a35 34 + L
      else if t = 102 ∨ t = 103 ∨ t = 104 then supB (dgV U a2 a30 a31 a32 a33 a34 a35) + 1 + L
      else dgV U a2 a30 a31 a32 a33 a34 a35 t) ≤ dgV U' a2 a30 a31 a32 a33 (a34 + L) a35 := by g_tac
theorem g35 (hs : supB (dgV U a2 a30 a31 a32 a33 a34 a35) ≤ S) (hU : U ≤ U') (hS : S + 1 + L ≤ U') :
    (fun t : Fin 256 => if t = 35 then dgV U a2 a30 a31 a32 a33 a34 a35 35 + L
      else if t = 102 ∨ t = 103 ∨ t = 104 then supB (dgV U a2 a30 a31 a32 a33 a34 a35) + 1 + L
      else dgV U a2 a30 a31 a32 a33 a34 a35 t) ≤ dgV U' a2 a30 a31 a32 a33 a34 (a35 + L) := by g_tac

theorem dgV_le (h2 : a2 ≤ U) (h30 : a30 ≤ U) (h31 : a31 ≤ U) (h32 : a32 ≤ U) (h33 : a33 ≤ U)
    (h34 : a34 ≤ U) (h35 : a35 ≤ U) : supB (dgV U a2 a30 a31 a32 a33 a34 a35) ≤ U :=
  supB_le_of fun t => by fin_cases t <;> simp [dgV] <;> omega

end G

section T
variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

theorem tmplB_dec {U a2 : ℕ} (hU1 : K ≤ U) (hU2 : N ≤ U) (hU3 : N * K ≤ U) (hU4 : 1 ≤ U)
    (hU5 : 2 * k ≤ U) (hU6 : c.d ≤ U) (hU7 : Algo.nT k ≤ U) :
    tmplB (120 : Fin 256) (decTmpl c) (dgV U a2 (0 + c.d * (N * K)) (0 + c.d * (N * K))
      (0 + Algo.nT k * (N * K)) (0 + Algo.nT k * (N * K)) (0 + 2 * k * (N * K)) (0 + N * K)) ≤
      dtV K N c.d (Algo.nT k) k U a2 := fun t => by
  fin_cases t <;> simp [tmplB, decTmpl, natB, dgV, dtV, max_le_iff] <;> omega

theorem dt_in {U a2 : ℕ} (h2 : a2 ≤ 2 * k * (N * K)) (h1 : 1 ≤ U) :
    (fun j : Fin 101 => dtV K N c.d (Algo.nT k) k U a2 (eKR j)) ≤
      dfV K N c.d (Algo.nT k) k U U U U U U U := fun j => by
  fin_cases j <;> simp [dtV, dfV, eKR_val, h2, h1]

end T

theorem embedF_le_const {m n : ℕ} (e : Fin m ↪ Fin n) {f : Fin n → ℕ} {g : Fin m → ℕ} {U : ℕ}
    (hf : ∀ t, f t ≤ U) (hg : ∀ j, g j ≤ U) : embedF e f g ≤ fun _ => U := fun t => by
  rcases embedF_cases e f g t with ⟨-, h⟩ | ⟨j, -, h⟩ <;> rw [h]
  · exact hf t
  · exact hg j

/-- The tail of `decFinB` after `decFP`, from every tape below `M`. -/
def decTailT (K M : ℕ) : ℕ :=
  ((2 * (M + 1) + 3) + (2 * (M + 1) + 3)) + (prefT K M + ((2 * (M + 1 + K + 1) + 3) +
    (419 * (M + 1 + K + 1) ^ 3 + ((2 * (M + 1 + K + 1) + 3) +
    ((max (putT ([true, false, false] : List Bool).length (M + 1 + K))
      (putT ([true, true, false] : List Bool).length (M + 1 + K)) + 1) +
    (256 * (2 * (max (M + 1 + K + ([true, false, false] : List Bool).length + 1)
        (M + 1 + K + ([true, true, false] : List Bool).length + 1) + 1) + 3) +
      (2 * (max (M + 1 + K + ([true, false, false] : List Bool).length + 1)
        (M + 1 + K + ([true, true, false] : List Bool).length + 1) + 1) + 3)))))))

open SigabaNeo.Tape.Prog (cp clr ballP) in
theorem ub_decTail (K M : ℕ) :
    UB (XProg.seq (XProg.prog (cp 28 39 ⨾ clr 39)) <| XProg.seq (prefP K 28 39 41 42) <|
      XProg.seq (XProg.prog (clr 28)) <|
      XProg.seq (XProg.frame eKR (XProg.prog (SigabaNeo.Tape.Prog.map ProgKeyR.ballR ballP))) <|
      XProg.seq (XProg.prog (clr 0)) <|
      XProg.seq (XProg.ifBit 40 (putW 0 [true, false, false]) (putW 0 [true, true, false]))
        (clearL clrAll)) M (decTailT K M)
      (max (M + 1 + K + ([true, false, false] : List Bool).length + 1)
        (M + 1 + K + ([true, true, false] : List Bool).length + 1)) := by
  refine ((show UB (XProg.prog (cp 28 39 ⨾ clr 39)) _ _ _ from
      fun ℓ hℓ => ((SigabaNeo.Tape.Prog.ubp_prim0 (.copy 28 39) rfl _).seq
        (SigabaNeo.Tape.Prog.ubp_prim0 (.clear 39) rfl _)) ℓ hℓ).seq <|
    (ub_prefP K 28 39 41 42 _).seq <| (ub_clear 28 _).seq <|
    ((ub_frame eKR _ noGrow_ballR _).mono
      ((SigabaNeo.Tape.Prog.timeBound_le _ noGrow_ballR _).trans
        (by rw [tbD_ballR, tbC_ballR])) le_rfl).seq <|
    (ub_clear 0 _).seq <|
    (ub_ifBit (ub_putW 0 [true, false, false] _) (ub_putW 0 [true, true, false] _)).seq <|
    ((ub_clearL _ clrAll).mono (Nat.add_le_add_right (Nat.mul_le_mul_right _ length_clrAll_le) _)
      le_rfl)).mono (le_of_eq ?_) le_rfl
  simp only [decTailT]

/-- **The time of `decFinB` per tape** (`B` the offsets and lengths, `U0` the input bound, `T`
the templates). -/
def decFT' (N K k d nT B U0 T : ℕ) : ℕ :=
  let U6 := U0 + 6 * (1 + B)
  let U7 := U6 + K
  getT B B U0 + (getT B B (U0 + (1 + B)) + (getT B B (U0 + 2 * (1 + B)) +
    (getT B B (U0 + 3 * (1 + B)) + (getT B B (U0 + 4 * (1 + B)) + (getT B B (U0 + 5 * (1 + B)) +
    ((K + 1) * (2 * (U6 + K + 1) + 3) + (11 * ((2 * T + 1) * (4 * U7 + 12)) +
    (((2 * U7 + 3) * wMV N K d + ((2 * U7 + 3) * wMV N K nT + ((2 * U7 + 3) * wMV N K (2 * k) +
        ((2 * U7 + 3) * (29 * (N * K) + 28 * N + 7) + ((2 * U7 + 3) * (29 * (N * K) + 28 * N + 7) +
          (2 * U7 + 3) * (29 * (N * K) + 28 * N + 7)))))) + decTailT K U7))))))))

section Main
variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

set_option maxHeartbeats 4000000 in
/-- **`decFinB` per tape**: from tape `0` below `F0`, tape `2` below `F2 ≤ 2k N K`, the others
blank. -/
theorem ph_decFinB' (B U0 T F0 F2 : ℕ) (hB : ∀ x ∈ decOffs hk c, x ≤ B) (hF0 : F0 ≤ U0)
    (hF2 : F2 ≤ 2 * k * (N * K)) (hTU : T ≤ U0)
    (t1 : K ≤ T) (t2 : N ≤ T) (t3 : N * K ≤ T) (t4 : 1 ≤ T) (t5 : 2 * k ≤ T) (t6 : c.d ≤ T)
    (t7 : Algo.nT k ≤ T) (t8 : 2 * k * (N * K) ≤ U0) :
    Ph (decFinB hk c) (fun t => if t.val = 0 then F0 else if t.val = 2 then F2 else 0)
      (decFT' N K k c.d (Algo.nT k) B U0 T)
      (fun _ => max (U0 + 6 * (1 + B) + K + 1 + K + ([true, false, false] : List Bool).length + 1)
        (U0 + 6 * (1 + B) + K + 1 + K + ([true, true, false] : List Bool).length + 1)) := by
  have hb := fun x (hx : x ∈ decOffs hk c) => hB x hx
  simp only [decOffs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := hb
  have p1 := (ph_getAt' (fixLen (skEnc hk c) + lPsi (N := N) (K := K) hk) (c.d * (N * K))
    (src := 0) (dst := 30) (tmp := 102) (a := 103) (b := 104) (by decide) (by decide) (by decide)
    (by decide) (by decide) (dgV U0 F2 0 0 0 0 0 0)).mono le_rfl
    (getT_mono' b1 b2 (dgV_le (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (g30 (S := U0) (U' := U0 + (1 + B)) (dgV_le (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)) (by omega) (by omega))
  have p2 := (ph_getAt' (lenPK hk c) (c.d * (N * K))
    (src := 0) (dst := 31) (tmp := 102) (a := 103) (b := 104) (by decide) (by decide) (by decide)
    (by decide) (by decide) (dgV (U0 + (1 + B)) F2 (0 + c.d * (N * K)) 0 0 0 0 0)).mono le_rfl
    (getT_mono' b3 b2 (dgV_le (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (g31 (S := U0 + (1 + B)) (U' := U0 + 2 * (1 + B)) (dgV_le (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega))
  have p3 := (ph_getAt' (fixLen (skEnc hk c) + lPsi (N := N) (K := K) hk + c.d * (N * K))
    (Algo.nT k * (N * K))
    (src := 0) (dst := 32) (tmp := 102) (a := 103) (b := 104) (by decide) (by decide) (by decide)
    (by decide) (by decide) (dgV (U0 + 2 * (1 + B)) F2 (0 + c.d * (N * K)) (0 + c.d * (N * K)) 0 0 0 0)).mono le_rfl
    (getT_mono' b4 b5 (dgV_le (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (g32 (S := U0 + 2 * (1 + B)) (U' := U0 + 3 * (1 + B)) (dgV_le (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega))
  have p4 := (ph_getAt' (lenPK hk c + c.d * (N * K)) (Algo.nT k * (N * K))
    (src := 0) (dst := 33) (tmp := 102) (a := 103) (b := 104) (by decide) (by decide) (by decide)
    (by decide) (by decide) (dgV (U0 + 3 * (1 + B)) F2 (0 + c.d * (N * K)) (0 + c.d * (N * K))
      (0 + Algo.nT k * (N * K)) 0 0 0)).mono le_rfl
    (getT_mono' b6 b5 (dgV_le (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (g33 (S := U0 + 3 * (1 + B)) (U' := U0 + 4 * (1 + B)) (dgV_le (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega))
  have p5 := (ph_getAt' (lenPK hk c + c.d * (N * K) + Algo.nT k * (N * K)) (2 * k * (N * K))
    (src := 0) (dst := 34) (tmp := 102) (a := 103) (b := 104) (by decide) (by decide) (by decide)
    (by decide) (by decide) (dgV (U0 + 4 * (1 + B)) F2 (0 + c.d * (N * K)) (0 + c.d * (N * K))
      (0 + Algo.nT k * (N * K)) (0 + Algo.nT k * (N * K)) 0 0)).mono le_rfl
    (getT_mono' b7 b8 (dgV_le (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (g34 (S := U0 + 4 * (1 + B)) (U' := U0 + 5 * (1 + B)) (dgV_le (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega))
  have p6 := (ph_getAt' (fixLen (skEnc hk c) + fixLen (ctEnc hk c) - N * K) (N * K)
    (src := 0) (dst := 35) (tmp := 102) (a := 103) (b := 104) (by decide) (by decide) (by decide)
    (by decide) (by decide) (dgV (U0 + 5 * (1 + B)) F2 (0 + c.d * (N * K)) (0 + c.d * (N * K))
      (0 + Algo.nT k * (N * K)) (0 + Algo.nT k * (N * K)) (0 + 2 * k * (N * K)) 0)).mono le_rfl
    (getT_mono' b9 b10 (dgV_le (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (g35 (S := U0 + 5 * (1 + B)) (U' := U0 + 6 * (1 + B)) (dgV_le (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega))
  set U6 := U0 + 6 * (1 + B) with hU6
  set β6 := dgV U6 F2 (0 + c.d * (N * K)) (0 + c.d * (N * K)) (0 + Algo.nT k * (N * K))
    (0 + Algo.nT k * (N * K)) (0 + 2 * k * (N * K)) (0 + N * K) with hβ6
  have hs6 : supB β6 ≤ U6 := dgV_le (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have hlen : (Algo.decRadW K).length = K := SigabaNeo.Lattices.Algo.length_toBits _ _
  have p7 := (ph_putW (4 : Fin 256) (Algo.decRadW K) β6).mono le_rfl
    (show _ ≤ (K + 1) * (2 * (U6 + K + 1) + 3) by rw [hlen]; exact Nat.mul_le_mul le_rfl (by omega))
    (show _ ≤ dgV (U6 + K) F2 (0 + c.d * (N * K)) (0 + c.d * (N * K)) (0 + Algo.nT k * (N * K))
      (0 + Algo.nT k * (N * K)) (0 + 2 * k * (N * K)) (0 + N * K) from fun t => by
        rw [hlen]; fin_cases t <;> simp [β6, dgV, Function.update_apply] <;> omega)
  set U7 := U6 + K with hU7
  have p8 := (ph_tmplP (120 : Fin 256) (decTmpl c) _ (by simp [decTmpl])).mono le_rfl
    (tmplTT_le2 (120 : Fin 256) U7 T (by omega) (decTmpl c) _
      (fun t => by fin_cases t <;> simp [dgV] <;> omega)
      (by simp only [decTmpl, List.mem_cons, List.not_mem_nil, or_false]
          rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption))
    (tmplB_dec (U := U7) (a2 := F2) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega))
  have p9 := (ph_frame eKR ((ph_decFP' K N c.d (Algo.nT k) k U7 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mono
    (dt_in hF2 (by omega)) le_rfl le_rfl)).mono le_rfl le_rfl
    (embedF_le_const eKR (U := U7) (fun t => by fin_cases t <;> simp [dtV] <;> omega)
      (fun j => df_le (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) j))
  have p10 := ph_of_ub (β := fun _ => U7) (fun _ => le_rfl) (ub_decTail K U7)
  rw [decFinB, getP_eq, getP_eq, getP_eq, getP_eq, getP_eq, getP_eq]
  refine (p1.seq <| p2.seq <| p3.seq <| p4.seq <| p5.seq <| p6.seq <| p7.seq <| p8.seq <|
    p9.seq p10).mono ?_ (le_of_eq ?_) (fun _ => le_rfl)
  · intro t; fin_cases t <;> simp [dgV] <;> omega
  · simp only [decFT', hU6, hU7, decTmpl, List.length_cons, List.length_nil]
    try ring

end Main
end AdvancedEncryption.RingBTVW.Prog
