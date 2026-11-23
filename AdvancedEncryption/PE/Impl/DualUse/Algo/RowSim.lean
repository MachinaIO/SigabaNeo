import PE.Impl.DualUse.SimKeyGame

/-!
# Key rows and `c_f̂` as a row of the simulated trapdoor

The simulated trapdoor `simKeyMat Rm x W Ψ Bj f` (the short matrix of the simulation of the
reductions) is a polynomial identity in its inputs: no relation between them is needed to compute
it. Read at one row `r`, it gives the two homomorphic evaluations of the real algorithms:

* **`keyMatrix_eq_rowSim`**: with `Ψ = 0`, `x = 0` and row `r` of every `W_j` equal to `B_j`
  (row `r` of every `Rᵢ` zero), `B_f̂ = row_r W_f + f(0) G̲`;
* **`evalCiphertext_eq_rowSim`**: with `Ψ` the ciphertext's, `x = 0`, row `r` of every `W_j`
  equal to `c_j`, and rows `r'`, `r` of `Rᵢ` the two rows of `Ψᵢ`,
  `c_f̂ = row_r W_f + f(0) · (second row of G)`.

The other rows of `W_j`, `Rᵢ` are free; the machines use them to carry data across the `W_f`
block. `f(0) = 1` for every window predicate (`circ_eval_zero_win`): the date `(0, 0)` is not
valid.
-/

namespace AdvancedEncryption.DualUse

open SigabaNeo SigabaNeo.Lattices Matrix AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

section Generic

variable {R : Type*} [CommRing R] {k : ℕ} {m : Type*} [Fintype m] [DecidableEq m]

/-- Row `r` of a matrix, as a one-row matrix. -/
def rowAt {W : Type*} (M : Matrix m W R) (r : m) : Matrix (Fin 1) W R := Matrix.of fun _ col => M r col

omit [Fintype m] [DecidableEq m] in
theorem rowAt_mul {W W' : Type*} [Fintype W] (M : Matrix m W R) (A : Matrix W W' R) (r : m) :
    rowAt (M * A) r = rowAt M r * A := by
  ext i col; simp [rowAt, Matrix.mul_apply]

omit [Fintype m] [DecidableEq m] in
theorem rowAt_add {W : Type*} (M M' : Matrix m W R) (r : m) :
    rowAt (M + M') r = rowAt M r + rowAt M' r := by
  ext i col; simp [rowAt]

omit [Fintype m] [DecidableEq m] in
theorem rowAt_neg {W : Type*} (M : Matrix m W R) (r : m) : rowAt (-M) r = -rowAt M r := by
  ext i col; simp [rowAt]

omit [Fintype m] [DecidableEq m] in
theorem rowAt_smul {W : Type*} (a : R) (M : Matrix m W R) (r : m) :
    rowAt (a • M) r = a • rowAt M r := by
  ext i col; simp [rowAt]

omit [Fintype m] [DecidableEq m] in
theorem rowAt_zero {W : Type*} (r : m) : rowAt (0 : Matrix m W R) r = 0 := by
  ext i col; simp [rowAt]

omit [Fintype m] [DecidableEq m] in
theorem rowAt_sum {W ι : Type*} (s : Finset ι) (M : ι → Matrix m W R) (r : m) :
    rowAt (∑ b ∈ s, M b) r = ∑ b ∈ s, rowAt (M b) r := by
  ext i col; simp [rowAt, Matrix.sum_apply]

/-- The unit row `e_r`. -/
def unitRow (r : m) : Matrix (Fin 1) m R := Matrix.of fun _ j => if j = r then 1 else 0

omit [DecidableEq m] in
theorem unitRow_mul [DecidableEq m] {W : Type*} (r : m) (M : Matrix m W R) :
    unitRow r * M = rowAt M r := by
  ext i col
  simp [unitRow, rowAt, Matrix.mul_apply]

omit [Fintype m] [DecidableEq m] in
/-- **The `W`-row of the simulation is `EvalFX`** on the rows: `row_r` of `slpSim` is `slpEnc` of the
rows `r` of the `W_j`. -/
theorem rowAt_slpSim {r' W ι : Type*} [Fintype r'] [Fintype W] (Γ : GadgetMatrix R r' W)
    (A : ι → Matrix r' W R) (Wm : ι → Matrix m W R) (x : ι → R) (p : SLP ι) (w : Wire ι) (r : m) :
    rowAt (slpSim Γ A Wm x p w) r = slpEnc Γ A x (fun j => rowAt (Wm j) r) p w := by
  have h := SLP.valueOf_map (fun i => (A i, Wm i, x i)) (Γ.G, 0, 1) (simStep Γ)
    (fun j => (A j, x j, rowAt (Wm j) r)) (Γ.G, 1, 0) (encStep Γ)
    (fun u => (u.1, u.2.2, rowAt u.2.1 r)) (fun _ => rfl) (by simp [rowAt_zero])
    (fun a b => by
      simp only [simStep, encStep, rowAt_neg, rowAt_add, rowAt_mul, rowAt_smul]) p w
  exact congrArg (fun t => t.2.2) h

end Generic

variable {N K k : ℕ} {hk : 2 ^ K < 2 ^ k} {c : Conf N K k}

/-- The date `(0, 0)`: every bit `false`. -/
def date0 : Date := (0, 0)

theorem bitsOf_date0 (i : Fin nA) : bitsOf date0 i = false := by
  fin_cases i <;> rfl

/-- **A window predicate is true on the date `(0, 0)`** (it is not a valid date). -/
theorem evalBool_date0 (w : Window) :
    SLP.evalBool (bitsOf date0) (predC (winWord w)).1 (predC (winWord w)).2 = true := by
  have hne : parse (winWord w) ≠ [] := by
    rw [winWord, parse_unparse, winGates, predGates, toGates]
    simp
  rw [predC, ← evalGates_predOf (bitsOf date0) _ hne, ofFn_bitsOf]
  rw [winWord, parse_unparse, evalGates_winGates]
  simp [accepts, valid, date0]

/-- A predicate true on `x` evaluates to `1` on the bits of `x`. -/
theorem circ_eval_of_true (x : Fin nA → Bool) (f : SLP (Fin nA) × Wire (Fin nA))
    (hfx : SLP.evalBool x f.1 f.2 = true) :
    ((Sdw (N := N) hk).circ f).eval (fun i => bitR (R := Rg N K) (x i)) = 1 := by
  have := Circuit.eval_bits (R := Rg N K) x (f.1.circuit f.2)
  rw [SLP.evalBool_circuit, hfx] at this
  simp only [bitR]
  exact this.trans (by simp)

/-- `f(0) = 1` in the ring for a window predicate. -/
theorem circ_eval_date0 (w : Window) :
    ((Sdw (N := N) hk).circ (predC (winWord w))).eval
      (fun i => bitR (R := Rg N K) (bitsOf date0 i)) = 1 :=
  circ_eval_of_true _ _ (evalBool_date0 w)

theorem bitR_date0 (i : Fin nA) : bitR (R := Rg N K) (bitsOf date0 i) = 0 := by
  rw [bitsOf_date0]; simp [bitR]

/-! ### The key row -/

theorem bitsOf_zero : bitsOf (Sdw (N := N) hk) (fun _ => (0 : Matrix (Fin 2) (Col k) (Rg N K))) = 0 := by
  funext j
  show (coeffBits N (2 ^ K) k hk.le (Fin 2) (Col k)).bits 0 j.2 = 0
  rw [coeffBits_isBoolean hk.le (Fin 2) 0 j.2]
  simp [coeffBool, bitR]

/-- **The key row as a row of the simulated trapdoor**: if row `r` of every `W_j` is `B_j` and row
`r` of every `Rᵢ` is zero, then with `Ψ = 0` and `x = (0, 0)`,
`B_f̂ = row_r (simKeyMat …) + f(0) G̲`. -/
theorem keyMatrix_eq_rowSim (mpk : PK hk c) (Rm : Fin nA → Matrix (Fin c.d) (Col k) (Rg N K))
    (W : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin c.d) (Col k) (Rg N K))
    (r : Fin c.d) (hW : ∀ j, rowAt (W j) r = mpk.Bj j) (hR : ∀ i, rowAt (Rm i) r = 0)
    (f : (Sdw (N := N) hk).Pred) :
    keyMatrix mpk f = rowAt (simKeyMat (S := Sdw (N := N) hk) Rm (bitsOf date0) W (fun _ => 0)
        mpk.Bj f) r +
      ((Sdw (N := N) hk).circ f).eval (fun i => bitR (R := Rg N K) (bitsOf date0 i)) •
        (Sdw (N := N) hk).Γ₁.G := by
  set A : Matrix (Fin 2) (Fin c.d) (Rg N K) := Matrix.of fun _ j => if j = r then 1 else 0
  have hrow : (Matrix.of fun _ c => A 0 c : Matrix (Fin 1) (Fin c.d) (Rg N K)) = unitRow r := by
    ext i j; simp [A, unitRow]
  have hΨ : ∀ i, (fun _ => (0 : Matrix (Fin 2) (Col k) (Rg N K))) i =
      A * Rm i + bitR (R := Rg N K) (bitsOf date0 i) • (Sdw (N := N) hk).Γ.G := by
    intro i
    rw [show bitR (R := Rg N K) (bitsOf date0 i) = 0 from bitR_date0 i, zero_smul, add_zero]
    ext a col
    have := congrArg (fun M : Matrix (Fin 1) (Col k) (Rg N K) => M 0 col) (hR i)
    simp only [rowAt, Matrix.of_apply, Matrix.zero_apply] at this
    simp [A, Matrix.mul_apply, this]
  have hB : ∀ j, (oldMPK mpk).Bj j = (Matrix.of fun _ c => A 0 c) * W j +
      bitsOf (Sdw (N := N) hk) (fun _ => 0) j • (Sdw (N := N) hk).Γ₁.G := by
    intro j
    rw [hrow, unitRow_mul, hW j, bitsOf_zero]
    simp [oldMPK]
  have h := keyMatrix_sim (ringSetting_fhatCorrect hk (Fin nA)) (oldMPK mpk) A Rm (bitsOf date0) W
    (fun _ => 0) hΨ hB f
  rw [hrow, unitRow_mul] at h
  exact h

/-! ### `c_f̂` -/

/-- **`c_f̂` as a row of the simulated trapdoor**: if row `r` of every `W_j` is `c_j` and rows `r'`,
`r` of every `Rᵢ` are the rows `0`, `1` of `Ψᵢ`, then with the ciphertext's `Ψ` and
`x = (0, 0)`, `c_f̂ = row_r (simKeyMat …) + f(0) · (row 1 of G)`. -/
theorem evalCiphertext_eq_rowSim (mpk : PK hk c) (ct : CT hk c)
    (Rm : Fin nA → Matrix (Fin c.d) (Col k) (Rg N K))
    (W : (Sdw (N := N) hk).Attr × (Sdw (N := N) hk).ctBits.Index → Matrix (Fin c.d) (Col k) (Rg N K))
    (r r' : Fin c.d) (hW : ∀ j, rowAt (W j) r = ct.cj j)
    (hR0 : ∀ i, rowAt (Rm i) r' = rowAt (ct.Ψ i) 0) (hR1 : ∀ i, rowAt (Rm i) r = rowAt (ct.Ψ i) 1)
    (f : (Sdw (N := N) hk).Pred) :
    evalCiphertext mpk f ct = rowAt (simKeyMat (S := Sdw (N := N) hk) Rm (bitsOf date0) W ct.Ψ
        mpk.Bj f) r +
      ((Sdw (N := N) hk).circ f).eval (fun i => bitR (R := Rg N K) (bitsOf date0 i)) •
        rowAt (Sdw (N := N) hk).Γ.G 1 := by
  set A : Matrix (Fin 2) (Fin c.d) (Rg N K) :=
    Matrix.of fun a j => if a = 0 then (if j = r' then 1 else 0) else (if j = r then 1 else 0)
  have hΨ : ∀ i, ct.Ψ i = A * Rm i + bitR (R := Rg N K) (bitsOf date0 i) • (Sdw (N := N) hk).Γ.G := by
    intro i
    rw [show bitR (R := Rg N K) (bitsOf date0 i) = 0 from bitR_date0 i, zero_smul, add_zero]
    ext a col
    fin_cases a
    · have := congrArg (fun M : Matrix (Fin 1) (Col k) (Rg N K) => M 0 col) (hR0 i)
      simp only [rowAt, Matrix.of_apply] at this
      simp [A, Matrix.mul_apply, this]
    · have := congrArg (fun M : Matrix (Fin 1) (Col k) (Rg N K) => M 0 col) (hR1 i)
      simp only [rowAt, Matrix.of_apply] at this
      simp [A, Matrix.mul_apply, this]
  have hsim := sim_relation (Sdw (N := N) hk).Γ A ct.Ψ (fun i => bitR (R := Rg N K) (bitsOf date0 i))
    Rm hΨ ((Sdw (N := N) hk).circ f)
  have hbot : botRow (evalMat (Sdw (N := N) hk).Γ ct.Ψ ((Sdw (N := N) hk).circ f)) =
      rowAt (evalSim (Sdw (N := N) hk).Γ ct.Ψ (fun i => bitR (R := Rg N K) (bitsOf date0 i)) Rm
        ((Sdw (N := N) hk).circ f)) r +
      ((Sdw (N := N) hk).circ f).eval (fun i => bitR (R := Rg N K) (bitsOf date0 i)) •
        rowAt (Sdw (N := N) hk).Γ.G 1 := by
    have e : botRow (evalMat (Sdw (N := N) hk).Γ ct.Ψ ((Sdw (N := N) hk).circ f)) =
        rowAt (evalMat (Sdw (N := N) hk).Γ ct.Ψ ((Sdw (N := N) hk).circ f)) 1 := by
      ext i col; rfl
    rw [e, hsim, rowAt_add, rowAt_smul, rowAt_mul]
    congr 1
    have : rowAt A 1 = unitRow r := by ext i j; simp [A, rowAt, unitRow]
    rw [this, unitRow_mul]
  unfold evalCiphertext simKeyMat
  rw [rowAt_add, rowAt_sum, hbot, ← add_assoc]
  congr 2
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rowAt_mul, rowAt_slpSim]
  congr 2
  funext j
  exact (hW j).symm

end AdvancedEncryption.DualUse
