import PE.Impl.ExpLUT.Prog.RedChalTail
open SigabaNeo.Tape.RingVM.Hash
/-!
# The law of the challenge component (package G2, `chalP`)

* **`chal_words`**: the words the code pushes are the canonical encoding `ctEnc` of the challenge
  `chalCT D σ μ = shiftCT ⌊q/2⌉ μ (redView (rawF σ)).2`;
* **`exec_chalC`**: the code ends with these words in `xOut`;
* **`law_chalP`**, **`wf_chalP`**: the component's law and well-formedness.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace AdvancedEncryption.ExpLUT.Prog.RedChal

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### The words of the challenge -/

/-- The words of `b`. -/
noncomputable def bWords (σ : RawSec D) : List (List Bool) :=
  (Enum.list (α := BCol (Wb D) D.K)).map fun c => encRM D.N D.K (σ.2.1.vB c + σ.2.2.1 c)

/-- The words of the helpers. -/
noncomputable def hWords (σ : RawSec D) : List (List Bool) :=
  ((Enum.list (α := Jh D)).map fun k => (Enum.list (α := Col D.K)).map fun c =>
    encRM D.N D.K (σ.2.1.vH k c - (setting D).G 1 c + σ.2.2.2.1 k c)).flatten

/-- The words of the bottom rows of `C^in`. -/
noncomputable def cbAll (σ : RawSec D) : List (List Bool) :=
  ((Enum.list (α := Pos)).map fun t =>
    cbWords (fun v => -σ.2.1.vB (.inl v)) (fun i => σ.2.2.2.2.2.2 (.inl (t, (0, i))))
      (fun i => σ.2.2.2.2.2.2 (.inl (t, (1, i)))) (fun i => σ.2.2.2.2.2.1.2.1 t (0, i))
      (fun i => σ.2.2.2.2.2.1.2.1 t (1, i)) (σ.1 t)).flatten

/-- **All the words of the challenge.** -/
noncomputable def allWords (σ : RawSec D) (μ : Bool) : List (List Bool) :=
  bWords σ ++ hWords σ ++ ((Enum.list (α := Fin D.b)).map (autWords σ)).flatten ++ cbAll σ ++
    cinWords σ ++ c0Words σ ++
      [encRM D.N D.K (σ.2.1.vd + σ.2.2.2.2.1 + half D * msgR D μ)]

theorem flatten_map_flatten {α : Type} (l : List α) (f : α → List (List Bool)) :
    (l.map f).flatten.flatten = (l.map fun a => (f a).flatten).flatten := by
  rw [List.flatten_flatten, List.map_map]; rfl

theorem enc_b (σ : RawSec D) (μ : Bool) :
    (vecE D (BCol (Wb D) D.K)).enc (chalCT D σ μ).b = (bWords σ).flatten :=
  vecE_enc_eq _

theorem enc_h (σ : RawSec D) (μ : Bool) :
    (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc (chalCT D σ μ).h = (hWords σ).flatten := by
  rw [hWords, flatten_map_flatten]
  refine (fun_enc_eq _ _).trans ?_
  congr 1
  exact List.map_congr_left fun k _ => vecE_enc_eq _

theorem enc_caut (σ : RawSec D) (μ : Bool) :
    (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
      (chalCT D σ μ).caut = ((Enum.list (α := Fin D.b)).map (autWords σ)).flatten.flatten := by
  rw [flatten_map_flatten, caut_split]
  congr 1
  exact List.map_congr_left fun t _ => (caut_words σ μ t).symm

theorem bb_sub (σ : RawSec D) :
    ((redPub σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1).Bb 1 - fun v =>
      (redCore σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1).1 (.inl v)) = fun v => -σ.2.1.vB (.inl v) := by
  funext v
  have gen : ∀ a b : Rg D, b - (a + b) = -a := fun a b => by abel
  exact gen _ _

theorem cinBot_apply (σ : RawSec D) (μ : Bool) (t : Pos) (c : Col D.K) :
    (chalCT D σ μ).cinBot t c = (fun v => -σ.2.1.vB (.inl v)) ⬝ᵥ bv (σ.2.2.2.2.2.2 (.inl (t, c))) +
      σ.2.2.2.2.2.1.2.1 t c + (setting D).E.X ^ (wSt * (σ.1 t).val) * (setting D).G 1 c := by
  show ((redPub σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1).Bb 1 - (fun v =>
      (redCore σ.2.1 σ.2.2.1 σ.2.2.2.1 σ.2.2.2.2.1).1 (.inl v))) ⬝ᵥ bv (σ.2.2.2.2.2.2 (.inl (t, c))) +
      σ.2.2.2.2.2.1.2.1 t c + (setting D).E.X ^ (wSt * attrN σ.1 t) * (setting D).G 1 c = _
  rw [bb_sub]
  rfl

theorem enc_cb (σ : RawSec D) (μ : Bool) :
    (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc (chalCT D σ μ).cinBot = (cbAll σ).flatten := by
  rw [cbAll, flatten_map_flatten]
  refine (fun_enc_eq _ _).trans ?_
  congr 1
  refine List.map_congr_left fun t _ => ?_
  refine (vecE_enc_eq _).trans ?_
  rw [cbWords]
  refine congrArg List.flatten ?_
  refine (enum_col_map (fun c => encRM D.N D.K ((chalCT D σ μ).cinBot t c))).trans ?_
  congr 1
  · refine List.map_congr_left fun i _ => ?_
    rw [cinBot_apply]
    erw [G1_zero]
    simp
  · refine List.map_congr_left fun i _ => ?_
    rw [cinBot_apply]
    erw [G1_one]
    have gen : ∀ A B P Q : Rg D, A + B + P * Q = A + Q * P + B := fun A B P Q => by ring
    exact congrArg _ (gen _ _ _ _)

/-- **The words of the challenge are its encoding.** -/
theorem chal_words (σ : RawSec D) (μ : Bool) :
    (allWords σ μ).flatten = (ctEnc D).enc (chalCT D σ μ) := by
  have e : (ctEnc D).enc (chalCT D σ μ) =
      (vecE D (BCol (Wb D) D.K)).enc (chalCT D σ μ).b ++
      ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc (chalCT D σ μ).h ++
      ((FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
        (chalCT D σ μ).caut ++
      ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc (chalCT D σ μ).cinBot ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
        (chalCT D σ μ).cin ++
      ((vecE D (Col D.K)).enc (chalCT D σ μ).c0 ++ (rEnc D).enc (chalCT D σ μ).cm))))) := rfl
  rw [e, enc_b, enc_h, enc_caut, enc_cb]
  simp only [allWords, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]
  exact congrArg _ (congrArg _ (congrArg _ (congrArg _ (congrArg₂ (· ++ ·) (cin_words σ μ)
    (congrArg₂ (· ++ ·) (c0_words σ μ) rfl)))))

/-! ### The registers at the start -/

theorem tm_rho (j : ℕ) (hj : j < 8) : tm D (rhoR j) = 2 * D.N - wtR j := by
  rw [rhoR_val hj, tm, if_neg (by simp; omega), if_pos (by simp; omega)]
  simp

theorem tm_kR (t : ℕ) (ht : t < 32) : tm D (kR t) = κD D t := by
  rw [kR_val ht, tm, if_pos (by simp; omega)]
  simp

/-- The registers at the start of the code. -/
noncomputable def w0 (σ : RawSec D) (μ : Bool) : St :=
  SigabaNeo.Tape.RingVM.Handler.initW1 ra rb r1 (tm D) ((rawEnc D).enc σ) [μ]

theorem w0_tmpl (σ : RawSec D) (μ : Bool) (r : Fin 200) (h0 : r ≠ ra) (h1 : r ≠ rb)
    (h2 : r ≠ r1) : w0 σ μ r = List.replicate (tm D r) false := by
  simp [w0, SigabaNeo.Tape.RingVM.Handler.initW1, SigabaNeo.Tape.RingVM.Handler.initW, Function.update_apply, h0, h1, h2]

theorem w0_ra (σ : RawSec D) (μ : Bool) : w0 σ μ ra = (rawEnc D).enc σ := by
  simp [w0, SigabaNeo.Tape.RingVM.Handler.initW1, SigabaNeo.Tape.RingVM.Handler.initW, Function.update_apply]

theorem w0_rb (σ : RawSec D) (μ : Bool) : w0 σ μ rb = [μ] := by
  simp [w0, SigabaNeo.Tape.RingVM.Handler.initW1, SigabaNeo.Tape.RingVM.Handler.initW, Function.update_apply]

theorem w0_r1 (σ : RawSec D) (μ : Bool) :
    w0 σ μ r1 = true :: List.replicate (D.N * D.K - 1) false := by
  simp [w0, SigabaNeo.Tape.RingVM.Handler.initW1, Function.update_apply]
  rfl

theorem kR_notin (L : List (Fin 200)) (hL : ∀ j ∈ L, j.val < 48 ∨ 80 ≤ j.val) (t : ℕ) :
    kR t ∉ L := fun h => by
  have := hL _ h; simp [kR] at this; omega

theorem rhoR_notin (L : List (Fin 200)) (hL : ∀ j ∈ L, j.val < 37 ∨ 45 ≤ j.val) {j : ℕ}
    (hj : j < 8) : rhoR j ∉ L := fun h => by
  have := hL _ h; rw [rhoR_val hj] at this; simp at this; omega

/-! ### The run -/

set_option maxRecDepth 20000 in
/-- **The code ends with the words of the challenge in `xOut`.** -/
theorem exec_chalC_words (hb : 1 ≤ D.b) (hb32 : D.b ≤ 32) (hN : wSt * 2 ^ 7 ≤ 2 * D.N)
    (σ : RawSec D) (μ : Bool) :
    exec D.N D.K (chalC D) (w0 σ μ) xOut =
      bufW (D.N * D.K) (List.replicate (ctEnc D).len false) ([] ++ allWords σ μ) := by
  have hKp := D.K_pos
  have hNp := D.N_pos
  set W := w0 σ μ with hWdef
  have T : ∀ r, r ≠ ra → r ≠ rb → r ≠ r1 → W r = List.replicate (tm D r) false :=
    w0_tmpl σ μ
  have L : ∀ r, r ≠ ra → r ≠ rb → r ≠ r1 → (W r).length = tm D r := fun r h0 h1 h2 => by
    rw [T r h0 h1 h2, List.length_replicate]
  have hone : W r1 = true :: List.replicate (D.N * D.K - 1) false := w0_r1 σ μ
  have h1l : (W r1).length = D.N * D.K := by
    rw [hone]; simp; have : 0 < D.N * D.K := Nat.mul_pos hNp hKp; omega
  have h1v : decRM D.N D.K (W r1) = 1 := by rw [hone]; exact decRM_one hKp hNp
  simp only [chalC, exec_ofList_cons, exec_ofList_nil]
  -- the parse
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, pF⟩ := exec_parseC σ W (w0_ra σ μ)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [L _ (by decide) (by decide) (by decide)]; rfl)
  set w1 := exec D.N D.K parseC W with hw1
  -- `b`
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, bF⟩ := exec_bC σ w1 (List.replicate (ctEnc D).len false) []
    (fun _ h => absurd h List.not_mem_nil) p2 p3
    (by rw [pF _ (by decide), T _ (by decide) (by decide) (by decide), bufW_nil]; rfl)
    (by rw [pF _ (by decide), T _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [pF _ (by decide), T _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [pF _ (by decide), T _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [pF _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [pF _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [pF _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [pF _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [pF _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [pF _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
  set w2 := exec D.N D.K bC w1 with hw2
  have F2 : ∀ r, r ∉ parseW ++ bW → w2 r = W r := fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [bF r hr.2, pF r hr.1]
  -- the helpers
  obtain ⟨h1, h2, h3, hF⟩ := exec_hC hb σ w2 (List.replicate (ctEnc D).len false) ([] ++ bWords σ)
    (fun y hy => by simp at hy; exact mem_words hy) b4
    (by rw [bF _ (by decide), p4, h2W_eq]) b1
    (by rw [F2 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F2 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F2 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F2 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F2 _ (by decide), h1l]) (by rw [F2 _ (by decide), h1v])
    (by rw [F2 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl) b6 b7
  set w3 := exec D.N D.K hC w2 with hw3
  have F3 : ∀ r, r ∉ parseW ++ bW ++ hW → w3 r = W r := fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [hF r hr.2, F2 r hr.1]
  have hys2 : ∀ y ∈ [] ++ bWords σ ++ ((List.range (D.b * 2)).map
      (hout ((vsV σ.2.1).drop (D.mb + D.K + 1)) D.K (D.b * 2) (D.K * (D.b * 2)) 0
        (F0 σ) (F1 σ))).flatten, y.length = D.N * D.K := by
    rw [hout_eq]
    intro y hy
    simp only [List.nil_append, List.mem_append] at hy
    rcases hy with hy | hy
    · exact mem_words hy
    · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp hy
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hl
      exact mem_words hyl
  -- `c^aut`
  obtain ⟨a1, a2, a3, a4, a5, aF⟩ := exec_autC σ w3
    ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc σ.2.2.2.2.2.1.2.1 ++
      ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
        σ.2.2.2.2.2.1.2.2.1 ++ (vecE D (Col D.K)).enc σ.2.2.2.2.2.1.2.2.2))
    (List.replicate (ctEnc D).len false) _ hys2
    (by rw [F3 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (fun t ht => by
      rw [F3 _ (kR_notin _ (by decide) t), T _ (kR_notin [ra] (by decide) t ∘ fun h => by simp [h])
        (kR_notin [rb] (by decide) t ∘ fun h => by simp [h])
        (kR_notin [r1] (by decide) t ∘ fun h => by simp [h]), tm_kR t (by omega)])
    (by rw [hF _ (by decide), b2])
    (by rw [hF _ (by decide), bF _ (by decide), p10])
    (by rw [hF _ (by decide), bF _ (by decide), p6, flW, floodEnc_split])
    h1
    (by rw [F3 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F3 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F3 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F3 _ (by decide), T _ (by decide) (by decide) (by decide)]; rfl)
    h2 (by rw [F3 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl) h3
  set w4 := exec D.N D.K (autC D) w3 with hw4
  have F4 : ∀ r, r ∉ parseW ++ bW ++ hW ++ (xV :: xZ :: phW) → w4 r = W r := fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [aF r hr.2, F3 r hr.1]
  -- the bottom rows of `C^in`
  have hys3 : ∀ y ∈ [] ++ bWords σ ++ ((List.range (D.b * 2)).map
      (hout ((vsV σ.2.1).drop (D.mb + D.K + 1)) D.K (D.b * 2) (D.K * (D.b * 2)) 0
        (F0 σ) (F1 σ))).flatten ++ ((Enum.list (α := Fin D.b)).map (autWords σ)).flatten,
      y.length = D.N * D.K := by
    intro y hy
    rcases List.mem_append.mp hy with h' | h'
    · exact hys2 y h'
    · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp h'
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
      exact mem_autWords (t := a) y hyl
  obtain ⟨c1, c2, c3, c4, c5, cF⟩ := exec_cbC hN σ w4
    ((FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc
        σ.2.2.2.2.2.1.2.2.1 ++ (vecE D (Col D.K)).enc σ.2.2.2.2.2.1.2.2.2)
    (List.replicate (ctEnc D).len false) _ hys3
    (by rw [aF _ (by decide), hF _ (by decide), b3])
    (by rw [aF _ (by decide), hF _ (by decide), bF _ (by decide), p7])
    (by rw [aF _ (by decide), hF _ (by decide), bF _ (by decide), p1])
    a2
    (by rw [F4 _ (by decide), h1l]) (by rw [F4 _ (by decide), h1v]) a1
    (by rw [F4 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (fun j hj => by
      have hne : ∀ r : Fin 200, r ∈ [ra, rb, r1] → rhoR j ≠ r := fun r hr h =>
        rhoR_notin [ra, rb, r1] (by decide) hj (h ▸ hr)
      rw [F4 _ (rhoR_notin _ (by decide) hj), L _ (hne _ (by simp)) (hne _ (by simp))
        (hne _ (by simp)), tm_rho j hj])
    (by rw [F4 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F4 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F4 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F4 _ (by decide), T _ (by decide) (by decide) (by decide)]; rfl)
    a3 a4 a5
    (by rw [F4 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
  set w5 := exec D.N D.K cbC w4 with hw5
  have F5 : ∀ r, r ∉ parseW ++ bW ++ hW ++ (xV :: xZ :: phW) ++ (xV :: xZ :: cbW) →
      w5 r = W r := fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [cF r hr.2, F4 r hr.1]
  have hys4 : ∀ y ∈ [] ++ bWords σ ++ ((List.range (D.b * 2)).map
      (hout ((vsV σ.2.1).drop (D.mb + D.K + 1)) D.K (D.b * 2) (D.K * (D.b * 2)) 0
        (F0 σ) (F1 σ))).flatten ++ ((Enum.list (α := Fin D.b)).map (autWords σ)).flatten ++
        cbAll σ, y.length = D.N * D.K := by
    intro y hy
    rcases List.mem_append.mp hy with h' | h'
    · exact hys3 y h'
    · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp h'
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
      exact mem_cbWords y hyl
  -- `c^in` and `c₀`
  obtain ⟨i1, iF⟩ := exec_cinC σ w5 (List.replicate (ctEnc D).len false) _ hys4
    (by rw [cF _ (by decide), aF _ (by decide), hF _ (by decide), b2])
    (by rw [cF _ (by decide), aF _ (by decide), hF _ (by decide), bF _ (by decide), p9])
    (by rw [cF _ (by decide), aF _ (by decide), hF _ (by decide), bF _ (by decide), p8])
    (by rw [F5 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F5 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    c2 c1
    (by rw [F5 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F5 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F5 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F5 _ (by decide), T _ (by decide) (by decide) (by decide)]; rfl)
    c3 c4 c5
  set w6 := exec D.N D.K cinC w5 with hw6
  have F6 : ∀ r, r ∉ parseW ++ bW ++ hW ++ (xV :: xZ :: phW) ++ (xV :: xZ :: cbW) ++
      (xV :: xZ :: phW) → w6 r = W r := fun r hr => by
    rw [List.mem_append, not_or] at hr; rw [iF r hr.2, F5 r hr.1]
  have hys5 : ∀ y ∈ [] ++ bWords σ ++ ((List.range (D.b * 2)).map
      (hout ((vsV σ.2.1).drop (D.mb + D.K + 1)) D.K (D.b * 2) (D.K * (D.b * 2)) 0
        (F0 σ) (F1 σ))).flatten ++ ((Enum.list (α := Fin D.b)).map (autWords σ)).flatten ++
        cbAll σ ++ cinWords σ ++ c0Words σ, y.length = D.N * D.K := by
    intro y hy
    rcases List.mem_append.mp hy with h' | h'
    · rcases List.mem_append.mp h' with h'' | h''
      · exact hys4 y h''
      · exact mem_words h''
    · exact mem_words h'
  -- `c_m`
  rw [exec_cmC w6 σ.2.1.vd σ.2.2.2.2.1 μ (List.replicate (ctEnc D).len false) _ hys5
    (by rw [iF _ (by decide), cF _ (by decide), aF _ (by decide), hF _ (by decide), b5])
    (by rw [iF _ (by decide), cF _ (by decide), aF _ (by decide), hF _ (by decide),
      bF _ (by decide), p5])
    (by rw [F6 _ (by decide), h1l]) (by rw [F6 _ (by decide), h1v])
    (by rw [F6 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)
    (by rw [F6 _ (by decide)]; exact w0_rb σ μ) i1
    (by rw [F6 _ (by decide), L _ (by decide) (by decide) (by decide)]; rfl)]
  rw [hout_eq]
  simp only [allWords, hWords, List.nil_append, List.append_assoc]

/-! ### The law of the component -/

theorem mem_allWords (σ : RawSec D) (μ : Bool) :
    ∀ y ∈ allWords σ μ, y.length = D.N * D.K := by
  intro y hy
  simp only [allWords, List.mem_append, List.mem_singleton] at hy
  rcases hy with (((((h | h) | h) | h) | h) | h) | h
  · exact mem_words h
  · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp h
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hl
    exact mem_words hyl
  · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp h
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
    exact mem_autWords (t := a) y hyl
  · obtain ⟨l, hl, hyl⟩ := List.mem_flatten.mp h
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
    exact mem_cbWords y hyl
  · exact mem_words h
  · exact mem_words h
  · rw [h]; exact length_encRM _ _ _

/-- **The code computes the encoding of the challenge.** -/
theorem exec_chalC (hb : 1 ≤ D.b) (hb32 : D.b ≤ 32) (hN : wSt * 2 ^ 7 ≤ 2 * D.N)
    (σ : RawSec D) (μ : Bool) :
    exec D.N D.K (chalC D) (w0 σ μ) xOut = (ctEnc D).enc (chalCT D σ μ) := by
  rw [exec_chalC_words hb hb32 hN, List.nil_append, bufW_full (mem_allWords σ μ), chal_words]
  rw [List.length_replicate, ← length_flatten_of (mem_allWords σ μ), chal_words]
  exact (length_enc _ _).symm

/-- **The law of the challenge component.** -/
theorem law_chalP (hb : 1 ≤ D.b) (hb32 : D.b ≤ 32) (hN : wSt * 2 ^ 7 ≤ 2 * D.N)
    (σ : RawSec D) (μ : Bool) :
    XProg.law (chalP D) (io2 (R := 245) ((rawEnc D).enc σ) [μ] []) =
      PMF.pure (io2 (R := 245) ((ctEnc D).enc (chalCT D σ μ)) [] []) := by
  rw [chalP, SigabaNeo.Tape.RingVM.Handler.law_ringIO1 D.N_pos D.K_pos (by decide) xOut r1 (by decide) (by decide)]
  rw [show SigabaNeo.Tape.RingVM.Handler.initW1 ra rb r1 (tm D) ((rawEnc D).enc σ) [μ] = w0 σ μ from rfl,
    exec_chalC hb hb32 hN σ μ]

/-- **The challenge component is well formed.** -/
theorem wf_chalP : (chalP D).WF :=
  SigabaNeo.Tape.RingVM.Handler.wf_ringIO1 _ _ _ _ _ _ _ _ (loopOkB_chalC D)

open AdvancedEncryption.PE.Generic in
/-- **The `law_chal` field of `Generic.Comps`** for the reduction's challenger `spS` (any
`Ok`). -/
theorem law_chal_spS (hb : 1 ≤ D.b) (hb32 : D.b ≤ 32) (hN : wSt * 2 ^ 7 ≤ 2 * D.N)
    (kb : KeyBoxes D) (L : ℕ) (impl : Impl sig) (χfl : PMF (Rg D)) (i₀ : CInst D)
    (σ : RawSec D) (μ : Bool) :
    XProg.law (chalP D) (io2 (R := 245) ((w8Codes (rawEnc D)).sig.enc σ) ((univ w8).encMsg μ) []) =
      ((spS D kb L (rawF D) (rawSetup D χfl) impl χfl i₀).chal σ μ).map
        fun ct => io2 (R := 245) ct [] [] := by
  have e : (spS D kb L (rawF D) (rawSetup D χfl) impl χfl i₀).chal σ μ =
      PMF.pure ((ctEnc D).enc (chalCT D σ μ)) := rfl
  rw [e, PMF.pure_map]
  exact law_chalP hb hb32 hN σ μ

/-- The hypotheses at the concrete dimensions. -/
theorem Dc_hyps : 1 ≤ Dc.b ∧ Dc.b ≤ 32 ∧ wSt * 2 ^ 7 ≤ 2 * Dc.N := by
  refine ⟨by decide, by decide, ?_⟩
  show 2 ^ 14 * 2 ^ 7 ≤ 2 * 2 ^ 24
  norm_num

end AdvancedEncryption.ExpLUT.Prog.RedChal
