import SigabaNeoStd.Lattices.ProgAlgo.Mersenne.VMBuf
import PE.Impl.ExpLUT.Prog.RedPubPMath
open SigabaNeo.Tape.RingVM.Hash
/-!
# A gadget row of hashes (package G2, `pubP`)

Every hashed matrix row of the public key has the shape
`c ↦ ψ (f ⬝ᵥ bv (g c)) + u · G_{ρ c} + e c` over `c ∈ Col` (`a_t`, `cb_t`, `A₀`, `A^in`, `A^aut`).
`rowC m ρ` computes it with two hash phases (`SigabaNeo.Tape.RingVM.Hash.hashPhase`) of `K` rounds each, one per half
`Col = {0, 1} × Fin K`: the post-map `m` (`xH := ψ xAcc`), and on the half `ρ` the gadget post
`gpost m`, which also adds the scratch word `xP` and doubles it (`2^i u` in round `i`).

* `phashV`: the hash of enumerated words is `f ⬝ᵥ bv z`;
* **`exec_halfC`**: one half;
* **`exec_rowC`**: the row, into the phase buffer `xOut` (pre-sized to `|Col|` words).
-/

set_option linter.unusedSectionVars false

namespace AdvancedEncryption.ExpLUT.Prog.RedPubP

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices
  SigabaNeo.Lattices.Algo Matrix AdvancedEncryption.PE AdvancedEncryption.PE.BranchingProgram
open SigabaNeo.Tape.RingVM.Hash

variable {D : Dims}

/-! ### Hashes of enumerated words -/

theorem psum_map_enum {α M : Type} [Enum α] [Fintype α] [AddCommMonoid M] (g : α → M) :
    ((Enum.list (α := α)).map g).sum = ∑ a, g a := by
  classical
  rw [← List.sum_toFinset g Enum.nodup]
  congr 1
  ext a; simp [Enum.complete a]

/-- **The hash of enumerated words is the binary hash.** -/
theorem phashV (vs : Wb D → List Bool) (f : Wb D → Rg D) (hf : ∀ v, decRM D.N D.K (vs v) = f v)
    (z : Wb D → Bool) :
    SigabaNeo.Tape.RingVM.Hash.hashV (N := D.N) (K := D.K) ((Enum.list (α := Wb D)).map vs)
        ((Enum.list (α := Wb D)).map z) = f ⬝ᵥ bv z := by
  rw [SigabaNeo.Tape.RingVM.Hash.hashV, List.zipWith_map, List.zipWith_self, psum_map_enum]
  simp only [dotProduct, bv, bitVal, hf]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp_all

theorem map_range_finRange {β : Type} (n : ℕ) (h : ℕ → β) :
    (List.range n).map h = (List.finRange n).map fun i : Fin n => h i.val := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp

theorem getD_map_finRange {β : Type} {n : ℕ} (F : Fin n → β) (d : β) (i : Fin n) :
    ((List.finRange n).map F).getD i d = F i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-! ### The code -/

/-- The counter template of a half row (`K` rounds). -/
@[simp] abbrev cK : Fin 200 := 9

/-- **The gadget post**: `m`, then `xH += xP`, `xP := 2 xP`. -/
def gpost (m : Code) : Code := .seq m (.seq (.add xH xH xP) (.add xP xP xP))

/-- A half row: `K` rounds of the hash phase with the post-map `p`. -/
def halfC (p : Code) : Code := .seq (.cp xCnt cK) (hashPhase p)

/-- **A gadget row**: the gadget post on the half `ρ`. -/
def rowC (m : Code) (ρ : Fin 2) : Code :=
  if ρ = 0 then .seq (halfC (gpost m)) (halfC m) else .seq (halfC m) (halfC (gpost m))

theorem wr_gpost (m : Code) (hwm : ∀ j ∈ wr m, j = xH) : ∀ j ∈ wr (gpost m), j = xH ∨ j = xP := by
  intro j hj
  simp only [gpost, wr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with h | h | h
  · exact Or.inl (hwm j h)
  · exact Or.inl h
  · exact Or.inr h

/-! ### A half row -/

/-- **A half row**: the words `ψ (f ⬝ᵥ bv (g i)) + [γ] 2^i u + e i`, `i < K`. -/
theorem exec_halfC (γ : Bool) (m : Code) (ψ : Rg D → Rg D) (hwm : ∀ j ∈ wr m, j = xH) (w : St)
    (hm : ∀ w' : St, (w' xAcc).length = D.N * D.K → (∀ j, j ∉ phW → w' j = w j) →
      (exec D.N D.K m w' xH).length = D.N * D.K ∧
        decRM D.N D.K (exec D.N D.K m w' xH) = ψ (decRM D.N D.K (w' xAcc)))
    (f : Wb D → Rg D) (vs : Wb D → List Bool) (hvs : ∀ v, (vs v).length = D.N * D.K)
    (hvf : ∀ v, decRM D.N D.K (vs v) = f v)
    (g : Fin D.K → Wb D → Bool) (e : Fin D.K → Rg D) (es : Fin D.K → List Bool)
    (hes : ∀ i, (es i).length = D.N * D.K) (hef : ∀ i, decRM D.N D.K (es i) = e i)
    (u : Rg D) (rest restF b₀ : List Bool) (ys₀ : List (List Bool))
    (hys₀ : ∀ y ∈ ys₀, y.length = D.N * D.K)
    (hV : w xV = ((Enum.list (α := Wb D)).map vs).flatten)
    (hZ : w xZ = ((List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g i)).flatten ++ rest)
    (hF : w xF = ((List.finRange D.K).map es).flatten ++ restF)
    (hOut : w xOut = bufW (D.N * D.K) b₀ ys₀)
    (hPl : (w xP).length = D.N * D.K) (hPv : decRM D.N D.K (w xP) = u)
    (hcK : (w cK).length = D.K)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    exec D.N D.K (halfC (if γ then gpost m else m)) w xOut = bufW (D.N * D.K) b₀ (ys₀ ++
        (List.finRange D.K).map fun i => encRM D.N D.K (ψ (f ⬝ᵥ bv (g i)) +
          (if γ then (2 : ZMod (2 ^ D.K - 1)) ^ (i : ℕ) • u else 0) + e i)) ∧
      exec D.N D.K (halfC (if γ then gpost m else m)) w xZ = rest ∧
      exec D.N D.K (halfC (if γ then gpost m else m)) w xF = restF ∧
      (exec D.N D.K (halfC (if γ then gpost m else m)) w xv).length = D.N * D.K ∧
      (exec D.N D.K (halfC (if γ then gpost m else m)) w xBit).length = 1 ∧
      (exec D.N D.K (halfC (if γ then gpost m else m)) w xf).length = D.N * D.K ∧
      (γ = false → exec D.N D.K (halfC (if γ then gpost m else m)) w xP = w xP) ∧
      (exec D.N D.K (halfC (if γ then gpost m else m)) w xP).length = D.N * D.K ∧
      ∀ j, j ∉ phW → exec D.N D.K (halfC (if γ then gpost m else m)) w j = w j := by
  set post := if γ then gpost m else m with hpostDef
  set w0 := Function.update w xCnt (w cK) with hw0
  have hw0f : ∀ j, j ≠ xCnt → w0 j = w j := fun j hj => Function.update_of_ne hj _ _
  have hex : exec D.N D.K (halfC post) w = exec D.N D.K (hashPhase post) w0 := rfl
  have hnp : ∀ j, j ∉ phW → j ≠ xCnt := fun j hj h => hj (by rw [h]; decide)
  let φ : ℕ → Rg D → Rg D := fun i x => ψ x + (if γ then (2 : ZMod (2 ^ D.K - 1)) ^ i • u else 0)
  let Q : ℕ → List Bool → Prop := fun i p => p.length = D.N * D.K ∧
    decRM D.N D.K p = (if γ then (2 : ZMod (2 ^ D.K - 1)) ^ i • u else u) ∧ (γ = false → p = w xP)
  have hwp : ∀ j ∈ wr post, j = xH ∨ j = xP := by
    intro j hj
    rw [hpostDef] at hj
    split_ifs at hj
    · exact wr_gpost m hwm j hj
    · exact Or.inl (hwm j hj)
  have hmP : ∀ w' : St, exec D.N D.K m w' xP = w' xP := fun w' =>
    exec_not_mem m w' xP fun h => absurd (hwm xP h) (by decide)
  have hpost : ∀ i, ∀ w' : St, (w' xAcc).length = D.N * D.K → (∀ j, j ∉ phW → w' j = w0 j) →
      Q i (w' xP) → (exec D.N D.K post w' xH).length = D.N * D.K ∧
        decRM D.N D.K (exec D.N D.K post w' xH) = φ i (decRM D.N D.K (w' xAcc)) ∧
        Q (i + 1) (exec D.N D.K post w' xP) := by
    intro i w' hA hfr hQ
    have hfr' : ∀ j, j ∉ phW → w' j = w j := fun j hj => by rw [hfr j hj, hw0f j (hnp j hj)]
    obtain ⟨hm1, hm2⟩ := hm w' hA hfr'
    obtain ⟨hQ1, hQ2, hQ3⟩ := hQ
    cases γ with
    | false =>
      simp only [hpostDef, Bool.false_eq_true, if_false]
      refine ⟨hm1, by rw [hm2]; simp [φ], ?_⟩
      rw [hmP]
      exact ⟨hQ1, by simpa using hQ2, hQ3⟩
    | true =>
      simp only [hpostDef, if_true]
      set w1 := exec D.N D.K m w' with hw1
      have h1P : w1 xP = w' xP := hmP w'
      have ex : exec D.N D.K (gpost m) w' = Function.update (Function.update w1 xH
          (addRMW D.N D.K (w1 xH) (w' xP))) xP (addRMW D.N D.K (w' xP) (w' xP)) := by
        show exec D.N D.K (.add xP xP xP) (exec D.N D.K (.add xH xH xP) w1) = _
        simp only [exec, Function.update_self, h1P, opd_eq hm1, opd_eq hQ1,
          Function.update_of_ne (show xP ≠ xH by decide)]
      rw [ex]
      refine ⟨?_, ?_, ?_⟩
      · rw [Function.update_of_ne (show xH ≠ xP by decide), Function.update_self,
          length_addRMW _ _ hm1]
      · rw [Function.update_of_ne (show xH ≠ xP by decide), Function.update_self,
          decRM_addRMW hm1 hQ1, hm2, hQ2]
        simp [φ]
      · rw [Function.update_self]
        refine ⟨length_addRMW _ _ hQ1 _, ?_, fun h => absurd h (by decide)⟩
        rw [decRM_addRMW hQ1 hQ1, hQ2]
        simp only [if_true]
        rw [pow_succ, mul_comm, mul_smul, two_smul]
  have hQ0 : Q 0 (w0 xP) := by
    rw [hw0f _ (by decide)]
    refine ⟨hPl, ?_, fun _ => rfl⟩
    split_ifs <;> simp [hPv]
  set zss := (List.finRange D.K).map fun i => (Enum.list (α := Wb D)).map (g i)
  set fs := (List.finRange D.K).map es
  have hlz : zss.length = D.K := by simp [zss]
  have hvs' : ∀ v ∈ (Enum.list (α := Wb D)).map vs, v.length = D.N * D.K := by
    intro v hv; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hv; exact hvs a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := exec_hashPhase (N := D.N) (K := D.K) D.K_pos post φ Q
    hwp w0 hpost hQ0 ((Enum.list (α := Wb D)).map vs) zss rest fs restF b₀ ys₀ hvs'
    (fun z hz => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz; simp)
    (fun z hz => by obtain ⟨i, -, rfl⟩ := List.mem_map.mp hz; exact hes i) hys₀
    (by rw [hlz, hw0, Function.update_self, hcK]) (by simp [fs, zss])
    (by rw [hw0f _ (by decide), hV]) (by rw [hw0f _ (by decide), hZ])
    (by rw [hw0f _ (by decide), hF]) (by rw [hw0f _ (by decide), hOut])
    (by rw [hw0f _ (by decide), hCm, List.length_map]) (by rw [hw0f _ (by decide), hC1])
    (by rw [hw0f _ (by decide), hCNK]) (by rw [hw0f _ (by decide), hZero])
    (by rw [hw0f _ (by decide), hv]) (by rw [hw0f _ (by decide), hb])
    (by rw [hw0f _ (by decide), hf])
  rw [hex]
  refine ⟨?_, h3, h4, h5, h6, h7, fun hγ => (h2.2.2 hγ), h2.1, fun j hj => by
    rw [h8 j hj, hw0f j (hnp j hj)]⟩
  rw [h1, hlz, map_range_finRange]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  simp only [zss, fs, getD_map_finRange, φ, phashV vs f hvf, hef]

/-! ### A row -/

theorem finRange_two : List.finRange 2 = [0, 1] := rfl

/-- The values on `Col` along `Enum`: the half `0`, then the half `1`. -/
theorem map_col {β : Type} (F : Col D.K → β) :
    (Enum.list (α := Col D.K)).map F =
      (List.finRange D.K).map (fun i => F (0, i)) ++ (List.finRange D.K).map (fun i => F (1, i)) := by
  rw [show (Enum.list (α := Col D.K)) = (List.finRange 2).product (List.finRange D.K) from rfl,
    map_product, finRange_two]
  simp

/-- **A gadget row of hashes**: the words `ψ (f ⬝ᵥ bv (g c)) + u G_{ρ c} + e c`, `c ∈ Col`, in
the phase buffer `xOut` (pre-sized to `|Col|` words). -/
theorem exec_rowC (ρ : Fin 2) (m : Code) (ψ : Rg D → Rg D) (hwm : ∀ j ∈ wr m, j = xH) (w : St)
    (hm : ∀ w' : St, (w' xAcc).length = D.N * D.K → (∀ j, j ∉ phW → w' j = w j) →
      (exec D.N D.K m w' xH).length = D.N * D.K ∧
        decRM D.N D.K (exec D.N D.K m w' xH) = ψ (decRM D.N D.K (w' xAcc)))
    (f : Wb D → Rg D) (vs : Wb D → List Bool) (hvs : ∀ v, (vs v).length = D.N * D.K)
    (hvf : ∀ v, decRM D.N D.K (vs v) = f v)
    (g : Col D.K → Wb D → Bool) (e : Col D.K → Rg D) (es : Col D.K → List Bool)
    (hes : ∀ c, (es c).length = D.N * D.K) (hef : ∀ c, decRM D.N D.K (es c) = e c)
    (u : Rg D) (rest restF : List Bool)
    (hV : w xV = ((Enum.list (α := Wb D)).map vs).flatten)
    (hZ : w xZ = ((Enum.list (α := Col D.K)).map fun c => (Enum.list (α := Wb D)).map (g c)).flatten ++
      rest)
    (hF : w xF = ((Enum.list (α := Col D.K)).map es).flatten ++ restF)
    (hOut : (w xOut).length = 2 * D.K * (D.N * D.K))
    (hPl : (w xP).length = D.N * D.K) (hPv : decRM D.N D.K (w xP) = u)
    (hcK : (w cK).length = D.K)
    (hCm : (w xCm).length = (Enum.list (α := Wb D)).length) (hC1 : (w xC1).length = 1)
    (hCNK : (w xCNK).length = D.N * D.K) (hZero : w xZero = List.replicate (D.N * D.K) false)
    (hv : (w xv).length = D.N * D.K) (hb : (w xBit).length = 1) (hf : (w xf).length = D.N * D.K) :
    exec D.N D.K (rowC m ρ) w xOut = ((Enum.list (α := Col D.K)).map fun c =>
        encRM D.N D.K (ψ (f ⬝ᵥ bv (g c)) + u * (setting D).G ρ c + e c)).flatten ∧
      exec D.N D.K (rowC m ρ) w xZ = rest ∧ exec D.N D.K (rowC m ρ) w xF = restF ∧
      (exec D.N D.K (rowC m ρ) w xv).length = D.N * D.K ∧
      (exec D.N D.K (rowC m ρ) w xBit).length = 1 ∧
      (exec D.N D.K (rowC m ρ) w xf).length = D.N * D.K ∧
      ∀ j, j ∉ phW → exec D.N D.K (rowC m ρ) w j = w j := by
  have hZ' := hZ
  have hF' := hF
  rw [map_col, List.flatten_append, List.append_assoc] at hZ'
  rw [map_col, List.flatten_append, List.append_assoc] at hF'
  have hO0 : w xOut = bufW (D.N * D.K) (w xOut) [] := (bufW_nil _ _).symm
  have hmw : ∀ w1 : St, (∀ j, j ∉ phW → w1 j = w j) → ∀ w' : St,
      (w' xAcc).length = D.N * D.K → (∀ j, j ∉ phW → w' j = w1 j) →
      (exec D.N D.K m w' xH).length = D.N * D.K ∧
        decRM D.N D.K (exec D.N D.K m w' xH) = ψ (decRM D.N D.K (w' xAcc)) :=
    fun w1 h1 w' hA hfr => hm w' hA fun j hj => by rw [hfr j hj, h1 j hj]
  have hword : ∀ (γ : Bool) (ρ' : Fin 2), (γ = true ↔ ρ = ρ') → ∀ i : Fin D.K,
      encRM D.N D.K (ψ (f ⬝ᵥ bv (g (ρ', i))) +
        (if γ then (2 : ZMod (2 ^ D.K - 1)) ^ (i : ℕ) • u else 0) + e (ρ', i)) =
      encRM D.N D.K (ψ (f ⬝ᵥ bv (g (ρ', i))) + u * (setting D).G ρ (ρ', i) + e (ρ', i)) := by
    intro γ ρ' hγ i
    have hG : u * (setting D).G ρ (ρ', i) = if ρ = ρ' then
        (2 : ZMod (2 ^ D.K - 1)) ^ (i : ℕ) • u else 0 := mul_G_apply u ρ (ρ', i)
    rw [hG]
    cases γ with
    | false =>
      have : ¬ ρ = ρ' := fun h => absurd (hγ.mpr h) (by decide)
      rw [if_neg this]; rfl
    | true =>
      have : ρ = ρ' := hγ.mp rfl
      rw [if_pos this]; rfl
  have hlen : ∀ (l : List (List Bool)), (∀ y ∈ l, y.length = D.N * D.K) →
      ∀ y ∈ l, y.length = D.N * D.K := fun l h => h
  have hwl : ∀ (F : Fin D.K → Rg D), ∀ y ∈ (List.finRange D.K).map (fun i => encRM D.N D.K (F i)),
      y.length = D.N * D.K := by
    intro F y hy; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy; exact length_encRM _ _ _
  by_cases hρ : ρ = 0
  · subst hρ
    have ex : exec D.N D.K (rowC m 0) w =
        exec D.N D.K (halfC (if false then gpost m else m))
          (exec D.N D.K (halfC (if true then gpost m else m)) w) := rfl
    obtain ⟨a1, a2, a3, a4, a5, a6, -, a8, a9⟩ := exec_halfC true m ψ hwm w hm f vs hvs hvf
      (fun i => g (0, i)) (fun i => e (0, i)) (fun i => es (0, i)) (fun i => hes _)
      (fun i => hef _) u _ _ (w xOut) [] (by simp) hV hZ' hF' hO0 hPl hPv hcK hCm hC1 hCNK hZero
      hv hb hf
    set w1 := exec D.N D.K (halfC (if true then gpost m else m)) w
    obtain ⟨b1, b2, b3, b4, b5, b6, -, -, b9⟩ := exec_halfC false m ψ hwm w1 (hmw w1 a9) f vs hvs
      hvf (fun i => g (1, i)) (fun i => e (1, i)) (fun i => es (1, i)) (fun i => hes _)
      (fun i => hef _) (decRM D.N D.K (w1 xP)) rest restF (w xOut) _ (hwl _)
      (by rw [a9 _ (by decide), hV]) a2 a3 a1 a8 rfl
      (by rw [a9 _ (by decide), hcK]) (by rw [a9 _ (by decide), hCm])
      (by rw [a9 _ (by decide), hC1]) (by rw [a9 _ (by decide), hCNK])
      (by rw [a9 _ (by decide), hZero]) a4 a5 a6
    rw [ex]
    refine ⟨?_, b2, b3, b4, b5, b6, fun j hj => by rw [b9 j hj, a9 j hj]⟩
    rw [b1, bufW_full (by
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · exact hwl _ y (by simpa using h)
        · exact hwl _ y h)
      (by rw [hOut, List.length_append, List.length_map, List.length_map,
        List.length_finRange]; ring), map_col]
    congr 2
    · exact List.map_congr_left fun i _ => hword true 0 (by decide) i
    · exact List.map_congr_left fun i _ => hword false 1 (by decide) i
  · have hρ1 : ρ = 1 := by
      revert hρ; clear hword; revert ρ; decide
    subst hρ1
    have ex : exec D.N D.K (rowC m 1) w =
        exec D.N D.K (halfC (if true then gpost m else m))
          (exec D.N D.K (halfC (if false then gpost m else m)) w) := rfl
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := exec_halfC false m ψ hwm w hm f vs hvs hvf
      (fun i => g (0, i)) (fun i => e (0, i)) (fun i => es (0, i)) (fun i => hes _)
      (fun i => hef _) u _ _ (w xOut) [] (by simp) hV hZ' hF' hO0 hPl hPv hcK hCm hC1 hCNK hZero
      hv hb hf
    set w1 := exec D.N D.K (halfC (if false then gpost m else m)) w
    have hP1 : w1 xP = w xP := a7 rfl
    obtain ⟨b1, b2, b3, b4, b5, b6, -, -, b9⟩ := exec_halfC true m ψ hwm w1 (hmw w1 a9) f vs hvs
      hvf (fun i => g (1, i)) (fun i => e (1, i)) (fun i => es (1, i)) (fun i => hes _)
      (fun i => hef _) u rest restF (w xOut) _ (hwl _)
      (by rw [a9 _ (by decide), hV]) a2 a3 a1 (by rw [hP1, hPl]) (by rw [hP1, hPv])
      (by rw [a9 _ (by decide), hcK]) (by rw [a9 _ (by decide), hCm])
      (by rw [a9 _ (by decide), hC1]) (by rw [a9 _ (by decide), hCNK])
      (by rw [a9 _ (by decide), hZero]) a4 a5 a6
    rw [ex]
    refine ⟨?_, b2, b3, b4, b5, b6, fun j hj => by rw [b9 j hj, a9 j hj]⟩
    rw [b1, bufW_full (by
        intro y hy
        rcases List.mem_append.mp hy with h | h
        · exact hwl _ y (by simpa using h)
        · exact hwl _ y h)
      (by rw [hOut, List.length_append, List.length_map, List.length_map,
        List.length_finRange]; ring), map_col]
    congr 2
    · exact List.map_congr_left fun i _ => hword false 0 (by decide) i
    · exact List.map_congr_left fun i _ => hword true 1 (by decide) i

end AdvancedEncryption.ExpLUT.Prog.RedPubP
