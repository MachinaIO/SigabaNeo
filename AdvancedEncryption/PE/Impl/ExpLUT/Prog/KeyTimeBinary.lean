import PE.Impl.ExpLUT.Prog.KeyTimeRing

/-! End-to-end runtime certificate for compiled binary ring instructions. -/
namespace AdvancedEncryption.ExpLUT.Prog.KeyTime
open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.MVM SigabaNeo.Tape.Prog
open SigabaNeo.Tape.Sym Prog.SpecT

def binaryFrame : Fin 37 ↪ Fin 105 := mkE (fOp 34) (fOp_inj 34 (Or.inl rfl))
def canonicalFrame : Fin 28 ↪ Fin 105 := mkE fCan fCan_inj

def binaryAfter (M N K : ℕ) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  embedF binaryFrame a (ringArea M N K (N * K))
def canonicalAfter (M N K : ℕ) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  embedF canonicalFrame a (ringArea M N K (N * K))

theorem embed_bound {k n : ℕ} (e : Fin n ↪ Fin k) (a : Fin k → ℕ) (b : Fin n → ℕ)
    (M : ℕ) (ha : ∀ t, a t ≤ M) (hb : ∀ j, b j ≤ M) : ∀ t, embedF e a b t ≤ M := by
  intro t
  rcases embedF_cases e a b t with ⟨_, h⟩ | ⟨j, _, h⟩
  · rw [h]; exact ha t
  · rw [h]; exact hb j

theorem ringArea_bound {n : ℕ} (M N K : ℕ) (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M) :
    ∀ j : Fin n, ringArea M N K (N * K) j ≤ M := by
  intro j
  simp only [ringArea]
  split_ifs <;> omega

theorem binaryAfter_fields (M N K : ℕ) (a : Fin 105 → ℕ) :
    binaryAfter M N K a 32 = N * K ∧ binaryAfter M N K a 35 = K ∧
    binaryAfter M N K a 36 = N ∧ binaryAfter M N K a 38 = a 38 := by
  have h0 := embedF_apply_self binaryFrame a (ringArea M N K (N * K)) 0
  have h3 := embedF_apply_self binaryFrame a (ringArea M N K (N * K)) 3
  have h4 := embedF_apply_self binaryFrame a (ringArea M N K (N * K)) 4
  refine ⟨h0, h3, h4, ?_⟩
  rcases embedF_cases binaryFrame a (ringArea M N K (N * K)) 38 with ⟨_, h⟩ | ⟨j, hj, _⟩
  · exact h
  · have he := congrArg Fin.val hj
    have hjlt := j.isLt
    change (if j.val = 0 then 32 else if j.val = 1 then 33 else if j.val = 2 then 34
      else if j.val = 3 then 35 else if j.val = 4 then 36 else j.val - 5) = 38 at he
    split_ifs at he <;> omega

theorem canonicalAfter_result (M N K : ℕ) (a : Fin 105 → ℕ) :
    canonicalAfter M N K a 33 = N * K :=
  embedF_apply_self canonicalFrame a (ringArea M N K (N * K)) 0

def binaryResult (M N K : ℕ) (d : Fin 64) (a : Fin 105 → ℕ) : Fin 105 → ℕ :=
  embedF (mkE (fOut d) (fOut_inj d))
    (canonicalAfter M N K (binaryAfter M N K
      (Function.update (Function.update a 33 (N * K)) 34 (N * K))))
    (fun j ↦ if j = 0 then N * K else 0)

def binaryTime (M N K : ℕ) (o : Op) : ℕ :=
  (2 * M + 3) * (2 * (30 + 10 * (N * K)) + pEval [M, N, K] (binaryPoly o) +
    (7 + 44 * N + 40 * (N * K)) + 20)

/-- A complete actual binary instruction, including both loads and canonical output. -/
theorem compile_binary_cert (o : Op) (ho : o = .add ∨ o = .sub ∨ o = .mul)
    (d s t : Fin 64) (M N K : ℕ) (a : Fin 105 → ℕ)
    (hM : ∀ j, a j ≤ M) (hNK : N * K ≤ M) (hN : N ≤ M) (hK : K ≤ M)
    (hk : a 35 ≤ K) (hn : a 36 ≤ N) (hz : a 37 = N * K) (hones : a 38 ≤ N * K)
    (h32 : a 32 = 0) (h39 : a 39 = 0) (h40 : a 40 = 0) :
    Cert (MVM.compile (.op o d s t)) a (binaryResult M N K d a) (binaryTime M N K o) := by
  let a1 := Function.update a (33 : Fin 105) (N * K)
  let a2 := Function.update a1 (34 : Fin 105) (N * K)
  have hM1 : ∀ j, a1 j ≤ M := by
    intro j
    simp only [a1, Function.update_apply]
    split_ifs <;> first | exact hNK | exact hM j
  have hM2 : ∀ j, a2 j ≤ M := by
    intro j
    simp only [a2, Function.update_apply]
    split_ifs <;> first | exact hNK | exact hM1 j
  have hload1 := load_cert N K M 33 (Or.inl rfl) s a hM hz h32 h39 h40
  have hload2 := load_cert N K M 34 (Or.inr rfl) t a1 hM1
    (by simpa [a1] using hz) (by simpa [a1] using h32)
    (by simpa [a1] using h39) (by simpa [a1] using h40)
  have hop := binaryOp_cert o ho M N K a2 hM2 (by simp [a2, a1]) (by simp [a2])
    (by simpa [a2, a1] using hk) (by simpa [a2, a1] using hn)
  have hbM := embed_bound binaryFrame a2 (ringArea M N K (N * K)) M hM2
    (ringArea_bound M N K hNK hN hK)
  obtain ⟨hb0, hb3, hb4, hb38⟩ := binaryAfter_fields M N K a2
  have hcan := canon_cert M N K (binaryAfter M N K a2) hbM hb0.le
    (by rw [hb38]; simpa [a2, a1] using hones) hb3.le hb4.le
  have hcM := embed_bound canonicalFrame (binaryAfter M N K a2)
    (ringArea M N K (N * K)) M hbM (ringArea_bound M N K hNK hN hK)
  have hout := store_cert N K M d (canonicalAfter M N K (binaryAfter M N K a2)) hcM
    (canonicalAfter_result M N K _).le
  have h := hload1.seq (hload2.seq (hop.seq (hcan.seq hout)))
  have he : (2 * M + 3) * (30 + 10 * (N * K)) +
      ((2 * M + 3) * (30 + 10 * (N * K)) +
      ((2 * M + 3) * pEval [M, N, K] (binaryPoly o) +
      ((2 * M + 3) * (7 + 44 * N + 40 * (N * K)) + (2 * M + 3) * 20))) =
        binaryTime M N K o := by unfold binaryTime; ring
  rw [he] at h
  have hbin : o.bin = true := by rcases ho with rfl | rfl | rfl <;> rfl
  simpa only [MVM.compile, t2Of, hbin, ↓reduceIte, binaryResult, a1, a2,
    binaryAfter, canonicalAfter, binaryFrame, canonicalFrame] using h

/-- The complete instruction leaves all operation words blank and a bounded result. -/
theorem binaryResult_words (M N K : ℕ) (d : Fin 64) (a : Fin 105 → ℕ) :
    binaryResult M N K d a (tR d) = N * K ∧
    binaryResult M N K d a 32 = 0 ∧ binaryResult M N K d a 33 = 0 ∧
    binaryResult M N K d a 34 = 0 := by
  let e := mkE (fOut d) (fOut_inj d)
  let b := canonicalAfter M N K (binaryAfter M N K
    (Function.update (Function.update a 33 (N * K)) 34 (N * K)))
  let z : Fin 4 → ℕ := fun j ↦ if j = 0 then N * K else 0
  exact ⟨embedF_apply_self e b z 0, embedF_apply_self e b z 1,
    embedF_apply_self e b z 2, embedF_apply_self e b z 3⟩

end AdvancedEncryption.ExpLUT.Prog.KeyTime
