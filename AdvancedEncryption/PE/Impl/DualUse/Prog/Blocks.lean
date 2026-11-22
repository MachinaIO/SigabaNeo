import PE.Impl.DualUse.Prog.C0
import SigabaNeo.Lib.Lattices.ProgAlgo.Hash

/-!
# Word blocks with their templates

Each library word program (`SigabaNeo.Lib.Lattices.ProgAlgo`, `SigabaNeo.Lib.Machines.Prog.Split`)
is wrapped as a small `XProg` that builds its templates (`natP`), runs, and clears the templates
again. Every block writes **one** tape, `0`, and reads its inputs on the next tapes; the remaining
tapes are scratch, blank before and after. Its law is therefore an update:
`law S = PMF.pure (Function.update S 0 v)` whenever the scratch tapes of `S` are blank.

Placed by a frame on any distinct tapes of a larger machine (`law_frame_upd`), the blocks compose
by rewriting. Each block has a uniform time bound (`UB`).

| block | tapes | value on tape `0` |
|---|---|---|
| `trB m r s B Z` | `1` input; scratch `2 … 20` | `trW m r s B Z` (transposes) |
| `selB n B` | `1` bits, `2` `X`, `3` `Y`; scratch `4 … 13` | `selW n B` |
| `hashB P d N K` | `1` bits, `2` `V`, `3` `E`; scratch `4 … 45` | `hashW P d N K` |
| `mmB m n l N K` | `1` `x`, `2` `y`; scratch `3 … 59` | `matMulW N K m n l` |
| `addB L N K`, `subB L N K` | `1` `x`, `2` `y`; scratch `3 … 28` | `matAddW`, `matSubW` |
| `getB o L` | `1` a word `W`; scratch `2 … 10` | `takeD L (W.drop o)` |
| `joinB a b c` | `1` `2` `3`; scratch `4 … 11` | `takeD a A ++ takeD b B ++ takeD c C` |
| `gadB N K k` | scratch `1 … 21` | `gadW N K k` |
| `oneB N K` | scratch `1` | `true :: replicate (N K − 1) false` |
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape SigabaNeo.Tape.XProg

/-! ### Generic lemmas -/

section Generic

variable {n k : ℕ}

/-- **A framed block with an update law** updates the image of its output tape. -/
theorem law_frame_upd (e : Fin n ↪ Fin k) (p : XProg n) (s : Store k) (o : Fin n) (v : List Bool)
    (h : p.law (fun j => s (e j)) = PMF.pure (Function.update (fun j => s (e j)) o v)) :
    (frame e p).law s = PMF.pure (Function.update s (e o) v) := by
  rw [law_frame, h, PMF.pure_map, embedF_upd, embedF_comp]

/-- A relabelled deterministic program with an update law. -/
theorem law_progMap {u : Fin n → Fin k} (hu : Function.Injective u) (p : Prog n) (hp : p.NoGrow)
    (s : Store k) (o : Fin n) (v : List Bool) (h : p.run (s ∘ u) = Function.update (s ∘ u) o v) :
    (prog (Prog.map u p)).law s = PMF.pure (Function.update s (u o) v) := by
  rw [law_prog]; exact Prog.law_map_eq_update hu p hp s o v h

/-- **A uniform bound of a relabelled deterministic program.** -/
theorem ub_progMap (u : Fin n → Fin k) (p : Prog n) (hp : p.NoGrow) (M : ℕ) :
    UB (prog (Prog.map u p)) M (Prog.timeBound p M) M := by
  intro ℓ hℓ
  have hc : ℓ ≤ fun _ => M := fun j => hℓ j
  refine ⟨?_, fun i => ?_⟩
  · rw [timeBoundT_prog, ← Prog.timeBound_map (u := u)]
    exact (Prog.timeBoundT_mono (Prog.map u p) hc).trans (Prog.timeBoundT_const_le (Prog.map u p) M)
  · show Prog.lenBoundT (Prog.map u p) ℓ i ≤ M
    have := ((Prog.lenBoundT_mono (Prog.map u p) hc).trans (Prog.lenBoundT_const_le (Prog.map u p) M)) i
    rwa [Prog.lenBound_eq _ (hp.map u)] at this

/-- **A uniform bound of a framed block.** -/
theorem ub_frameB (e : Fin n ↪ Fin k) {p : XProg n} {M T M' : ℕ} (h : UB p M T M') (hM : M ≤ M') :
    UB (frame e p) M T M' := by
  intro ℓ hℓ
  have hc : ∀ j, (fun j => ℓ (e j)) j ≤ M := fun j => hℓ (e j)
  refine ⟨?_, fun i => ?_⟩
  · rw [timeBoundT_frame]; exact (h _ hc).1
  · show embedF e ℓ (lenBoundT p fun j => ℓ (e j)) i ≤ M'
    rcases embedF_cases e ℓ (lenBoundT p fun j => ℓ (e j)) i with ⟨-, h'⟩ | ⟨j, rfl, h'⟩
    · rw [h']; exact (hℓ i).trans hM
    · rw [h']; exact (h _ hc).2 j

theorem wf_progMap {u : Fin n → Fin k} (hu : Function.Injective u) {p : Prog n} (hp : p.WF) :
    (prog (Prog.map u p)).WF := Prog.WF.map hu hp

end Generic

/-! ### Transposes -/

def trU : Fin 20 → Fin 21 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
theorem trU_inj : Function.Injective trU := by decide

/-- **The transposes of `m` block matrices** (`trW`), with their templates. -/
def trB (m r s B Z : ℕ) : XProg 21 :=
  seq (natP 2 20 B) <| seq (natP 3 20 r) <| seq (natP 4 20 s) <| seq (natP 5 20 m) <|
  seq (natP 6 20 Z) <| seq (natP 7 20 (m * (s * (r * B) + Z))) <|
  seq (prog (Prog.map trU Prog.trP)) <| clearL [2, 3, 4, 5, 6, 7]

theorem wf_trB (m r s B Z : ℕ) : (trB m r s B Z).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, wf_natP (by decide) _, wf_progMap trU_inj Prog.wf_trP, wf_clearL _⟩

set_option maxHeartbeats 1000000 in
theorem law_trB (m r s B Z : ℕ) (S : Store 21) (hS : ∀ i : Fin 21, 2 ≤ i.val → S i = []) :
    (trB m r s B Z).law S = PMF.pure (Function.update S 0 (trW m r s B Z (S 1))) := by
  unfold trB
  rw [law_seq, law_natP (by decide) _ _ (hS 20 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_progMap trU_inj _ Prog.noGrow_trP _ 0 _ (Prog.run_trP (B := B) (r := r) (s := s)
    (m := m) (Z := Z) _ (fun i hi => by fin_cases i <;> first | (simp at hi; done) | simp [trU, hS])
    (by simp [trU]) (by simp [trU]) (by simp [trU]) (by simp [trU]) (by simp [trU]) (by simp [trU])),
    PMF.pure_bind, law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [trU, hS]

/-- The sizes of the templates of `trB`. -/
def sizeTrB (m r s B Z : ℕ) : ℕ := B + r + s + m + Z + m * (s * (r * B) + Z)

/-- The time of `trB` from tapes below `M`. -/
def timeTrB (m r s B Z M : ℕ) : ℕ :=
  (2 * B + 1) * (4 * M + 12) + (2 * r + 1) * (4 * M + 12) + (2 * s + 1) * (4 * M + 12) +
    (2 * m + 1) * (4 * M + 12) + (2 * Z + 1) * (4 * M + 12) +
    (2 * (m * (s * (r * B) + Z)) + 1) * (4 * M + 12) + Prog.timeBound Prog.trP M +
    ([2, 3, 4, 5, 6, 7].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_trB (m r s B Z M : ℕ) (hM : sizeTrB m r s B Z ≤ M) :
    UB (trB m r s B Z) M (timeTrB m r s B Z M) M := by
  unfold sizeTrB at hM
  have u := (ub_natP (t := (2 : Fin 21)) (c := 20) (by decide) (n := B) (M := M) (by omega)).seq <|
    (ub_natP (t := (3 : Fin 21)) (c := 20) (by decide) (n := r) (M := M) (by omega)).seq <|
    (ub_natP (t := (4 : Fin 21)) (c := 20) (by decide) (n := s) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 21)) (c := 20) (by decide) (n := m) (M := M) (by omega)).seq <|
    (ub_natP (t := (6 : Fin 21)) (c := 20) (by decide) (n := Z) (M := M) (by omega)).seq <|
    (ub_natP (t := (7 : Fin 21)) (c := 20) (by decide) (n := m * (s * (r * B) + Z)) (M := M)
      (by omega)).seq <|
    (ub_progMap trU _ Prog.noGrow_trP M).seq <| ub_clearL M [2, 3, 4, 5, 6, 7]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeTrB, Nat.add_assoc, List.length_cons, List.length_nil]

/-! ### Selection by bits -/

def selU : Fin 13 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
theorem selU_inj : Function.Injective selU := by decide

/-- **Blocks selected by bits** (`selW`), with their templates. -/
def selB (n B : ℕ) : XProg 14 :=
  seq (natP 4 13 B) <| seq (natP 5 13 n) <| seq (natP 6 13 (n * B)) <|
  seq (prog (Prog.map selU Prog.bitSelP)) <| clearL [4, 5, 6]

theorem wf_selB (n B : ℕ) : (selB n B).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_progMap selU_inj Prog.wf_bitSelP, wf_clearL _⟩

set_option maxHeartbeats 1000000 in
theorem law_selB (n B : ℕ) (S : Store 14) (hS : ∀ i : Fin 14, 4 ≤ i.val → S i = []) :
    (selB n B).law S = PMF.pure (Function.update S 0 (selW n B (S 1) (S 2) (S 3))) := by
  unfold selB
  rw [law_seq, law_natP (by decide) _ _ (hS 13 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_progMap selU_inj _ Prog.noGrow_bitSelP _ 0 _ (Prog.run_bitSelP (B := B) (n := n)
    _ (fun i hi => by fin_cases i <;> first | (simp at hi; done) | simp [selU, hS])
    (by simp [selU]) (by simp [selU]) (by simp [selU])), PMF.pure_bind, law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [selU, hS]

def sizeSelB (n B : ℕ) : ℕ := B + n + n * B

def timeSelB (n B M : ℕ) : ℕ :=
  (2 * B + 1) * (4 * M + 12) + (2 * n + 1) * (4 * M + 12) + (2 * (n * B) + 1) * (4 * M + 12) +
    Prog.timeBound Prog.bitSelP M + ([4, 5, 6].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_selB (n B M : ℕ) (hM : sizeSelB n B ≤ M) : UB (selB n B) M (timeSelB n B M) M := by
  unfold sizeSelB at hM
  have u := (ub_natP (t := (4 : Fin 14)) (c := 13) (by decide) (n := B) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 14)) (c := 13) (by decide) (n := n) (M := M) (by omega)).seq <|
    (ub_natP (t := (6 : Fin 14)) (c := 13) (by decide) (n := n * B) (M := M) (by omega)).seq <|
    (ub_progMap selU _ Prog.noGrow_bitSelP M).seq <| ub_clearL M [4, 5, 6]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeSelB, Nat.add_assoc, List.length_cons, List.length_nil]

/-! ### Sums selected by bits -/

def hashU : Fin 45 → Fin 46 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
  44]
theorem hashU_inj : Function.Injective hashU := by decide

/-- **Sums selected by bits** (`hashW`), with their templates. -/
def hashB (P d N K : ℕ) : XProg 46 :=
  seq (natP 4 45 K) <| seq (natP 5 45 N) <| seq (natP 6 45 (N * K)) <| seq (natP 7 45 d) <|
  seq (natP 8 45 P) <| seq (natP 9 45 (P * (N * K))) <|
  seq (prog (Prog.map hashU Prog.hashP)) <| clearL [4, 5, 6, 7, 8, 9]

theorem wf_hashB (P d N K : ℕ) : (hashB P d N K).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, wf_natP (by decide) _, wf_progMap hashU_inj Prog.wf_hashP, wf_clearL _⟩

set_option maxHeartbeats 2000000 in
theorem law_hashB (P d N K : ℕ) (S : Store 46) (hS : ∀ i : Fin 46, 4 ≤ i.val → S i = []) :
    (hashB P d N K).law S = PMF.pure (Function.update S 0 (hashW P d N K (S 1) (S 2) (S 3))) := by
  unfold hashB
  rw [law_seq, law_natP (by decide) _ _ (hS 45 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_progMap hashU_inj _ Prog.noGrow_hashP _ 0 _ (Prog.run_hashP (K := K) (N := N)
    (d := d) (P := P) _ (fun i hi => by fin_cases i <;> first | (simp at hi; done) | simp [hashU, hS])
    (by simp [hashU]) (by simp [hashU]) (by simp [hashU]) (by simp [hashU]) (by simp [hashU])
    (by simp [hashU])), PMF.pure_bind, law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [hashU, hS]

def sizeHashB (P d N K : ℕ) : ℕ := K + N + N * K + d + P + P * (N * K)

def timeHashB (P d N K M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + (2 * N + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * d + 1) * (4 * M + 12) + (2 * P + 1) * (4 * M + 12) +
    (2 * (P * (N * K)) + 1) * (4 * M + 12) + Prog.timeBound Prog.hashP M +
    ([4, 5, 6, 7, 8, 9].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_hashB (P d N K M : ℕ) (hM : sizeHashB P d N K ≤ M) :
    UB (hashB P d N K) M (timeHashB P d N K M) M := by
  unfold sizeHashB at hM
  have u := (ub_natP (t := (4 : Fin 46)) (c := 45) (by decide) (n := K) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 46)) (c := 45) (by decide) (n := N) (M := M) (by omega)).seq <|
    (ub_natP (t := (6 : Fin 46)) (c := 45) (by decide) (n := N * K) (M := M) (by omega)).seq <|
    (ub_natP (t := (7 : Fin 46)) (c := 45) (by decide) (n := d) (M := M) (by omega)).seq <|
    (ub_natP (t := (8 : Fin 46)) (c := 45) (by decide) (n := P) (M := M) (by omega)).seq <|
    (ub_natP (t := (9 : Fin 46)) (c := 45) (by decide) (n := P * (N * K)) (M := M) (by omega)).seq <|
    (ub_progMap hashU _ Prog.noGrow_hashP M).seq <| ub_clearL M [4, 5, 6, 7, 8, 9]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeHashB, Nat.add_assoc, List.length_cons, List.length_nil]

/-! ### Matrix products -/

def mmU : Fin 59 → Fin 60 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
  44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
theorem mmU_inj : Function.Injective mmU := by decide

/-- **The product of matrix words** (`matMulW`), with its templates. -/
def mmB (m n l N K : ℕ) : XProg 60 :=
  seq (natP 3 59 K) <| seq (natP 4 59 N) <| seq (natP 5 59 (N * K)) <| seq (natP 6 59 m) <|
  seq (natP 7 59 n) <| seq (natP 8 59 l) <| seq (natP 9 59 (m * l * (N * K))) <|
  seq (prog (Prog.map mmU Prog.matMulP)) <| clearL [3, 4, 5, 6, 7, 8, 9]

theorem wf_mmB (m n l N K : ℕ) : (mmB m n l N K).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_progMap mmU_inj Prog.wf_matMulP, wf_clearL _⟩

set_option maxHeartbeats 4000000 in
theorem law_mmB (m n l N K : ℕ) (S : Store 60) (hS : ∀ i : Fin 60, 3 ≤ i.val → S i = [])
    (hx : (S 1).length = m * n * (N * K)) (hy : (S 2).length = n * l * (N * K)) :
    (mmB m n l N K).law S = PMF.pure (Function.update S 0 (matMulW N K m n l (S 1) (S 2))) := by
  unfold mmB
  rw [law_seq, law_natP (by decide) _ _ (hS 59 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_progMap mmU_inj _ Prog.noGrow_matMulP _ 0 _ (Prog.run_matMulP (K := K) (N := N)
    (m := m) (n := n) (l := l) _
    (fun i hi => by fin_cases i <;> first | (simp at hi; done) | simp [mmU, hS])
    (by simp [mmU]) (by simp [mmU]) (by simp [mmU]) (by simp [mmU]) (by simp [mmU]) (by simp [mmU])
    (by simp [mmU]) (by simp [mmU, hx]) (by simp [mmU, hy])), PMF.pure_bind, law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [mmU, hS]

def sizeMmB (m n l N K : ℕ) : ℕ := K + N + N * K + m + n + l + m * l * (N * K)

def timeMmB (m n l N K M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + (2 * N + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * m + 1) * (4 * M + 12) + (2 * n + 1) * (4 * M + 12) + (2 * l + 1) * (4 * M + 12) +
    (2 * (m * l * (N * K)) + 1) * (4 * M + 12) + Prog.timeBound Prog.matMulP M +
    ([3, 4, 5, 6, 7, 8, 9].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_mmB (m n l N K M : ℕ) (hM : sizeMmB m n l N K ≤ M) :
    UB (mmB m n l N K) M (timeMmB m n l N K M) M := by
  unfold sizeMmB at hM
  have u := (ub_natP (t := (3 : Fin 60)) (c := 59) (by decide) (n := K) (M := M) (by omega)).seq <|
    (ub_natP (t := (4 : Fin 60)) (c := 59) (by decide) (n := N) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 60)) (c := 59) (by decide) (n := N * K) (M := M) (by omega)).seq <|
    (ub_natP (t := (6 : Fin 60)) (c := 59) (by decide) (n := m) (M := M) (by omega)).seq <|
    (ub_natP (t := (7 : Fin 60)) (c := 59) (by decide) (n := n) (M := M) (by omega)).seq <|
    (ub_natP (t := (8 : Fin 60)) (c := 59) (by decide) (n := l) (M := M) (by omega)).seq <|
    (ub_natP (t := (9 : Fin 60)) (c := 59) (by decide) (n := m * l * (N * K)) (M := M)
      (by omega)).seq <|
    (ub_progMap mmU _ Prog.noGrow_matMulP M).seq <| ub_clearL M [3, 4, 5, 6, 7, 8, 9]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeMmB, Nat.add_assoc, List.length_cons, List.length_nil]

/-! ### Entrywise sums and differences -/

def adU : Fin 28 → Fin 29 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 21, 22, 23, 24, 25, 26, 27]
theorem adU_inj : Function.Injective adU := by decide

/-- **Entrywise sum of `L` ring entries** (`matAddW`), with its templates. -/
def addB (L N K : ℕ) : XProg 29 :=
  seq (natP 3 28 K) <| seq (natP 4 28 (L * N)) <| seq (prog (Prog.map adU Prog.addRWP)) <|
  clearL [3, 4]

/-- **Entrywise difference of `L` ring entries** (`matSubW`), with its templates. -/
def subB (L N K : ℕ) : XProg 29 :=
  seq (natP 3 28 K) <| seq (natP 4 28 (L * N)) <| seq (prog (Prog.map adU Prog.subRWP)) <|
  clearL [3, 4]

theorem wf_addB (L N K : ℕ) : (addB L N K).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_progMap adU_inj Prog.wf_addRWP, wf_clearL _⟩

theorem wf_subB (L N K : ℕ) : (subB L N K).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_progMap adU_inj Prog.wf_subRWP, wf_clearL _⟩

set_option maxHeartbeats 1000000 in
theorem law_addB (L N K : ℕ) (S : Store 29) (hS : ∀ i : Fin 29, 3 ≤ i.val → S i = [])
    (hx : (S 1).length = L * N * K) (hy : (S 2).length = L * N * K) :
    (addB L N K).law S = PMF.pure (Function.update S 0 (matAddW N K L (S 1) (S 2))) := by
  unfold addB
  rw [law_seq, law_natP (by decide) _ _ (hS 28 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_progMap adU_inj _ Prog.noGrow_addRWP _ 0 _ (Prog.run_addRWP_mat (K := K) (N := N)
    (L := L) _ (fun i hi => by fin_cases i <;> first | (simp at hi; done) | simp [adU, hS])
    (by simp [adU]) (by simp [adU]) (by simp [adU, hx]) (by simp [adU, hy])), PMF.pure_bind,
    law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [adU, hS]

set_option maxHeartbeats 1000000 in
theorem law_subB (L N K : ℕ) (S : Store 29) (hS : ∀ i : Fin 29, 3 ≤ i.val → S i = [])
    (hx : (S 1).length = L * N * K) (hy : (S 2).length = L * N * K) :
    (subB L N K).law S = PMF.pure (Function.update S 0 (matSubW N K L (S 1) (S 2))) := by
  unfold subB
  rw [law_seq, law_natP (by decide) _ _ (hS 28 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_progMap adU_inj _ Prog.noGrow_subRWP _ 0 _ (Prog.run_subRWP_mat (K := K) (N := N)
    (L := L) _ (fun i hi => by fin_cases i <;> first | (simp at hi; done) | simp [adU, hS])
    (by simp [adU]) (by simp [adU]) (by simp [adU, hx]) (by simp [adU, hy])), PMF.pure_bind,
    law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [adU, hS]

def sizeAddB (L N K : ℕ) : ℕ := K + L * N

def timeAddB (L N K M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + (2 * (L * N) + 1) * (4 * M + 12) + Prog.timeBound Prog.addRWP M +
    ([3, 4].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

def timeSubB (L N K M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + (2 * (L * N) + 1) * (4 * M + 12) + Prog.timeBound Prog.subRWP M +
    ([3, 4].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_addB (L N K M : ℕ) (hM : sizeAddB L N K ≤ M) : UB (addB L N K) M (timeAddB L N K M) M := by
  unfold sizeAddB at hM
  have u := (ub_natP (t := (3 : Fin 29)) (c := 28) (by decide) (n := K) (M := M) (by omega)).seq <|
    (ub_natP (t := (4 : Fin 29)) (c := 28) (by decide) (n := L * N) (M := M) (by omega)).seq <|
    (ub_progMap adU _ Prog.noGrow_addRWP M).seq <| ub_clearL M [3, 4]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeAddB, Nat.add_assoc, List.length_cons, List.length_nil]

theorem ub_subB (L N K M : ℕ) (hM : sizeAddB L N K ≤ M) : UB (subB L N K) M (timeSubB L N K M) M := by
  unfold sizeAddB at hM
  have u := (ub_natP (t := (3 : Fin 29)) (c := 28) (by decide) (n := K) (M := M) (by omega)).seq <|
    (ub_natP (t := (4 : Fin 29)) (c := 28) (by decide) (n := L * N) (M := M) (by omega)).seq <|
    (ub_progMap adU _ Prog.noGrow_subRWP M).seq <| ub_clearL M [3, 4]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeSubB, Nat.add_assoc, List.length_cons, List.length_nil]

/-! ### Fields of a word -/

def getU : Fin 10 → Fin 11 := ![2, 0, 3, 1, 4, 5, 6, 7, 8, 9]
theorem getU_inj : Function.Injective getU := by decide

/-- **The field of length `L` at the offset `o`** of the word on tape `1`. -/
def getB (o L : ℕ) : XProg 11 :=
  seq (natP 4 10 o) <| seq (natP 5 10 L) <| seq (prog (Prog.map getU Prog.splitP)) <| clearL [2, 4, 5]

theorem wf_getB (o L : ℕ) : (getB o L).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_progMap getU_inj Prog.wf_splitP, wf_clearL _⟩

set_option maxHeartbeats 1000000 in
theorem law_getB (o L : ℕ) (S : Store 11) (hS : ∀ i : Fin 11, 2 ≤ i.val → S i = []) :
    (getB o L).law S = PMF.pure (Function.update S 0 (takeD L ((S 1).drop o))) := by
  unfold getB
  rw [law_seq, law_natP (by decide) _ _ (hS 10 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_prog, Prog.law_eq_run _ (Prog.noGrow_splitP.map getU),
    Prog.run_splitP_map getU_inj _ (by simp [getU, hS]) (by simp [getU, hS]) (by simp [getU, hS]),
    PMF.pure_bind, law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [getU, hS, takeD]

def timeGetB (o L M : ℕ) : ℕ :=
  (2 * o + 1) * (4 * M + 12) + (2 * L + 1) * (4 * M + 12) + Prog.timeBound Prog.splitP M +
    ([2, 4, 5].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_getB (o L M : ℕ) (hM : o + L ≤ M) : UB (getB o L) M (timeGetB o L M) M := by
  have u := (ub_natP (t := (4 : Fin 11)) (c := 10) (by decide) (n := o) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 11)) (c := 10) (by decide) (n := L) (M := M) (by omega)).seq <|
    (ub_progMap getU _ Prog.noGrow_splitP M).seq <| ub_clearL M [2, 4, 5]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeGetB, Nat.add_assoc, List.length_cons, List.length_nil]

/-! ### Joins -/

def joinU : Fin 11 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
theorem joinU_inj : Function.Injective joinU := by decide

/-- **The join of three words**, cut to the lengths `a`, `b`, `c`. -/
def joinB (a b c : ℕ) : XProg 12 :=
  seq (natP 4 11 a) <| seq (natP 5 11 b) <| seq (natP 6 11 c) <| seq (natP 7 11 (a + b + c)) <|
  seq (prog (Prog.map joinU Prog.joinP)) <| clearL [4, 5, 6, 7]

theorem wf_joinB (a b c : ℕ) : (joinB a b c).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_progMap joinU_inj Prog.wf_joinP, wf_clearL _⟩

set_option maxHeartbeats 1000000 in
theorem law_joinB (a b c : ℕ) (S : Store 12) (hS : ∀ i : Fin 12, 4 ≤ i.val → S i = []) :
    (joinB a b c).law S = PMF.pure (Function.update S 0
      (takeD a (S 1) ++ takeD b (S 2) ++ takeD c (S 3))) := by
  unfold joinB
  rw [law_seq, law_natP (by decide) _ _ (hS 11 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_prog, Prog.law_eq_run _ (Prog.noGrow_joinP.map joinU),
    Prog.run_joinP_map joinU_inj _ (by simp [joinU, hS]) (by simp [joinU, hS]) (by simp [joinU, hS])
      (by simp [joinU]), PMF.pure_bind, law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [joinU, hS]

def timeJoinB (a b c M : ℕ) : ℕ :=
  (2 * a + 1) * (4 * M + 12) + (2 * b + 1) * (4 * M + 12) + (2 * c + 1) * (4 * M + 12) +
    (2 * (a + b + c) + 1) * (4 * M + 12) + Prog.timeBound Prog.joinP M +
    ([4, 5, 6, 7].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_joinB (a b c M : ℕ) (hM : a + b + c ≤ M) : UB (joinB a b c) M (timeJoinB a b c M) M := by
  have u := (ub_natP (t := (4 : Fin 12)) (c := 11) (by decide) (n := a) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 12)) (c := 11) (by decide) (n := b) (M := M) (by omega)).seq <|
    (ub_natP (t := (6 : Fin 12)) (c := 11) (by decide) (n := c) (M := M) (by omega)).seq <|
    (ub_natP (t := (7 : Fin 12)) (c := 11) (by decide) (n := a + b + c) (M := M) (by omega)).seq <|
    (ub_progMap joinU _ Prog.noGrow_joinP M).seq <| ub_clearL M [4, 5, 6, 7]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeJoinB, Nat.add_assoc, List.length_cons, List.length_nil]

/-! ### The gadget row and the word of `1` -/

def gadU : Fin 21 → Fin 22 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20]
theorem gadU_inj : Function.Injective gadU := by decide

/-- **The gadget row `G̲`** (`gadW`), with its templates. -/
def gadB (N K k : ℕ) : XProg 22 :=
  seq (natP 1 21 K) <| seq (natP 2 21 N) <| seq (natP 3 21 (N * K)) <| seq (natP 4 21 k) <|
  seq (natP 5 21 (2 * k * (N * K))) <| seq (prog (Prog.map gadU Prog.gadP)) <| clearL [1, 2, 3, 4, 5]

theorem wf_gadB (N K k : ℕ) : (gadB N K k).WF :=
  ⟨wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _, wf_natP (by decide) _,
    wf_natP (by decide) _, wf_progMap gadU_inj Prog.wf_gadP, wf_clearL _⟩

set_option maxHeartbeats 1000000 in
theorem law_gadB (N K k : ℕ) (S : Store 22) (hS : ∀ i : Fin 22, 1 ≤ i.val → S i = []) :
    (gadB N K k).law S = PMF.pure (Function.update S 0 (gadW N K k)) := by
  unfold gadB
  rw [law_seq, law_natP (by decide) _ _ (hS 21 (by decide)), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_natP (by decide) _ _ (by simp [hS]), PMF.pure_bind]
  rw [law_seq, law_progMap gadU_inj _ Prog.noGrow_gadP _ 0 _ (Prog.run_gadP (K := K) (N := N) (k := k)
    _ (fun i hi => by fin_cases i <;> first | (simp at hi; done) | simp [gadU, hS])
    (by simp [gadU]) (by simp [gadU]) (by simp [gadU]) (by simp [gadU]) (by simp [gadU])),
    PMF.pure_bind, law_clearL]
  congr 1
  funext t
  fin_cases t <;> simp [gadU, hS]

def sizeGadB (N K k : ℕ) : ℕ := K + N + N * K + k + 2 * k * (N * K)

def timeGadB (N K k M : ℕ) : ℕ :=
  (2 * K + 1) * (4 * M + 12) + (2 * N + 1) * (4 * M + 12) + (2 * (N * K) + 1) * (4 * M + 12) +
    (2 * k + 1) * (4 * M + 12) + (2 * (2 * k * (N * K)) + 1) * (4 * M + 12) +
    Prog.timeBound Prog.gadP M + ([1, 2, 3, 4, 5].length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_gadB (N K k M : ℕ) (hM : sizeGadB N K k ≤ M) : UB (gadB N K k) M (timeGadB N K k M) M := by
  unfold sizeGadB at hM
  have u := (ub_natP (t := (1 : Fin 22)) (c := 21) (by decide) (n := K) (M := M) (by omega)).seq <|
    (ub_natP (t := (2 : Fin 22)) (c := 21) (by decide) (n := N) (M := M) (by omega)).seq <|
    (ub_natP (t := (3 : Fin 22)) (c := 21) (by decide) (n := N * K) (M := M) (by omega)).seq <|
    (ub_natP (t := (4 : Fin 22)) (c := 21) (by decide) (n := k) (M := M) (by omega)).seq <|
    (ub_natP (t := (5 : Fin 22)) (c := 21) (by decide) (n := 2 * k * (N * K)) (M := M)
      (by omega)).seq <|
    (ub_progMap gadU _ Prog.noGrow_gadP M).seq <| ub_clearL M [1, 2, 3, 4, 5]
  refine u.mono (le_of_eq ?_) le_rfl
  simp only [timeGadB, Nat.add_assoc, List.length_cons, List.length_nil]

/-- **The word of `1`**: a leading `1`, then `N K − 1` zeros. -/
def oneB (N K : ℕ) : XProg 2 := seq (natP 0 1 (N * K - 1)) (prog (.prim (.cons 0 true)))

theorem wf_oneB (N K : ℕ) : (oneB N K).WF := ⟨wf_natP (by decide) _, trivial⟩

theorem law_oneB (N K : ℕ) (hN : 0 < N) (hK : 0 < K) (S : Store 2) (hS : S 1 = []) :
    (oneB N K).law S = PMF.pure (Function.update S 0 (oneW N K)) := by
  unfold oneB
  rw [law_seq, law_natP (by decide) _ _ hS, PMF.pure_bind, law_prim, oneW_eq hN hK]
  congr 1
  funext t
  fin_cases t <;> simp [Prim.apply]

def timeOneB (N K M : ℕ) : ℕ := (2 * (N * K - 1) + 1) * (4 * M + 12) + (2 * (M + 1) + 3)

theorem ub_oneB (N K M : ℕ) (hM : N * K ≤ M) : UB (oneB N K) M (timeOneB N K M) (M + 1) :=
  (ub_natP (t := (0 : Fin 2)) (c := 1) (by decide) (n := N * K - 1) (M := M) (by omega)).seq
    (ub_prim _ M)

end AdvancedEncryption.DualUse.Prog
