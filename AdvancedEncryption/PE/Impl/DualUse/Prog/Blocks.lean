import PE.Impl.DualUse.Prog.C0
import SigabaNeo.Lib.Lattices.ProgAlgo.Hash
import SigabaNeo.Lib.Lattices.ProgAlgo.SpecZ

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

/-- The tapes `≥ j` of `Fin n`. -/
def scrFrom (n j : ℕ) : List (Fin n) := (List.finRange n).filter fun t => decide (j ≤ t.val)

theorem mem_scrFrom {n j : ℕ} (t : Fin n) : t ∈ scrFrom n j ↔ j ≤ t.val := by
  simp [scrFrom]

/-- **Clearing tapes**, from bounds below `M`. -/
theorem vb_clearL [NeZero k] {M : ℕ} : ∀ (l : List (Fin k)) {a : Fin k → ℕ}, (∀ t, a t ≤ M) →
    VB (clearL l) a (l.length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))
      (fun t => if t ∈ l then 0 else a t)
  | [], a, ha => by
    refine (VB.prim (.copy 0 0) ha).mono le_rfl (by simp) fun t => ?_
    simp only [Prim.lenT, Function.update_apply, List.not_mem_nil, if_false]
    split_ifs with h
    · subst h; exact le_rfl
    · exact le_rfl
  | t :: l, a, ha => by
    have h1 := VB.prim (.clear t) ha
    have h2 := vb_clearL (M := M) l (a := (Prim.clear t).lenT a) fun i => by
      simp only [Prim.lenT, Function.update_apply]; split_ifs
      · exact Nat.zero_le _
      · exact ha i
    refine (h1.seq h2).mono le_rfl (by simp only [List.length_cons]; ring_nf; omega) fun i => ?_
    simp only [Prim.lenT, Function.update_apply, List.mem_cons]
    by_cases h1 : i = t <;> by_cases h2 : i ∈ l <;> simp [h1, h2]

open SigabaNeo.Tape.Sym in
/-- **A summarised program followed by clearing the scratch tapes `≥ j`.** -/
theorem vb_leafClear [NeZero k] {m fuel : ℕ} {p : Prog m} {σ : Asg} {w : Poly}
    (h : check fuel p σ [] w = true) (ρ : List ℕ) {M j : ℕ} (htop : top ρ = M)
    {u : Fin m → Fin k} (hu : Function.Injective u) {a : Fin k → ℕ} (ha : ∀ t, a t ≤ M)
    (hin : ∀ i, a (u i) ≤ pEval ρ (aGet σ i.val)) (scr : List (Fin k))
    (hscr : ∀ t : Fin k, j ≤ t.val → t ∈ scr) :
    VB (seq (prog (Prog.map u p)) (clearL scr)) a
      ((2 * M + 3) * pEval ρ w + (scr.length * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))) (zv j M) := by
  have h1 := VB.checkMap h ρ hu (b := fun _ => M) hin (fun t => htop ▸ ha t)
    (fun j hj => absurd hj (by simp)) (fun _ _ => htop.le) (fun t _ => ha t)
  rw [htop] at h1
  refine (h1.seq (vb_clearL scr (a := fun _ => M) fun _ => le_rfl)).mono le_rfl le_rfl fun t => ?_
  simp only [zv]
  by_cases ht : t ∈ scr
  · simp [ht]
  · have : t.val < j := by by_contra h'; exact ht (hscr t (by omega))
    simp [ht, this]

theorem natB_le {t c : Fin k} {n M : ℕ} {a : Fin k → ℕ} (ha : ∀ i, a i ≤ M) (hn : n ≤ M) (i : Fin k) :
    natB t c n a i ≤ M := by
  simp only [natB]; split_ifs
  · exact hn
  · exact max_le (ha c) hn
  · exact ha i

end Generic

/-! ### Transposes -/

def trU : Fin 20 → Fin 21 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
theorem trU_inj : Function.Injective trU := by decide

/-- **The transposes of `m` block matrices** (`trW`), with their templates. -/
def trB (m r s B Z : ℕ) : XProg 21 :=
  seq (natP 2 20 B) <| seq (natP 3 20 r) <| seq (natP 4 20 s) <| seq (natP 5 20 m) <|
  seq (natP 6 20 Z) <| seq (natP 7 20 (m * (s * (r * B) + Z))) <|
  seq (prog (Prog.map trU Prog.trP)) <| clearL (scrFrom 21 2)

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
  fin_cases t <;> simp [trU, hS, mem_scrFrom]

/-- The sizes of the templates of `trB`. -/
def sizeTrB (m r s B Z : ℕ) : ℕ := B + r + s + m + Z + m * (s * (r * B) + Z)

/-- The time of `trB` from tapes below `M` (scratch blank). -/
def timeTrB (m r s B Z M : ℕ) : ℕ :=
  (2 * (B) + 1) * (4 * M + 12) + ((2 * (r) + 1) * (4 * M + 12) + ((2 * (s) + 1) * (4 * M + 12) + ((2 * (m) + 1) * (4 * M + 12) + ((2 * (Z) + 1) * (4 * M + 12) + ((2 * (m * (s * (r * B) + Z)) + 1) * (4 * M + 12) + ((2 * M + 3) * (5 + 10 * m + 8 * s * m + 12 * r * s * m + 9 * B * r * s * m + 4 * r * s ^ 2 * m + 3 * B * r * s ^ 2 * m + 3 * B * s * m + 4 * r * m + 3 * m * Z) + ((19 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)))))))))

open SigabaNeo.Tape.Sym Prog.SpecZ Prog.SpecT in
theorem ub_trB (m r s B Z M : ℕ) (hM : sizeTrB m r s B Z ≤ M) :
    UBZ 2 (trB m r s B Z) M (timeTrB m r s B Z M) M := by
  unfold sizeTrB at hM
  have a0 := zv_le (k := 21) 2 M
  have h1 := VB.natP (t := (2 : Fin 21)) (c := 20) (by decide) (B) a0 (by omega)
  have a1 := natB_le (t := (2 : Fin 21)) (c := 20) (n := B) a0 (by omega)
  have h2 := VB.natP (t := (3 : Fin 21)) (c := 20) (by decide) (r) a1 (by omega)
  have a2 := natB_le (t := (3 : Fin 21)) (c := 20) (n := r) a1 (by omega)
  have h3 := VB.natP (t := (4 : Fin 21)) (c := 20) (by decide) (s) a2 (by omega)
  have a3 := natB_le (t := (4 : Fin 21)) (c := 20) (n := s) a2 (by omega)
  have h4 := VB.natP (t := (5 : Fin 21)) (c := 20) (by decide) (m) a3 (by omega)
  have a4 := natB_le (t := (5 : Fin 21)) (c := 20) (n := m) a3 (by omega)
  have h5 := VB.natP (t := (6 : Fin 21)) (c := 20) (by decide) (Z) a4 (by omega)
  have a5 := natB_le (t := (6 : Fin 21)) (c := 20) (n := Z) a4 (by omega)
  have h6 := VB.natP (t := (7 : Fin 21)) (c := 20) (by decide) (m * (s * (r * B) + Z)) a5 (by omega)
  have a6 := natB_le (t := (7 : Fin 21)) (c := 20) (n := m * (s * (r * B) + Z)) a5 (by omega)
  have hl := vb_leafClear (M := M) (j := 2) check_trP [M, B, r, s, m, Z, m * (s * (r * B) + Z)] rfl trU_inj a6 (fun i => by
      fin_cases i <;> simp [natB, zv, trU, σTr, aGet, pEval_vv, pEval_pTop, top, T])
    (scrFrom 21 2) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq hl)))))).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 21 2).length = 19 := rfl
  rw [e, timeTrB]
  simp only [wTrZ, pEval, mEval, List.headD, List.tail]
  ring

/-! ### Selection by bits -/

def selU : Fin 13 → Fin 14 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
theorem selU_inj : Function.Injective selU := by decide

/-- **Blocks selected by bits** (`selW`), with their templates. -/
def selB (n B : ℕ) : XProg 14 :=
  seq (natP 4 13 B) <| seq (natP 5 13 n) <| seq (natP 6 13 (n * B)) <|
  seq (prog (Prog.map selU Prog.bitSelP)) <| clearL (scrFrom 14 4)

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
  fin_cases t <;> simp [selU, hS, mem_scrFrom]

def sizeSelB (n B : ℕ) : ℕ := B + n + n * B

/-- The time of `selB` from tapes below `M` (scratch blank). -/
def timeSelB (n B M : ℕ) : ℕ :=
  (2 * (B) + 1) * (4 * M + 12) + ((2 * (n) + 1) * (4 * M + 12) + ((2 * (n * B) + 1) * (4 * M + 12) + ((2 * M + 3) * (5 + 9 * n + 6 * B * n) + ((10 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))))))

open SigabaNeo.Tape.Sym Prog.SpecZ Prog.SpecT in
theorem ub_selB (n B M : ℕ) (hM : sizeSelB n B ≤ M) :
    UBZ 4 (selB n B) M (timeSelB n B M) M := by
  unfold sizeSelB at hM
  have a0 := zv_le (k := 14) 4 M
  have h1 := VB.natP (t := (4 : Fin 14)) (c := 13) (by decide) (B) a0 (by omega)
  have a1 := natB_le (t := (4 : Fin 14)) (c := 13) (n := B) a0 (by omega)
  have h2 := VB.natP (t := (5 : Fin 14)) (c := 13) (by decide) (n) a1 (by omega)
  have a2 := natB_le (t := (5 : Fin 14)) (c := 13) (n := n) a1 (by omega)
  have h3 := VB.natP (t := (6 : Fin 14)) (c := 13) (by decide) (n * B) a2 (by omega)
  have a3 := natB_le (t := (6 : Fin 14)) (c := 13) (n := n * B) a2 (by omega)
  have hl := vb_leafClear (M := M) (j := 4) check_bitSelP [M, B, n, n * B] rfl selU_inj a3 (fun i => by
      fin_cases i <;> simp [natB, zv, selU, σSel, aGet, pEval_vv, pEval_pTop, top, T])
    (scrFrom 14 4) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq (h3.seq hl))).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 14 4).length = 10 := rfl
  rw [e, timeSelB]
  simp only [wSel, pEval, mEval, List.headD, List.tail]
  ring

/-! ### Sums selected by bits -/

def hashU : Fin 45 → Fin 46 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
  44]
theorem hashU_inj : Function.Injective hashU := by decide

/-- **Sums selected by bits** (`hashW`), with their templates. -/
def hashB (P d N K : ℕ) : XProg 46 :=
  seq (natP 4 45 K) <| seq (natP 5 45 N) <| seq (natP 6 45 (N * K)) <| seq (natP 7 45 d) <|
  seq (natP 8 45 P) <| seq (natP 9 45 (P * (N * K))) <|
  seq (prog (Prog.map hashU Prog.hashP)) <| clearL (scrFrom 46 4)

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
  fin_cases t <;> simp [hashU, hS, mem_scrFrom]

def sizeHashB (P d N K : ℕ) : ℕ := K + N + N * K + d + P + P * (N * K)

/-- The time of `hashB` from tapes below `M` (scratch blank). -/
def timeHashB (P d N K M : ℕ) : ℕ :=
  (2 * (K) + 1) * (4 * M + 12) + ((2 * (N) + 1) * (4 * M + 12) + ((2 * (N * K) + 1) * (4 * M + 12) + ((2 * (d) + 1) * (4 * M + 12) + ((2 * (P) + 1) * (4 * M + 12) + ((2 * (P * (N * K)) + 1) * (4 * M + 12) + ((2 * M + 3) * (7 + 23 * P + 18 * d * P + 6 * (N * K) * d * P + 28 * N * d * P + 29 * N * K * d * P + 12 * (N * K) * P + 28 * N * P + 29 * N * K * P) + ((42 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)))))))))

open SigabaNeo.Tape.Sym Prog.SpecZ Prog.SpecT in
theorem ub_hashB (P d N K M : ℕ) (hM : sizeHashB P d N K ≤ M) :
    UBZ 4 (hashB P d N K) M (timeHashB P d N K M) M := by
  unfold sizeHashB at hM
  have a0 := zv_le (k := 46) 4 M
  have h1 := VB.natP (t := (4 : Fin 46)) (c := 45) (by decide) (K) a0 (by omega)
  have a1 := natB_le (t := (4 : Fin 46)) (c := 45) (n := K) a0 (by omega)
  have h2 := VB.natP (t := (5 : Fin 46)) (c := 45) (by decide) (N) a1 (by omega)
  have a2 := natB_le (t := (5 : Fin 46)) (c := 45) (n := N) a1 (by omega)
  have h3 := VB.natP (t := (6 : Fin 46)) (c := 45) (by decide) (N * K) a2 (by omega)
  have a3 := natB_le (t := (6 : Fin 46)) (c := 45) (n := N * K) a2 (by omega)
  have h4 := VB.natP (t := (7 : Fin 46)) (c := 45) (by decide) (d) a3 (by omega)
  have a4 := natB_le (t := (7 : Fin 46)) (c := 45) (n := d) a3 (by omega)
  have h5 := VB.natP (t := (8 : Fin 46)) (c := 45) (by decide) (P) a4 (by omega)
  have a5 := natB_le (t := (8 : Fin 46)) (c := 45) (n := P) a4 (by omega)
  have h6 := VB.natP (t := (9 : Fin 46)) (c := 45) (by decide) (P * (N * K)) a5 (by omega)
  have a6 := natB_le (t := (9 : Fin 46)) (c := 45) (n := P * (N * K)) a5 (by omega)
  have hl := vb_leafClear (M := M) (j := 4) check_hashP [M, N, K, N * K, d, P, P * (N * K)] rfl hashU_inj a6 (fun i => by
      fin_cases i <;> simp [natB, zv, hashU, σHash, aGet, pEval_vv, pEval_pTop, top, T])
    (scrFrom 46 4) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq hl)))))).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 46 4).length = 42 := rfl
  rw [e, timeHashB]
  simp only [wHashZ, pEval, mEval, List.headD, List.tail]
  ring

/-! ### Matrix products -/

def mmU : Fin 59 → Fin 60 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43,
  44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
theorem mmU_inj : Function.Injective mmU := by decide

/-- **The product of matrix words** (`matMulW`), with its templates. -/
def mmB (m n l N K : ℕ) : XProg 60 :=
  seq (natP 3 59 K) <| seq (natP 4 59 N) <| seq (natP 5 59 (N * K)) <| seq (natP 6 59 m) <|
  seq (natP 7 59 n) <| seq (natP 8 59 l) <| seq (natP 9 59 (m * l * (N * K))) <|
  seq (prog (Prog.map mmU Prog.matMulP)) <| clearL (scrFrom 60 3)

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
  fin_cases t <;> simp [mmU, hS, mem_scrFrom]

def sizeMmB (m n l N K : ℕ) : ℕ := K + N + N * K + m + n + l + m * l * (N * K)

/-- The time of `mmB` from tapes below `M` (scratch blank). -/
def timeMmB (m n l N K M : ℕ) : ℕ :=
  (2 * (K) + 1) * (4 * M + 12) + ((2 * (N) + 1) * (4 * M + 12) + ((2 * (N * K) + 1) * (4 * M + 12) + ((2 * (m) + 1) * (4 * M + 12) + ((2 * (n) + 1) * (4 * M + 12) + ((2 * (l) + 1) * (4 * M + 12) + ((2 * (m * l * (N * K)) + 1) * (4 * M + 12) + ((2 * M + 3) * (m * n * l * (22 * N ^ 2 * K ^ 2 + 97 * N ^ 2 * K + 61 * N ^ 2 + 105 * (N * K) + 117 * N + 23 * K + 73) + m * n * l ^ 2 * (3 * (N * K) + 4) + m * n * (3 * (N * K) + 4) + m * l * (9 * (N * K) + 15) + 8 * m + 5) + ((57 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))))))))))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
open SigabaNeo.Tape.Sym Prog.SpecZ Prog.SpecT in
theorem ub_mmB (m n l N K M : ℕ) (hM : sizeMmB m n l N K ≤ M) :
    UBZ 3 (mmB m n l N K) M (timeMmB m n l N K M) M := by
  unfold sizeMmB at hM
  have a0 := zv_le (k := 60) 3 M
  have h1 := VB.natP (t := (3 : Fin 60)) (c := 59) (by decide) (K) a0 (by omega)
  have a1 := natB_le (t := (3 : Fin 60)) (c := 59) (n := K) a0 (by omega)
  have h2 := VB.natP (t := (4 : Fin 60)) (c := 59) (by decide) (N) a1 (by omega)
  have a2 := natB_le (t := (4 : Fin 60)) (c := 59) (n := N) a1 (by omega)
  have h3 := VB.natP (t := (5 : Fin 60)) (c := 59) (by decide) (N * K) a2 (by omega)
  have a3 := natB_le (t := (5 : Fin 60)) (c := 59) (n := N * K) a2 (by omega)
  have h4 := VB.natP (t := (6 : Fin 60)) (c := 59) (by decide) (m) a3 (by omega)
  have a4 := natB_le (t := (6 : Fin 60)) (c := 59) (n := m) a3 (by omega)
  have h5 := VB.natP (t := (7 : Fin 60)) (c := 59) (by decide) (n) a4 (by omega)
  have a5 := natB_le (t := (7 : Fin 60)) (c := 59) (n := n) a4 (by omega)
  have h6 := VB.natP (t := (8 : Fin 60)) (c := 59) (by decide) (l) a5 (by omega)
  have a6 := natB_le (t := (8 : Fin 60)) (c := 59) (n := l) a5 (by omega)
  have h7 := VB.natP (t := (9 : Fin 60)) (c := 59) (by decide) (m * l * (N * K)) a6 (by omega)
  have a7 := natB_le (t := (9 : Fin 60)) (c := 59) (n := m * l * (N * K)) a6 (by omega)
  have hl := vb_leafClear (M := M) (j := 3) check_matMulP [M, N, K, m, n, l] rfl mmU_inj a7 (fun i => by
      fin_cases i <;> simp [natB, zv, mmU, σMatZ, aGet, pEval_vv, pEval_pTop, top, T, pK, pN, pNK, pm, pn, pl, pmlNK, mo, pEval, mEval] <;>
        ring_nf <;> exact le_rfl)
    (scrFrom 60 3) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq hl))))))).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 60 3).length = 57 := rfl
  rw [e, timeMmB]
  simp [Prog.SpecT.wMat, pEval, mEval]
  ring

/-! ### Entrywise sums and differences -/

def adU : Fin 28 → Fin 29 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20, 21, 22, 23, 24, 25, 26, 27]
theorem adU_inj : Function.Injective adU := by decide

/-- **Entrywise sum of `L` ring entries** (`matAddW`), with its templates. -/
def addB (L N K : ℕ) : XProg 29 :=
  seq (natP 3 28 K) <| seq (natP 4 28 (L * N)) <| seq (prog (Prog.map adU Prog.addRWP)) <|
  clearL (scrFrom 29 3)

/-- **Entrywise difference of `L` ring entries** (`matSubW`), with its templates. -/
def subB (L N K : ℕ) : XProg 29 :=
  seq (natP 3 28 K) <| seq (natP 4 28 (L * N)) <| seq (prog (Prog.map adU Prog.subRWP)) <|
  clearL (scrFrom 29 3)

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
  fin_cases t <;> simp [adU, hS, mem_scrFrom]

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
  fin_cases t <;> simp [adU, hS, mem_scrFrom]

def sizeAddB (L N K : ℕ) : ℕ := K + L * N

/-- The time of `addB` from tapes below `M` (scratch blank). -/
def timeAddB (L N K M : ℕ) : ℕ :=
  (2 * (K) + 1) * (4 * M + 12) + ((2 * (L * N) + 1) * (4 * M + 12) + ((2 * M + 3) * (7 + 28 * (L * N) + 29 * (L * N) * K) + ((26 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)))))

open SigabaNeo.Tape.Sym Prog.SpecZ Prog.SpecT in
theorem ub_addB (L N K M : ℕ) (hM : sizeAddB L N K ≤ M) :
    UBZ 3 (addB L N K) M (timeAddB L N K M) M := by
  unfold sizeAddB at hM
  have a0 := zv_le (k := 29) 3 M
  have h1 := VB.natP (t := (3 : Fin 29)) (c := 28) (by decide) (K) a0 (by omega)
  have a1 := natB_le (t := (3 : Fin 29)) (c := 28) (n := K) a0 (by omega)
  have h2 := VB.natP (t := (4 : Fin 29)) (c := 28) (by decide) (L * N) a1 (by omega)
  have a2 := natB_le (t := (4 : Fin 29)) (c := 28) (n := L * N) a1 (by omega)
  have hl := vb_leafClear (M := M) (j := 3) check_addRWP [M, L * N, K] rfl adU_inj a2 (fun i => by
      fin_cases i <;> simp [natB, zv, adU, σAdd, aGet, pEval_vv, pEval_pTop, top, T])
    (scrFrom 29 3) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq hl)).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 29 3).length = 26 := rfl
  rw [e, timeAddB]
  simp only [wAdd, pEval, mEval, List.headD, List.tail]
  ring

/-- The time of `subB` from tapes below `M` (scratch blank). -/
def timeSubB (L N K M : ℕ) : ℕ :=
  (2 * (K) + 1) * (4 * M + 12) + ((2 * (L * N) + 1) * (4 * M + 12) + ((2 * M + 3) * (7 + 28 * (L * N) + 29 * (L * N) * K) + ((26 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)))))

open SigabaNeo.Tape.Sym Prog.SpecZ Prog.SpecT in
theorem ub_subB (L N K M : ℕ) (hM : sizeAddB L N K ≤ M) :
    UBZ 3 (subB L N K) M (timeSubB L N K M) M := by
  unfold sizeAddB at hM
  have a0 := zv_le (k := 29) 3 M
  have h1 := VB.natP (t := (3 : Fin 29)) (c := 28) (by decide) (K) a0 (by omega)
  have a1 := natB_le (t := (3 : Fin 29)) (c := 28) (n := K) a0 (by omega)
  have h2 := VB.natP (t := (4 : Fin 29)) (c := 28) (by decide) (L * N) a1 (by omega)
  have a2 := natB_le (t := (4 : Fin 29)) (c := 28) (n := L * N) a1 (by omega)
  have hl := vb_leafClear (M := M) (j := 3) check_subRWP [M, L * N, K] rfl adU_inj a2 (fun i => by
      fin_cases i <;> simp [natB, zv, adU, σAdd, aGet, pEval_vv, pEval_pTop, top, T])
    (scrFrom 29 3) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq hl)).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 29 3).length = 26 := rfl
  rw [e, timeSubB]
  simp only [wAdd, pEval, mEval, List.headD, List.tail]
  ring

/-! ### Fields of a word -/

def getU : Fin 10 → Fin 11 := ![2, 0, 3, 1, 4, 5, 6, 7, 8, 9]
theorem getU_inj : Function.Injective getU := by decide

/-- **The field of length `L` at the offset `o`** of the word on tape `1`. -/
def getB (o L : ℕ) : XProg 11 :=
  seq (natP 4 10 o) <| seq (natP 5 10 L) <| seq (prog (Prog.map getU Prog.splitP)) <|
    clearL (scrFrom 11 2)

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
  fin_cases t <;> simp [getU, hS, takeD, mem_scrFrom]

/-- The time of `getB` from tapes below `M` (scratch blank). -/
def timeGetB (o L M : ℕ) : ℕ :=
  (2 * o + 1) * (4 * M + 12) + ((2 * L + 1) * (4 * M + 12) +
    ((2 * M + 3) * (11 + 6 * o + 6 * L) + (9 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))))

open SigabaNeo.Tape.Sym Prog.SpecZ in
theorem ub_getB (o L M : ℕ) (hM : o + L ≤ M) : UBZ 2 (getB o L) M (timeGetB o L M) M := by
  have h1 := VB.natP (t := (4 : Fin 11)) (c := 10) (by decide) o (zv_le 2 M) (by omega)
  have a1 := natB_le (t := (4 : Fin 11)) (c := 10) (n := o) (zv_le 2 M) (by omega)
  have h2 := VB.natP (t := (5 : Fin 11)) (c := 10) (by decide) L a1 (by omega)
  have a2 := natB_le (t := (5 : Fin 11)) (c := 10) (n := L) a1 (by omega)
  have h3 := vb_leafClear (M := M) (j := 2) check_splitP [M, o, L] rfl getU_inj a2 (fun i => by
      fin_cases i <;> simp [natB, zv, getU, σSplit, aGet, pEval_vv, pEval_pTop, top, T])
    (scrFrom 11 2) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq h3)).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 11 2).length = 9 := rfl
  rw [e, timeGetB]
  simp only [wSplit, pEval, mEval, List.headD, List.tail]
  ring

/-! ### Joins -/

def joinU : Fin 11 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
theorem joinU_inj : Function.Injective joinU := by decide

/-- **The join of three words**, cut to the lengths `a`, `b`, `c`. -/
def joinB (a b c : ℕ) : XProg 12 :=
  seq (natP 4 11 a) <| seq (natP 5 11 b) <| seq (natP 6 11 c) <| seq (natP 7 11 (a + b + c)) <|
  seq (prog (Prog.map joinU Prog.joinP)) <| clearL (scrFrom 12 4)

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
  fin_cases t <;> simp [joinU, hS, mem_scrFrom]

/-- The time of `joinB` from tapes below `M` (scratch blank). -/
def timeJoinB (a b c M : ℕ) : ℕ :=
  (2 * (a) + 1) * (4 * M + 12) + ((2 * (b) + 1) * (4 * M + 12) + ((2 * (c) + 1) * (4 * M + 12) + ((2 * (a + b + c) + 1) * (4 * M + 12) + ((2 * M + 3) * (11 + 6 * a + 6 * b + 6 * c) + ((8 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3)))))))

open SigabaNeo.Tape.Sym Prog.SpecZ Prog.SpecT in
theorem ub_joinB (a b c M : ℕ) (hM : a + b + c ≤ M) :
    UBZ 4 (joinB a b c) M (timeJoinB a b c M) M := by
  have a0 := zv_le (k := 12) 4 M
  have h1 := VB.natP (t := (4 : Fin 12)) (c := 11) (by decide) (a) a0 (by omega)
  have a1 := natB_le (t := (4 : Fin 12)) (c := 11) (n := a) a0 (by omega)
  have h2 := VB.natP (t := (5 : Fin 12)) (c := 11) (by decide) (b) a1 (by omega)
  have a2 := natB_le (t := (5 : Fin 12)) (c := 11) (n := b) a1 (by omega)
  have h3 := VB.natP (t := (6 : Fin 12)) (c := 11) (by decide) (c) a2 (by omega)
  have a3 := natB_le (t := (6 : Fin 12)) (c := 11) (n := c) a2 (by omega)
  have h4 := VB.natP (t := (7 : Fin 12)) (c := 11) (by decide) (a + b + c) a3 (by omega)
  have a4 := natB_le (t := (7 : Fin 12)) (c := 11) (n := a + b + c) a3 (by omega)
  have hl := vb_leafClear (M := M) (j := 4) check_joinP [M, a, b, c, a + b + c] rfl joinU_inj a4 (fun i => by
      fin_cases i <;> simp [natB, zv, joinU, σJoin, aGet, pEval_vv, pEval_pTop, top, T])
    (scrFrom 12 4) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq (h3.seq (h4.seq hl)))).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 12 4).length = 8 := rfl
  rw [e, timeJoinB]
  simp only [wJoin, pEval, mEval, List.headD, List.tail]
  ring

/-! ### The gadget row and the word of `1` -/

def gadU : Fin 21 → Fin 22 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18,
  19, 20]
theorem gadU_inj : Function.Injective gadU := by decide

/-- **The gadget row `G̲`** (`gadW`), with its templates. -/
def gadB (N K k : ℕ) : XProg 22 :=
  seq (natP 1 21 K) <| seq (natP 2 21 N) <| seq (natP 3 21 (N * K)) <| seq (natP 4 21 k) <|
  seq (natP 5 21 (2 * k * (N * K))) <| seq (prog (Prog.map gadU Prog.gadP)) <| clearL (scrFrom 22 1)

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
  fin_cases t <;> simp [gadU, hS, mem_scrFrom]

def sizeGadB (N K k : ℕ) : ℕ := K + N + N * K + k + 2 * k * (N * K)

/-- The time of `gadB` from tapes below `M` (scratch blank). -/
def timeGadB (N K k M : ℕ) : ℕ :=
  (2 * (K) + 1) * (4 * M + 12) + ((2 * (N) + 1) * (4 * M + 12) + ((2 * (N * K) + 1) * (4 * M + 12) + ((2 * (k) + 1) * (4 * M + 12) + ((2 * (2 * k * (N * K)) + 1) * (4 * M + 12) + ((2 * M + 3) * (24 + 11 * K + 34 * k + 9 * N * k + 6 * N * K * k + 9 * (N * K) * k + 11 * K * k) + ((21 * (2 * (M + 1) + 3) + (2 * (M + 1) + 3))))))))

open SigabaNeo.Tape.Sym Prog.SpecZ Prog.SpecT in
theorem ub_gadB (N K k M : ℕ) (hM : sizeGadB N K k ≤ M) :
    UBZ 1 (gadB N K k) M (timeGadB N K k M) M := by
  unfold sizeGadB at hM
  have a0 := zv_le (k := 22) 1 M
  have h1 := VB.natP (t := (1 : Fin 22)) (c := 21) (by decide) (K) a0 (by omega)
  have a1 := natB_le (t := (1 : Fin 22)) (c := 21) (n := K) a0 (by omega)
  have h2 := VB.natP (t := (2 : Fin 22)) (c := 21) (by decide) (N) a1 (by omega)
  have a2 := natB_le (t := (2 : Fin 22)) (c := 21) (n := N) a1 (by omega)
  have h3 := VB.natP (t := (3 : Fin 22)) (c := 21) (by decide) (N * K) a2 (by omega)
  have a3 := natB_le (t := (3 : Fin 22)) (c := 21) (n := N * K) a2 (by omega)
  have h4 := VB.natP (t := (4 : Fin 22)) (c := 21) (by decide) (k) a3 (by omega)
  have a4 := natB_le (t := (4 : Fin 22)) (c := 21) (n := k) a3 (by omega)
  have h5 := VB.natP (t := (5 : Fin 22)) (c := 21) (by decide) (2 * k * (N * K)) a4 (by omega)
  have a5 := natB_le (t := (5 : Fin 22)) (c := 21) (n := 2 * k * (N * K)) a4 (by omega)
  have hl := vb_leafClear (M := M) (j := 1) check_gadP [M, N, K, N * K, k, 2 * k * (N * K)] rfl gadU_inj a5 (fun i => by
      fin_cases i <;> simp [natB, zv, gadU, Prog.SpecZ.σGad, aGet, pEval_vv, pEval_pTop, top, T])
    (scrFrom 22 1) (fun t ht => (mem_scrFrom t).2 ht)
  refine (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq hl))))).mono le_rfl (le_of_eq ?_) le_rfl
  have e : (scrFrom 22 1).length = 21 := rfl
  rw [e, timeGadB]
  simp only [wGadZ, pEval, mEval, List.headD, List.tail]
  ring

/-- **The word of `1`**: a leading `1`, then `N K − 1` zeros. -/
def oneB (N K : ℕ) : XProg 2 :=
  seq (natP 0 1 (N * K - 1)) (seq (prog (.prim (.cons 0 true))) (prog (.prim (.clear 1))))

theorem wf_oneB (N K : ℕ) : (oneB N K).WF := ⟨wf_natP (by decide) _, trivial, trivial⟩

theorem law_oneB (N K : ℕ) (hN : 0 < N) (hK : 0 < K) (S : Store 2) (hS : S 1 = []) :
    (oneB N K).law S = PMF.pure (Function.update S 0 (oneW N K)) := by
  unfold oneB
  rw [law_seq, law_natP (by decide) _ _ hS, PMF.pure_bind, law_seq, law_prim, PMF.pure_bind,
    law_prim, oneW_eq hN hK]
  congr 1
  funext t
  fin_cases t <;> simp [Prim.apply, hS]

/-- The time of `oneB` from tapes below `M` (scratch blank). -/
def timeOneB (N K M : ℕ) : ℕ :=
  (2 * (N * K - 1) + 1) * (4 * M + 12) + ((2 * (M + 1) + 3) + (2 * (M + 1) + 3))

theorem ub_oneB (N K M : ℕ) (hM : N * K ≤ M) (h1 : 1 ≤ M) :
    UBZ 1 (oneB N K) M (timeOneB N K M) M := by
  have a0 := zv_le (k := 2) 1 M
  have h2 := VB.natP (t := (0 : Fin 2)) (c := 1) (by decide) (N * K - 1) a0 (by omega)
  have a2 := natB_le (t := (0 : Fin 2)) (c := 1) (n := N * K - 1) a0 (by omega)
  have h3 := VB.prim (.cons (0 : Fin 2) true) a2
  have h4 := VB.prim (M := M) (.clear (1 : Fin 2)) (a := (Prim.cons 0 true).lenT (natB 0 1 (N * K - 1) (zv 1 M)))
    (fun i => by
      simp only [Prim.lenT, natB, zv, Function.update_apply]; split_ifs <;> simp_all <;> omega)
  refine (h2.seq (h3.seq h4)).mono le_rfl (le_of_eq (by unfold timeOneB; ring)) fun i => ?_
  simp only [Prim.lenT, natB, zv, Function.update_apply]; split_ifs <;> simp_all <;> omega

end AdvancedEncryption.DualUse.Prog
