import SigabaNeoStd.Machines.Pack.MachineT
import SigabaNeoStd.Machines.Prog.FrameSize

/-!
# The state count of the packed machine

* `card_getPh_le`: a read of segment `j` has at most `12 j + 32` states;
* `card_putPh_le`: a replacement at most `24 j + 182`;
* **`card_tr_le`**: the translation of `p` has at most `stA w K * XProg.size p` states, where
  `XProg.size p` is the state count of the old compiled machine (`XProg.card_state`) and
  `stA w K = w * (36 K + 214) + 12 K + 143`;
* **`states_packMachineT_le`**: the packed machine has at most
  `stA w K * (size p + 3K + 2) + 36K + 200` states.
-/

namespace SigabaNeo.Tape.Pack

open Cslib Function Turing MultiTapeTM

variable {K w D : ℕ}

/-! ### Cards of the phases -/

theorem card_markWork : Fintype.card MarkWorkState = 2 := by decide
theorem card_rewind : Fintype.card RewindState = 2 := by decide
theorem card_rewindWork : Fintype.card RewindWorkState = 2 := rfl

theorem card_getPh_le {k : ℕ} (j : ℕ) (t st fl : Fin k) :
    Fintype.card (getPh j t st fl).State ≤ 12 * j + 32 := by
  unfold getPh
  split_ifs
  · refine (Fintype.card_congr (Equiv.refl _)).trans_le ?_
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_bool,
      Fintype.card_fin, card_markWork, card_rewind, card_rewindWork]
    omega
  · show Fintype.card Unit ≤ _
    simp

theorem card_putTail : Fintype.card putTail.State = 108 := by
  rw [Prog.card_state]; rfl

theorem card_putPh_le {k : ℕ} (j : ℕ) (t st fl B : Fin k) :
    Fintype.card (putPh j t st fl B).State ≤ 24 * j + 182 := by
  unfold putPh
  split_ifs
  · refine (Fintype.card_congr (Equiv.refl _)).trans_le ?_
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_bool,
      Fintype.card_fin, Fintype.card_unit, card_markWork, card_rewind, card_rewindWork,
      card_putTail]
    omega
  · show Fintype.card Unit ≤ _
    simp

/-! ### Cards of the constructs -/

namespace ZProg

variable {c : ℕ}

theorem card_xp (p : XProg c) : Fintype.card (ZProg.xp p).State = p.size :=
  (Fintype.card_congr (Equiv.refl _)).trans (XProg.card_state p)

theorem card_ph (P : Phase c) : Fintype.card (ZProg.ph P).State = Fintype.card P.State :=
  Fintype.card_congr (Equiv.refl _)

theorem card_seq (p q : ZProg c) :
    Fintype.card (ZProg.seq p q).State = Fintype.card p.State + Fintype.card q.State := by
  rw [show Fintype.card (ZProg.seq p q).State = Fintype.card (p.State ⊕ q.State) from
    Fintype.card_congr (Equiv.refl _), Fintype.card_sum]

theorem card_ifBlank (i : Fin c) (p q : ZProg c) :
    Fintype.card (ZProg.ifBlank i p q).State = Fintype.card p.State + Fintype.card q.State + 1 := by
  rw [show Fintype.card (ZProg.ifBlank i p q).State = Fintype.card (Option (q.State ⊕ p.State))
    from Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum]
  ring

theorem card_ifBit (i : Fin c) (p q : ZProg c) :
    Fintype.card (ZProg.ifBit i p q).State = Fintype.card p.State + Fintype.card q.State + 1 := by
  rw [show Fintype.card (ZProg.ifBit i p q).State = Fintype.card (Option (p.State ⊕ q.State))
    from Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum]

theorem card_loop (i : Fin c) (b : ZProg c) :
    Fintype.card (ZProg.loop i b).State = Fintype.card b.State + 39 := by
  rw [show Fintype.card (ZProg.loop i b).State =
      Fintype.card (Option (((CQ (tailSpec i).e ⊕ b.State) ⊕ Unit) ⊕ Unit)) from
    Fintype.card_congr (Equiv.refl _), Fintype.card_option, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_sum, card_CQ, Fintype.card_unit]
  simp only [tailSpec, bwdSpec]
  ring

end ZProg

theorem card_seqL_ph {c : ℕ} (Ps : List (Phase c)) (q : ZProg c) :
    Fintype.card (seqL (Ps.map ZProg.ph) q).State =
      (Ps.map fun P => Fintype.card P.State).sum + Fintype.card q.State := by
  induction Ps with
  | nil => simp [seqL]
  | cons P Ps ih =>
    simp only [List.map_cons, seqL, List.sum_cons]
    rw [ZProg.card_seq, ZProg.card_ph, ih]
    ring

theorem sum_map_le {α : Type} (l : List α) (f : α → ℕ) (B : ℕ) (h : ∀ a ∈ l, f a ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h a List.mem_cons_self
    have := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    nlinarith

/-! ### Sizes are positive -/

theorem Prog.one_le_size {k : ℕ} : ∀ p : Prog k, 1 ≤ p.size
  | .prim _ => by simp only [Prog.size]; omega
  | .coin _ => by simp [Prog.size]
  | .seq p _ | .ifBlank _ p _ | .ifBit _ p _ => by
    have := Prog.one_le_size p; simp only [Prog.size]; omega
  | .loop _ _ => by simp [Prog.size]

theorem XProg.one_le_size : ∀ {k : ℕ} (p : XProg k), 1 ≤ p.size
  | _, .prog p => Prog.one_le_size p
  | _, .frame _ p => XProg.one_le_size p
  | _, .seq p _ | _, .ifBlank _ p _ | _, .ifBit _ p _ => by
    have := XProg.one_le_size p; simp only [XProg.size]; omega
  | _, .loop _ _ => by simp [XProg.size]

theorem Prog.size_localize {k : ℕ} (l : List (Fin k)) (hl0 : 0 < l.length) (q : Prog k) :
    (Prog.localize l hl0 q).size = q.size := Prog.size_map _ q

/-! ### The translation -/

/-- The factor of the state count of the translation. -/
def stA (w K : ℕ) : ℕ := w * (36 * K + 214) + 12 * K + 143

theorem card_skipZ : Fintype.card (skipZ (lay := packLayout w D)).State = 36 := by
  rw [skipZ, ZProg.card_xp]; rfl

theorem card_clrT : Fintype.card (clrT (packLayout w D)).State = 36 := by
  rw [clrT, ZProg.card_xp]; rfl

theorem card_leaf_le {m : ℕ} (σ : Fin m ↪ Fin K) (h : m ≤ w) (p : XProg m) :
    Fintype.card (leaf (packLayout w D) (packKit K w D) σ h p).State ≤ stA w K * p.size := by
  have hs := XProg.one_le_size p
  unfold leaf
  have hg : ((List.finRange m).map fun j =>
      ZProg.ph ((packKit K w D).get (σ j) (wsE (packLayout w D) h j))) =
      ((List.finRange m).map fun j => (packKit K w D).get (σ j) (wsE (packLayout w D) h j)).map
        ZProg.ph := by simp [List.map_map]
  have hp' : ((List.finRange m).map fun j =>
      ZProg.ph ((packKit K w D).put (σ j) (wsE (packLayout w D) h j))) =
      ((List.finRange m).map fun j => (packKit K w D).put (σ j) (wsE (packLayout w D) h j)).map
        ZProg.ph := by simp [List.map_map]
  rw [hg, card_seqL_ph, ZProg.card_seq, ZProg.card_xp, hp', card_seqL_ph, card_skipZ,
    XProg.size_frame, List.map_map, List.map_map]
  have h1 := sum_map_le ((List.finRange m)) ((fun P : Phase _ => Fintype.card P.State) ∘
    fun j => (packKit K w D).get (σ j) (wsE (packLayout w D) h j)) (12 * K + 32) (fun j _ =>
      (card_getPh_le _ _ _ _).trans (by have := (σ j).isLt; omega))
  have h2 := sum_map_le ((List.finRange m)) ((fun P : Phase _ => Fintype.card P.State) ∘
    fun j => (packKit K w D).put (σ j) (wsE (packLayout w D) h j)) (24 * K + 182) (fun j _ =>
      (card_putPh_le _ _ _ _ _).trans (by have := (σ j).isLt; omega))
  simp only [List.length_finRange] at h1 h2
  have h3 : m * (12 * K + 32) + m * (24 * K + 182) ≤ w * (36 * K + 214) := by
    have := Nat.mul_le_mul_right (36 * K + 214) h
    nlinarith
  have h4 : stA w K * p.size = stA w K * (p.size - 1) + stA w K := by
    rw [← Nat.mul_add_one]; congr 1; omega
  have h5 : p.size ≤ stA w K * (p.size - 1) + 1 := by
    have : 1 ≤ stA w K := by simp [stA]
    have := Nat.mul_le_mul_right (p.size - 1) this
    omega
  rw [h4]
  simp only [stA] at h5 ⊢
  omega

theorem card_leafP_le {k : ℕ} (σ : Fin k ↪ Fin K) (q : Prog k) (h : NarrowP w q) :
    Fintype.card (leafP (packLayout w D) (packKit K w D) σ q h).State ≤ stA w K * q.size := by
  have := card_leaf_le (D := D) ((Prog.listEmb _ (List.nodup_dedup _)).trans σ) h.1
    (XProg.prog (Prog.localize _ h.2 q))
  rwa [XProg.size_prog, Prog.size_localize] at this

theorem card_testZ_le (j : Fin K) (bit : Bool) (p q : ZProg (5 + w + D)) :
    Fintype.card (testZ (packLayout w D) (packKit K w D) j bit p q).State ≤
      Fintype.card p.State + Fintype.card q.State + (12 * K + 105) := by
  have hg := card_getPh_le (k := 5 + w + D) j (packLayout w D).T (packLayout w D).st (flT w D)
  have hj := j.isLt
  cases bit <;>
  · simp only [testZ, ZProg.card_seq, ZProg.card_ph, ZProg.card_ifBlank, ZProg.card_ifBit,
      card_clrT, Bool.false_eq_true, ↓reduceIte]
    show Fintype.card (getPh j _ _ _).State + _ ≤ _
    omega

theorem card_loopAt_le (j : Fin K) (d : ℕ) (b : ZProg (5 + w + D)) :
    Fintype.card (loopAt (packLayout w D) (packKit K w D) j d b).State ≤
      Fintype.card b.State + (48 * K + 321) := by
  have hj := j.isLt
  unfold loopAt
  split_ifs with hd
  · have hg : Fintype.card ((packKit K w D).get j ((packLayout w D).F ⟨d, hd⟩)).State ≤
        12 * j + 32 := card_getPh_le _ _ _ _
    have hg' : Fintype.card ((packKit K w D).get j (packLayout w D).T).State ≤ 12 * j + 32 :=
      card_getPh_le _ _ _ _
    have hp : Fintype.card ((packKit K w D).put j (packLayout w D).T).State ≤ 24 * j + 182 :=
      card_putPh_le _ _ _ _ _
    have ht : (XProg.prog (Prog.prim (Prim.tail (packLayout w D).T))).size = 36 := rfl
    rw [loopZ, ZProg.card_seq, ZProg.card_ph, ZProg.card_loop, ZProg.card_seq, tailZ,
      ZProg.card_seq, ZProg.card_ph, ZProg.card_seq, ZProg.card_xp, ZProg.card_ph, ht]
    omega
  · rw [card_skipZ]; omega

theorem stA_ge (w K : ℕ) : 12 * K + 106 ≤ stA w K ∧ 48 * K + 321 ≤ 39 * stA w K := by
  simp only [stA]; constructor <;> nlinarith

/-- **The state count of the translation of a plain program.** -/
theorem card_trP_le {k : ℕ} (σ : Fin k ↪ Fin K) :
    ∀ (d : ℕ) (q : Prog k),
      Fintype.card (trP (packLayout w D) (packKit K w D) σ d q).State ≤ stA w K * q.size
  | _, .prim a => by
    unfold trP orNarrow; split_ifs with h
    · exact card_leafP_le σ _ h
    · rw [card_skipZ]; have := stA_ge w K; simp only [Prog.size]; nlinarith
  | _, .coin i => by
    unfold trP orNarrow; split_ifs with h
    · exact card_leafP_le σ _ h
    · rw [card_skipZ]; have := stA_ge w K; simp only [Prog.size]; nlinarith
  | d, .seq p q => by
    unfold trP orNarrow; split_ifs with h
    · exact card_leafP_le σ _ h
    · rw [ZProg.card_seq]
      have := card_trP_le σ d p; have := card_trP_le σ d q
      simp only [Prog.size]; nlinarith
  | d, .ifBlank i p q => by
    unfold trP orNarrow; split_ifs with h
    · exact card_leafP_le σ _ h
    · have := card_testZ_le (σ i) false (trP (packLayout w D) (packKit K w D) σ d p)
        (trP (packLayout w D) (packKit K w D) σ d q)
      have := card_trP_le σ d p; have := card_trP_le σ d q; have := stA_ge w K
      simp only [Prog.size]; nlinarith
  | d, .ifBit i p q => by
    unfold trP orNarrow; split_ifs with h
    · exact card_leafP_le σ _ h
    · have := card_testZ_le (σ i) true (trP (packLayout w D) (packKit K w D) σ d p)
        (trP (packLayout w D) (packKit K w D) σ d q)
      have := card_trP_le σ d p; have := card_trP_le σ d q; have := stA_ge w K
      simp only [Prog.size]; nlinarith
  | d, .loop i b => by
    unfold trP orNarrow; split_ifs with h
    · exact card_leafP_le σ _ h
    · have := card_loopAt_le (σ i) d (trP (packLayout w D) (packKit K w D) σ (d + 1) b)
      have := card_trP_le σ (d + 1) b; have := stA_ge w K
      simp only [Prog.size]; nlinarith

/-- **The state count of the packing translation**: at most `stA w K` times the state count of
the old compiled machine. -/
theorem card_tr_le : ∀ {k : ℕ} (σ : Fin k ↪ Fin K) (d : ℕ) (p : XProg k),
    Fintype.card (tr (packLayout w D) (packKit K w D) σ d p).State ≤ stA w K * p.size
  | _, σ, d, .prog q => by
    unfold tr orLeaf; split_ifs with h
    · exact card_leaf_le σ h _
    · exact card_trP_le σ d q
  | _, σ, d, .frame e q => by
    unfold tr orLeaf; split_ifs with h
    · exact card_leaf_le σ h _
    · exact card_tr_le (e.trans σ) d q
  | _, σ, d, .seq p q => by
    unfold tr orLeaf; split_ifs with h
    · exact card_leaf_le σ h _
    · rw [ZProg.card_seq]
      have := card_tr_le σ d p; have := card_tr_le σ d q
      simp only [XProg.size]; nlinarith
  | _, σ, d, .ifBlank i p q => by
    unfold tr orLeaf; split_ifs with h
    · exact card_leaf_le σ h _
    · have := card_testZ_le (σ i) false (tr (packLayout w D) (packKit K w D) σ d p)
        (tr (packLayout w D) (packKit K w D) σ d q)
      have := card_tr_le σ d p; have := card_tr_le σ d q; have := stA_ge w K
      simp only [XProg.size]; nlinarith
  | _, σ, d, .ifBit i p q => by
    unfold tr orLeaf; split_ifs with h
    · exact card_leaf_le σ h _
    · have := card_testZ_le (σ i) true (tr (packLayout w D) (packKit K w D) σ d p)
        (tr (packLayout w D) (packKit K w D) σ d q)
      have := card_tr_le σ d p; have := card_tr_le σ d q; have := stA_ge w K
      simp only [XProg.size]; nlinarith
  | _, σ, d, .loop i b => by
    unfold tr orLeaf; split_ifs with h
    · exact card_leaf_le σ h _
    · have := card_loopAt_le (σ i) d (tr (packLayout w D) (packKit K w D) σ (d + 1) b)
      have := card_tr_le σ (d + 1) b; have := stA_ge w K
      simp only [XProg.size]; nlinarith

theorem size_snocN {k : ℕ} (o : Fin k) : ∀ n, (Prog.snocN o false n).size = 60 * n + 36
  | 0 => rfl
  | n + 1 => by
    rw [Prog.snocN, Prog.size, size_snocN o n]
    simp only [Prog.size, Prim.pad]
    ring

/-- **The state count of the packed machine.** -/
theorem states_packMachineT_le (p : XProg K) (i₀ o : Fin K) (n : ℕ) :
    (packMachineT w D p i₀ o n).states ≤ stA w K * p.size + 96 * K + 254 := by
  rw [states_packMachineT]
  have h1 := card_tr_le (w := w) (D := D) (Embedding.refl (Fin K)) 0 p
  have h2 := card_putPh_le (k := 5 + w + D) i₀ (ioT w D) (packLayout w D).st (flT w D) (bufT w D)
  have h3 := card_getPh_le (k := 5 + w + D) o (ioT w D) (packLayout w D).st (flT w D)
  have hs : (Prog.snocN (packLayout w D).st false K).size = 60 * K + 36 := size_snocN _ K
  have hi := i₀.isLt
  have ho := o.isLt
  have h2' : Fintype.card (putPh i₀ (ioT w D) (packLayout w D).st (flT w D) (bufT w D)).State ≤
      24 * K + 182 := h2.trans (by omega)
  have h3' : Fintype.card (getPh o (ioT w D) (packLayout w D).st (flT w D)).State ≤
      12 * K + 32 := h3.trans (by omega)
  show Fintype.card (ZProg.seq _ _).State + 4 ≤ _
  rw [ZProg.card_seq, ZProg.card_xp, XProg.size_prog, hs, ZProg.card_seq, ZProg.card_ph,
    ZProg.card_seq, ZProg.card_ph]
  omega

end SigabaNeo.Tape.Pack
