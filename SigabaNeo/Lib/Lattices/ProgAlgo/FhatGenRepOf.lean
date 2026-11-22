import SigabaNeo.Lib.Lattices.ProgAlgo.FhatGenBlock

/-!
# Generating gate tapes: the representations of the source wires

`oLoop body`: a nand-free body run once per output position `o` of `enumO` (in the registers
`43 … 46`, odometer `odoO`), each appending a chunk `f o` to a list (`iter_oLoop`). Instances:
the representation of an input (`inRepC`) and of the constant `1` (`constRepC`).
-/

set_option linter.unusedSimpArgs false

namespace SigabaNeo.Lattices

namespace FhatGen

open SigabaNeo.Tape SigabaNeo.Tape.RegVM SLP Algo

variable {ι : Type*} {E : Env} {ix : ι → ℕ}

/-- The registers `43 … 46` hold the output position `o`. -/
def ODig {N k : ℕ} (o : OI N k) (σ : St) : Prop :=
  σ.sc 43 = o.1.val ∧ σ.sc 44 = o.2.1.1.val ∧ σ.sc 45 = o.2.1.2.val ∧ σ.sc 46 = o.2.2.val

/-- The loop over the output positions. -/
def oLoop (body : Code) : Code := .rep 12 (.seq body odoO)

theorem iter_oLoop {N k : ℕ} (hk : 0 < k) (hN : 0 < N) {body : Code} {tgt : LR}
    {f : OI N k → List ℕ} {Q : St → Prop} (hf : ∀ o, (f o).length = k)
    (hQ : ∀ σ : St, Q σ → σ.sc 2 = k ∧ σ.sc 5 = N ∧ σ.sc 6 = 2)
    (hQo : ∀ (σ : St) (a b c d : ℕ), Q σ → Q (setSL σ (Function.update (Function.update
      (Function.update (Function.update σ.sc 43 a) 44 b) 45 c) 46 d) σ.ls))
    (hB : ∀ (σ : St) (o : OI N k), Q σ → ODig o σ → (σ.ls tgt).length + k ≤ E.C →
      Q (exec E body σ) ∧ ODig o (exec E body σ) ∧
        (exec E body σ).ls tgt = σ.ls tgt ++ f o)
    (hM : 4 * k * N + 2 ≤ E.M) (hkM : k ≤ E.M) (hNM : N ≤ E.M) :
    ∀ (i : ℕ) (σ : St) (L0 : List ℕ), i ≤ 4 * k * N → Q σ → σ.sc 43 = 0 → σ.sc 44 = 0 →
      σ.sc 45 = 0 → σ.sc 46 = 0 → σ.ls tgt = L0 → L0.length + 4 * k * N * k ≤ E.C →
      Q ((exec E (.seq body odoO))^[i] σ) ∧
        ((exec E (.seq body odoO))^[i] σ).ls tgt =
          L0 ++ (((enumO N k).take i).map f).flatten ∧
        ∃ a c1 c2 t, ((exec E (.seq body odoO))^[i] σ).sc 43 = a ∧
          ((exec E (.seq body odoO))^[i] σ).sc 44 = c1 ∧
          ((exec E (.seq body odoO))^[i] σ).sc 45 = c2 ∧
          ((exec E (.seq body odoO))^[i] σ).sc 46 = t ∧
          ((a * 2 + c1) * k + c2) * N + t = i ∧ c1 < 2 ∧ c2 < k ∧ t < N
  | 0, σ, L0, _, hq, h43, h44, h45, h46, hL, _ =>
    ⟨hq, by simp [hL], 0, 0, 0, 0, h43, h44, h45, h46, by ring, by omega, hk, hN⟩
  | i + 1, σ, L0, hi, hq, h43, h44, h45, h46, hL, hcap => by
    obtain ⟨hq1, hl1, a, c1, c2, t, h43', h44', h45', h46', hidx, hc1, hc2, ht⟩ :=
      iter_oLoop hk hN hf hQ hQo hB hM hkM hNM i σ L0 (by omega) hq h43 h44 h45 h46 hL hcap
    rw [Function.iterate_succ_apply']
    set τ := (exec E (.seq body odoO))^[i] σ
    have ha : a < 2 := by
      by_contra h
      have : 4 * k * N ≤ ((a * 2 + c1) * k + c2) * N + t := by nlinarith
      omega
    set o : OI N k := (⟨a, ha⟩, (⟨c1, hc1⟩, ⟨c2, hc2⟩), ⟨t, ht⟩)
    have ho : (enumO N k)[i]? = some o := by rw [← hidx]; exact enumO_getElem? o
    have hlen : (((enumO N k).take i).map f).flatten.length = i * k := by
      rw [length_flatten_of' (V := k) _ (fun w hw => by
        obtain ⟨o', _, rfl⟩ := List.mem_map.mp hw; exact hf o')]
      simp [List.length_take, length_enumO']; left; omega
    obtain ⟨hq2, ⟨d43, d44, d45, d46⟩, hl2⟩ := hB τ o hq1 ⟨h43', h44', h45', h46'⟩
      (by rw [hl1, List.length_append, hlen]; nlinarith)
    obtain ⟨hk2, hN2, h62⟩ := hQ _ hq2
    obtain ⟨a', c1', c2', t', h4, hidx', hc1', hc2', ht'⟩ := exec_odoO (E := E) (exec E body τ)
      a c1 c2 t hk2 hN2 h62 d43 d44 d45 d46 hc1 hc2 ht (by omega) hkM hNM (by omega)
    rw [exec_seq, h4]
    refine ⟨hQo _ _ _ _ _ hq2, ?_, a', c1', c2', t', by simp [setSL, Function.update_apply],
      by simp [setSL, Function.update_apply], by simp [setSL, Function.update_apply],
      by simp [setSL, Function.update_apply], by omega, hc1', hc2', ht'⟩
    simp only [setSL]
    rw [hl2, hl1, List.take_succ, ho, Option.toList_some, List.map_append, List.flatten_append,
      List.append_assoc]
    simp

/-! ### The representation of an input -/

/-- The codec index of a bit `(a, (c1, c2), i, j)` of a ciphertext: `a`, then the column, the bit,
the coefficient. -/
def codec {N k : ℕ} (b : BI N k) : ℕ :=
  (((b.1.val * 2 + b.2.1.1.val) * k + b.2.1.2.val) * k + b.2.2.1.val) * N + b.2.2.2.val

/-- `62 := base (61) + codec (a, (c1, c2), i (42), t)`. -/
def valC : Code :=
  .seq (.mov 62 43) (.seq (maddC 62 6 44 53) (.seq (maddC 62 2 45 53) (.seq (maddC 62 2 42 53)
    (.seq (maddC 62 5 46 53) (.add 62 61)))))

/-- One output position of an input: its `k` bits. -/
def inBody (tgt : LR) : Code :=
  .seq (.zero 42) (.rep 2 (.seq valC (.seq (.lpush tgt 62) (.inc 42))))

theorem codec_lt {N k : ℕ} (b : BI N k) : codec b < 4 * k * N * k := by
  obtain ⟨a, ⟨c1, c2⟩, i, j⟩ := b
  have := a.isLt; have := c1.isLt; have := c2.isLt; have := i.isLt; have := j.isLt
  simp only [codec]
  have mx : ∀ {x m y n : ℕ}, x < m → y < n → x * n + y < m * n := by
    intro x m y n hx hy
    calc x * n + y < x * n + n := by omega
      _ = (x + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right _ hx
  have h1 : a.val * 2 + c1.val < 4 := by omega
  have h2 := mx (mx (mx h1 c2.isLt) i.isLt) j.isLt
  calc _ < 4 * k * k * N := h2
    _ = 4 * k * N * k := by ring

theorem exec_valC {N k : ℕ} (σ : St) (o : OI N k) (i : Fin k) (base : ℕ) (hd : ODig o σ)
    (h2 : σ.sc 2 = k) (h5 : σ.sc 5 = N) (h6 : σ.sc 6 = 2) (h42 : σ.sc 42 = i.val)
    (h61 : σ.sc 61 = base) (hM : base + 4 * k * N * k ≤ E.M) :
    ∃ sc', exec E valC σ = setSL σ sc' σ.ls ∧
      sc' 62 = base + codec ((o.1, o.2.1, i, o.2.2) : BI N k) ∧
      ∀ r : SR, r ≠ 53 → r ≠ 62 → sc' r = σ.sc r := by
  obtain ⟨h43, h44, h45, h46⟩ := hd
  obtain ⟨a, ⟨c1, c2⟩, t⟩ := o
  simp only at h43 h44 h45 h46 ⊢
  have hc := codec_lt ((a, (c1, c2), i, t) : BI N k)
  simp only [codec] at hc ⊢
  have hk : 0 < k := Nat.pos_of_ne_zero (fun h => by subst h; exact c2.elim0)
  have hN : 0 < N := Nat.pos_of_ne_zero (fun h => by subst h; exact t.elim0)
  have hx1 : a.val * 2 + c1.val ≤ (a.val * 2 + c1.val) * k + c2.val :=
    le_trans (Nat.le_mul_of_pos_right _ hk) (Nat.le_add_right _ _)
  have hx2 : (a.val * 2 + c1.val) * k + c2.val ≤ ((a.val * 2 + c1.val) * k + c2.val) * k + i.val :=
    le_trans (Nat.le_mul_of_pos_right _ hk) (Nat.le_add_right _ _)
  have hx3 : ((a.val * 2 + c1.val) * k + c2.val) * k + i.val ≤
      (((a.val * 2 + c1.val) * k + c2.val) * k + i.val) * N + t.val :=
    le_trans (Nat.le_mul_of_pos_right _ hN) (Nat.le_add_right _ _)
  simp only [valC, exec_seq]
  rw [show exec E (.mov 62 43) σ = setSL σ (Function.update σ.sc 62 a.val) σ.ls by
    simp [exec, setSL, h43]]
  rw [exec_maddC 62 6 44 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [setSL, Function.update_apply, h6, h44]; omega)]
  rw [exec_maddC 62 2 45 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [setSL, Function.update_apply, h6, h44, h2, h45]; omega)]
  rw [exec_maddC 62 2 42 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [setSL, Function.update_apply, h6, h44, h2, h45, h42]; omega)]
  rw [exec_maddC 62 5 46 53 (by decide) (by decide) (by decide) (by decide) (by decide) _
    (by simp [setSL, Function.update_apply, h6, h44, h2, h45, h42, h5, h46]; omega)]
  refine ⟨_, rfl, ?_, ?_⟩
  · simp [exec, setSL, Function.update_apply, h6, h44, h2, h45, h42, h5, h46, h61]
    rw [min_eq_left (by omega)]; ring
  · intro r h53 h62
    simp [exec, setSL, Function.update_apply, h53, h62]

/-- The codec index with the bit as a natural. -/
def codecN {N k : ℕ} (o : OI N k) (i : ℕ) : ℕ :=
  (((o.1.val * 2 + o.2.1.1.val) * k + o.2.1.2.val) * k + i) * N + o.2.2.val

/-- The registers an input-representation body relies on. -/
def InQ (N k base : ℕ) (σ : St) : Prop :=
  σ.sc 2 = k ∧ σ.sc 5 = N ∧ σ.sc 6 = 2 ∧ σ.sc 61 = base

theorem iter_inner {N k : ℕ} (tgt : LR) (o : OI N k) (base : ℕ)
    (hM : base + 4 * k * N * k ≤ E.M) (hkM : k ≤ E.M) :
    ∀ (j i0 : ℕ) (σ : St), i0 + j ≤ k → InQ N k base σ → ODig o σ → σ.sc 42 = i0 →
      (σ.ls tgt).length + j ≤ E.C →
      ∃ sc', (exec E (.seq valC (.seq (.lpush tgt 62) (.inc 42))))^[j] σ =
          setSL σ sc' (Function.update σ.ls tgt (σ.ls tgt ++
            (List.range j).map fun x => base + codecN o (i0 + x))) ∧
        ∀ r : SR, r ≠ 42 → r ≠ 53 → r ≠ 62 → sc' r = σ.sc r
  | 0, i0, σ, _, _, _, _, _ => ⟨σ.sc, by simp [setSL], fun _ _ _ _ => rfl⟩
  | j + 1, i0, σ, hj, hq, hd, h42, hC => by
    rw [Function.iterate_succ_apply, exec_seq]
    have hi0 : i0 < k := by omega
    obtain ⟨sc1, e1, d1, f1⟩ := exec_valC (E := E) σ o ⟨i0, hi0⟩ base hd hq.1 hq.2.1 hq.2.2.1 h42
      hq.2.2.2 hM
    rw [e1, exec_seq]
    have hv : base + codec ((o.1, o.2.1, ⟨i0, hi0⟩, o.2.2) : BI N k) ≤ E.M := by
      have := codec_lt ((o.1, o.2.1, ⟨i0, hi0⟩, o.2.2) : BI N k); omega
    set σ2 : St := setSL σ (Function.update sc1 42 (i0 + 1)) (Function.update σ.ls tgt
      (σ.ls tgt ++ [base + codecN o i0]))
    have e2 : exec E (.inc 42) (exec E (.lpush tgt 62) (setSL σ sc1 σ.ls)) = σ2 := by
      rw [exec_lpush_lt (setSL σ sc1 σ.ls) tgt 62 (by simp [setSL]; omega)
        (by simp [setSL, d1]; exact hv)]
      simp only [exec, setSL, σ2, d1, f1 42 (by decide) (by decide), h42,
        min_eq_left (show i0 + 1 ≤ E.M by omega)]
      rfl
    rw [e2]
    have hfr : ∀ r : SR, r ≠ 42 → r ≠ 53 → r ≠ 62 → σ2.sc r = σ.sc r := fun r a b c => by
      simp [σ2, setSL, Function.update_of_ne a, f1 r b c]
    obtain ⟨sc', e', f'⟩ := iter_inner tgt o base hM hkM j (i0 + 1) σ2 (by omega)
      ⟨by rw [hfr 2 (by decide) (by decide) (by decide), hq.1],
        by rw [hfr 5 (by decide) (by decide) (by decide), hq.2.1],
        by rw [hfr 6 (by decide) (by decide) (by decide), hq.2.2.1],
        by rw [hfr 61 (by decide) (by decide) (by decide), hq.2.2.2]⟩
      ⟨by rw [hfr 43 (by decide) (by decide) (by decide), hd.1],
        by rw [hfr 44 (by decide) (by decide) (by decide), hd.2.1],
        by rw [hfr 45 (by decide) (by decide) (by decide), hd.2.2.1],
        by rw [hfr 46 (by decide) (by decide) (by decide), hd.2.2.2]⟩
      (by simp [σ2, setSL]) (by simp [σ2, setSL]; omega)
    refine ⟨sc', ?_, fun r a b c => (f' r a b c).trans (hfr r a b c)⟩
    rw [e']
    simp only [σ2, setSL, Function.update_idem, Function.update_self, List.append_assoc]
    congr 3
    rw [List.range_succ_eq_map]
    simp [codecN, codec, Nat.add_comm, Nat.add_left_comm]

theorem exec_inBody {N k : ℕ} (tgt : LR) (o : OI N k) (base : ℕ) (σ : St)
    (hM : base + 4 * k * N * k ≤ E.M) (hkM : k ≤ E.M) (hq : InQ N k base σ) (hd : ODig o σ)
    (hC : (σ.ls tgt).length + k ≤ E.C) :
    InQ N k base (exec E (inBody tgt) σ) ∧ ODig o (exec E (inBody tgt) σ) ∧
      (exec E (inBody tgt) σ).ls tgt = σ.ls tgt ++ (List.range k).map (fun x => base + codecN o x) ∧
      (∀ r : SR, r ≠ 42 → r ≠ 53 → r ≠ 62 → (exec E (inBody tgt) σ).sc r = σ.sc r) ∧
      ∀ l : LR, l ≠ tgt → (exec E (inBody tgt) σ).ls l = σ.ls l := by
  set σ0 := setSL σ (Function.update σ.sc 42 0) σ.ls
  have e0 : exec E (.zero 42) σ = σ0 := rfl
  have hs0 : ∀ r : SR, r ≠ 42 → σ0.sc r = σ.sc r := fun r h => by
    simp [σ0, setSL, Function.update_of_ne h]
  obtain ⟨sc', e', f'⟩ := iter_inner (E := E) tgt o base hM hkM k 0 σ0 (by omega)
    ⟨by rw [hs0 2 (by decide), hq.1], by rw [hs0 5 (by decide), hq.2.1],
      by rw [hs0 6 (by decide), hq.2.2.1], by rw [hs0 61 (by decide), hq.2.2.2]⟩
    ⟨by rw [hs0 43 (by decide), hd.1], by rw [hs0 44 (by decide), hd.2.1],
      by rw [hs0 45 (by decide), hd.2.2.1], by rw [hs0 46 (by decide), hd.2.2.2]⟩
    (by simp [σ0, setSL]) (by simp [σ0, setSL]; exact hC)
  have hrun : exec E (inBody tgt) σ = setSL σ0 sc' (Function.update σ0.ls tgt (σ0.ls tgt ++
      (List.range k).map fun x => base + codecN o (0 + x))) := by
    rw [inBody, exec_seq, e0, exec_rep, show σ0.sc 2 = k by rw [hs0 2 (by decide), hq.1], e']
  have g : ∀ r : SR, r ≠ 42 → r ≠ 53 → r ≠ 62 → (exec E (inBody tgt) σ).sc r = σ.sc r :=
    fun r a b c => by rw [hrun]; simp only [setSL]; rw [f' r a b c, hs0 r a]
  refine ⟨⟨by rw [g 2 (by decide) (by decide) (by decide), hq.1],
    by rw [g 5 (by decide) (by decide) (by decide), hq.2.1],
    by rw [g 6 (by decide) (by decide) (by decide), hq.2.2.1],
    by rw [g 61 (by decide) (by decide) (by decide), hq.2.2.2]⟩,
    ⟨by rw [g 43 (by decide) (by decide) (by decide), hd.1],
    by rw [g 44 (by decide) (by decide) (by decide), hd.2.1],
    by rw [g 45 (by decide) (by decide) (by decide), hd.2.2.1],
    by rw [g 46 (by decide) (by decide) (by decide), hd.2.2.2]⟩, ?_, g, fun l hl => ?_⟩
  · rw [hrun]; simp [σ0, setSL]
  · rw [hrun]; simp [σ0, setSL, Function.update_of_ne hl]

/-- **The representation of an input** (base `ix (i, 0)` in `61`) into `tgt`. -/
def inRepC (tgt : LR) : Code :=
  .seq (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46) (.lnil tgt)))))
    (oLoop (inBody tgt))

theorem exec_inRepC {A : Type*} {N k : ℕ} (hk : 0 < k) (hN : 0 < N)
    (ix' : A × BI N k → ℕ) (i : A) (base : ℕ) (hix : ∀ b, ix' (i, b) = base + codec b)
    (tgt : LR) (σ : St) (hq : InQ N k base σ) (h12 : σ.sc 12 = 4 * k * N)
    (hM : base + 4 * k * N * k + 4 * k * N + 2 ≤ E.M) (hC : 4 * k * N * k ≤ E.C) :
    InQ N k base (exec E (inRepC tgt) σ) ∧
      (exec E (inRepC tgt) σ).ls tgt = repList E ix' (fun b => Wire.input (i, b)) ∧
      (∀ r : SR, r.val < 42 ∨ (46 < r.val ∧ r.val ≠ 53 ∧ r.val ≠ 62) →
        (exec E (inRepC tgt) σ).sc r = σ.sc r) ∧
      ∀ l : LR, l ≠ tgt → (exec E (inRepC tgt) σ).ls l = σ.ls l := by
  have hkM : k ≤ E.M := by nlinarith
  have hNM : N ≤ E.M := by nlinarith
  set σ0 := setSL σ (Function.update (Function.update (Function.update (Function.update σ.sc 43 0)
    44 0) 45 0) 46 0) (Function.update σ.ls tgt [])
  have e0 : exec E (.seq (.zero 43) (.seq (.zero 44) (.seq (.zero 45) (.seq (.zero 46)
      (.lnil tgt))))) σ = σ0 := rfl
  have hs0 : ∀ r : SR, r.val < 43 ∨ 46 < r.val → σ0.sc r = σ.sc r := fun r hr => by
    simp only [σ0, setSL]
    rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide),
      Function.update_of_ne (by rintro rfl; revert hr; decide)]
  let Q : St → Prop := fun τ => InQ N k base τ ∧
    (∀ r : SR, r.val < 42 ∨ (46 < r.val ∧ r.val ≠ 53 ∧ r.val ≠ 62) → τ.sc r = σ.sc r) ∧
    ∀ l : LR, l ≠ tgt → τ.ls l = σ.ls l
  have hQ0 : Q σ0 := ⟨⟨by rw [hs0 2 (by decide), hq.1], by rw [hs0 5 (by decide), hq.2.1],
      by rw [hs0 6 (by decide), hq.2.2.1], by rw [hs0 61 (by decide), hq.2.2.2]⟩,
    fun r hr => hs0 r (by omega), fun l hl => by simp [σ0, setSL, Function.update_of_ne hl]⟩
  have hf : ∀ o : OI N k, ((List.range k).map fun x => base + codecN o x).length = k :=
    fun o => by simp
  have it := iter_oLoop (E := E) (tgt := tgt) (f := fun o => (List.range k).map
      fun x => base + codecN o x) (Q := Q) hk hN hf (fun τ h => ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩)
    (fun τ a b c d h => ⟨⟨by simp [setSL, h.1.1], by simp [setSL, h.1.2.1],
      by simp [setSL, h.1.2.2.1], by simp [setSL, h.1.2.2.2]⟩,
      fun r hr => by
        simp only [setSL]
        rw [Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide),
          Function.update_of_ne (by rintro rfl; revert hr; decide)]
        exact h.2.1 r hr, fun l hl => h.2.2 l hl⟩)
    (fun τ o h hd hC' => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := exec_inBody (E := E) tgt o base τ (by omega) hkM h.1 hd hC'
      exact ⟨⟨a1, fun r hr => by
          rw [a4 r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
            (by rintro rfl; revert hr; decide)]; exact h.2.1 r hr,
        fun l hl => by rw [a5 l hl]; exact h.2.2 l hl⟩, a2, a3⟩)
    (by omega) hkM hNM (4 * k * N) σ0 [] le_rfl hQ0 (by simp [σ0, setSL])
    (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by simp [σ0, setSL]) (by simp [σ0, setSL])
    (by simpa using hC)
  have hrun : exec E (inRepC tgt) σ = (exec E (.seq (inBody tgt) odoO))^[4 * k * N] σ0 := by
    rw [inRepC, exec_seq, e0, oLoop, exec_rep, hs0 12 (by decide), h12]
  obtain ⟨hQ, hL, -⟩ := it
  rw [hrun]
  refine ⟨hQ.1, ?_, hQ.2.1, hQ.2.2⟩
  rw [hL, List.nil_append, List.take_of_length_le (by rw [length_enumO']), repList]
  congr 1
  apply List.map_congr_left; intro o _
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [pos, hix, codec, codecN]

end FhatGen

end SigabaNeo.Lattices
