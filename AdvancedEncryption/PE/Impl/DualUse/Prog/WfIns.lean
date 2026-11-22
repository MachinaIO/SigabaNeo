import PE.Impl.DualUse.Prog.WfPred

/-!
# The input stores of the two simulations, from the simulation data

The two SLP evaluators of the `W_f` block start from the stores
`padW ++ (ins ++ [one]).flatten`, with the inputs `insTW sd` (`f̂`, top-row gadget) and
`insGW sd` (the predicate, Ring-GSW gadget) of `PE.Impl.DualUse.Prog.KeyWfWords`.

`bldP oA oB a b m V P l one : Prog 9` (tape `0` the word `sdEnc sd`, `1` the output, `2` the gate
counter, `3` … `8` scratch) appends the padding `replicate (|s 2| · V) false`, then for every item
`x` of `l` the next `a` bits of the stream `drop oA (s 0)`, the next `b` bits of the stream
`drop oB (s 0)` and the word written by `P x : Prog 3` (`0` the word of the data, `1` scratch,
`2` the output), then `one` (`run_bldP`).

* `insTP`: the streams of the `B_j` (in `mpk`) and of the `W_j`, the bits `ψ_j` (`psiBitP`), the
  items `Enum.list` of `Fin 10 × BI N k`: **`run_insTP`** writes
  `replicate (|s 2| · VT) false ++ (insTW sd ++ [simOneW … gadW]).flatten`;
* `insGP`: the streams of the `Ψᵢ` and of the `Rᵢ`, the bits `xᵢ` (`xBitP`), the items
  `List.finRange 10`: **`run_insGP`** writes `… ++ (insGW sd ++ [simOneW … gswGadW]).flatten`.
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape
  SigabaNeo.Tape.Prog Matrix AdvancedEncryption.RingBTVW AdvancedEncryption.DualUse.Algo
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow
open scoped SigabaNeo.Tape.Prog

set_option linter.unusedSimpArgs false

/-! ### The generic builder -/

/-- The tapes of the program of an item: the data, scratch, the output. -/
def u3 : Fin 3 → Fin 9 := ![0, 6, 5]

theorem u3_inj : Function.Injective u3 := by decide

@[simp] theorem u3_zero : u3 0 = 0 := rfl
@[simp] theorem u3_one : u3 1 = 6 := rfl
@[simp] theorem u3_two : u3 2 = 5 := rfl

section Generic

variable {α : Type}

/-- The items. -/
def itemsP (a b m : ℕ) (P : α → Prog 3) : List α → Prog 9
  | [] => nop 0
  | x :: l => appendP 1 3 a ⨾ appendP 1 4 b ⨾ Prog.map u3 (P x) ⨾ appendP 1 5 m ⨾ itemsP a b m P l

/-- **The builder.** -/
def bldP (oA oB a b m V : ℕ) (P : α → Prog 3) (l : List α) (one : List Bool) : Prog 9 :=
  padP 1 7 2 8 V ⨾ cp 3 0 ⨾ dropN oA 3 ⨾ cp 4 0 ⨾ dropN oB 4 ⨾ itemsP a b m P l ⨾
    SigabaNeo.Tape.Prog.putW 5 one ⨾ appendP 1 5 V ⨾ clr 3 ⨾ clr 4

theorem run_itemsP {a b m : ℕ} {P : α → Prog 3} {sd : List Bool} {fA fB fC : α → List Bool}
    (hA : ∀ x, (fA x).length = a) (hB : ∀ x, (fB x).length = b) (hC : ∀ x, (fC x).length = m)
    (hP : ∀ x (r : Store 3), r 0 = sd → r 1 = [] → run (P x) r = Function.update r 2 (fC x)) :
    ∀ (l : List α) (s : Store 9) (rA rB : List Bool), s 0 = sd → s 5 = [] → s 6 = [] →
      s 3 = l.flatMap fA ++ rA → s 4 = l.flatMap fB ++ rB →
      run (itemsP a b m P l) s = Function.update (Function.update (Function.update s 1
        (s 1 ++ (l.map fun x => fA x ++ fB x ++ fC x).flatten)) 3 rA) 4 rB
  | [], s, rA, rB, _, _, _, h3, h4 => by
    simp only [List.flatMap_nil, List.nil_append] at h3 h4
    rw [itemsP, run_nop]
    funext t
    simp only [Function.update_apply]
    split_ifs with h1 h2 h3' <;> subst_vars <;> simp_all
  | x :: l, s, rA, rB, h0, h5, h6, h3, h4 => by
    simp only [List.flatMap_cons, List.append_assoc] at h3 h4
    rw [itemsP, run_seq, run_appendP (by decide), run_seq, run_appendP (by decide), run_seq,
      run_map_eq_update u3_inj _ _ 2 (fC x) (hP x _ (by simp [u3, Function.update_apply, h0])
        (by simp [u3, Function.update_apply, h6])),
      run_seq, run_appendP (by decide)]
    have e3 : ((s 3).take a, (s 3).drop a) = (fA x, l.flatMap fA ++ rA) := by
      rw [h3, List.take_left' (hA x), List.drop_left' (hA x)]
    have e4 : ((s 4).take b, (s 4).drop b) = (fB x, l.flatMap fB ++ rB) := by
      rw [h4, List.take_left' (hB x), List.drop_left' (hB x)]
    simp only [Prod.mk.injEq] at e3 e4
    rw [run_itemsP hA hB hC hP l _ rA rB (by simp [Function.update_apply, h0])
      (by simp [u3, Function.update_apply, List.drop_of_length_le (le_of_eq (hC x))])
      (by simp [Function.update_apply, h6]) (by simp [Function.update_apply, e3.2])
      (by simp [Function.update_apply, e4.2])]
    funext t
    simp only [Function.update_apply, u3]
    by_cases t1 : t = 1
    · subst t1
      simp [e3.1, e4.1, List.take_of_length_le (le_of_eq (hC x)), List.append_assoc]
    · by_cases t3 : t = 3
      · subst t3; simp
      · by_cases t4 : t = 4
        · subst t4; simp
        · by_cases t5 : t = 5
          · subst t5; simp [h5, List.drop_of_length_le (le_of_eq (hC x))]
          · simp [t1, t3, t4, t5]

/-- **The builder** on a store whose scratch tapes `3` … `8` are blank. -/
theorem run_bldP {oA oB a b m V : ℕ} {P : α → Prog 3} {sd : List Bool} {fA fB fC : α → List Bool}
    (hA : ∀ x, (fA x).length = a) (hB : ∀ x, (fB x).length = b) (hC : ∀ x, (fC x).length = m)
    (hP : ∀ x (r : Store 3), r 0 = sd → r 1 = [] → run (P x) r = Function.update r 2 (fC x))
    (l : List α) (one : List Bool) (hone : one.length = V) {rA rB : List Bool}
    (hsA : sd.drop oA = l.flatMap fA ++ rA) (hsB : sd.drop oB = l.flatMap fB ++ rB)
    (s : Store 9) (h0 : s 0 = sd) (hb : ∀ t : Fin 9, 3 ≤ t.val → s t = []) :
    run (bldP oA oB a b m V P l one) s = Function.update s 1 (s 1 ++
      List.replicate ((s 2).length * V) false ++
        ((l.map fun x => fA x ++ fB x ++ fC x) ++ [one]).flatten) := by
  rw [bldP, run_seq, run_padP (by decide) (by decide) (by decide) V s (hb 8 (by decide))
    (hb 7 (by decide))]
  simp only [run_seq, run_copy, run_dropN']
  rw [run_itemsP hA hB hC hP l _ rA rB (by simp [Function.update_apply, h0])
    (by simp [Function.update_apply, hb 5 (by decide)])
    (by simp [Function.update_apply, hb 6 (by decide)])
    (by simp [Function.update_apply, h0, hsA]) (by simp [Function.update_apply, h0, hsB])]
  simp only [SigabaNeo.Tape.Prog.run_putW, run_appendP (show (1 : Fin 9) ≠ 5 by decide), run_clear]
  funext t
  simp only [Function.update_apply]
  by_cases t1 : t = 1
  · subst t1
    simp [List.take_of_length_le (le_of_eq hone), List.flatten_append, List.append_assoc]
  · by_cases t3 : t = 3
    · subst t3; simp [hb 3 (by decide)]
    · by_cases t4 : t = 4
      · subst t4; simp [hb 4 (by decide)]
      · by_cases t5 : t = 5
        · subst t5; simp [hb 5 (by decide), List.drop_of_length_le (le_of_eq hone)]
        · simp [t1, t3, t4, t5]

theorem coinFree_itemsP {a b m : ℕ} {P : α → Prog 3} (hP : ∀ x, (P x).CoinFree) :
    ∀ l : List α, (itemsP a b m P l).CoinFree
  | [] => rfl
  | x :: l => by
    have h1 := coinFree_appendP (1 : Fin 9) 3 a
    have h2 := coinFree_appendP (1 : Fin 9) 4 b
    have h3 := coinFree_appendP (1 : Fin 9) 5 m
    have h4 : (Prog.map u3 (P x)).coinFreeB = true := by
      have := hP x; simp only [CoinFree] at this; rw [coinFreeB_map]; exact this
    have h5 := coinFree_itemsP (a := a) (b := b) (m := m) hP l
    simp only [CoinFree] at h1 h2 h3 h5
    simp [CoinFree, itemsP, coinFreeB, h1, h2, h3, h4, h5]
where
  coinFreeB_map {n k : ℕ} {u : Fin n → Fin k} : ∀ p : Prog n, (map u p).coinFreeB = p.coinFreeB
    | .prim _ | .coin _ => rfl
    | .seq p q | .ifBlank _ p q | .ifBit _ p q => by
      simp only [Prog.map, coinFreeB, coinFreeB_map p, coinFreeB_map q]
    | .loop _ b => by simp only [Prog.map, coinFreeB, coinFreeB_map b]

theorem wf_itemsP {a b m : ℕ} {P : α → Prog 3} (hP : ∀ x, (P x).WF) :
    ∀ l : List α, (itemsP a b m P l).WF
  | [] => trivial
  | x :: l => ⟨wf_appendP _ _ _, wf_appendP _ _ _, WF.map u3_inj (hP x), wf_appendP _ _ _,
      wf_itemsP hP l⟩

theorem coinFree_bldP {oA oB a b m V : ℕ} {P : α → Prog 3} (hP : ∀ x, (P x).CoinFree) (l : List α)
    (one : List Bool) : (bldP oA oB a b m V P l one).CoinFree := by
  have h1 := coinFree_padP (1 : Fin 9) 7 2 8 V
  have h2 := coinFree_dropN oA (3 : Fin 9)
  have h3 := coinFree_dropN oB (4 : Fin 9)
  have h4 := coinFree_itemsP (a := a) (b := b) (m := m) hP l
  have h5 := SigabaNeo.Tape.Prog.coinFree_putW (5 : Fin 9) one
  have h6 := coinFree_appendP (1 : Fin 9) 5 V
  simp only [CoinFree] at h1 h2 h3 h4 h5 h6
  simp [CoinFree, bldP, coinFreeB, h1, h2, h3, h4, h5, h6]

theorem wf_bldP {oA oB a b m V : ℕ} {P : α → Prog 3} (hP : ∀ x, (P x).WF) (l : List α)
    (one : List Bool) : (bldP oA oB a b m V P l one).WF :=
  ⟨wf_padP (by decide) (by decide) V, trivial, wf_dropN _ _, trivial, wf_dropN _ _, wf_itemsP hP l,
    SigabaNeo.Tape.Prog.wf_putW _ _, wf_appendP _ _ _, trivial, trivial⟩

end Generic

/-! ### The layout of the simulation data -/

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-- The offset of the `B_j` in `sdEnc` (inside `mpk`). -/
def offB : ℕ := fixLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) +
  fixLen (matEnc (N := N) (K := K) (Fin 1) (TrapCol k))

/-- The offset of the `Rᵢ`. -/
def offR : ℕ := fixLen (pkEnc hk c) + fixLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d))

/-- The offset of the `W_j`. -/
def offW : ℕ := fixLen (pkEnc hk c) + (fixLen (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)) +
  fixLen (rmEnc c))

/-- The joint length of the simulation of `f̂`. -/
abbrev VT (N K k d : ℕ) : ℕ := lenA N K k 1 + lenA N K k d + N * K

/-- The joint length of the simulation of the predicate. -/
abbrev VG (N K k d : ℕ) : ℕ := lenA N K k 2 + lenA N K k d + N * K

theorem drop_len_add (x L : List Bool) (n : ℕ) : (x ++ L).drop (x.length + n) = L.drop n := by
  rw [List.drop_append]; simp

theorem drop_app2 {x y z : List Bool} {a b : ℕ} (ha : x.length = a) (hb : y.length = b) :
    (x ++ (y ++ z)).drop (a + b) = z := by
  subst ha hb; rw [drop_len_add, List.drop_left']; rfl

theorem drop_app3 {x y z r : List Bool} {a b c : ℕ} (ha : x.length = a) (hb : y.length = b)
    (hc : z.length = c) : (x ++ (y ++ (z ++ r))).drop (a + (b + c)) = r := by
  subst ha; rw [drop_len_add, drop_app2 hb hc]

theorem drop_app4 {w x y z r : List Bool} {a b c d : ℕ} (ha : w.length = a) (hb : x.length = b)
    (hc : y.length = c) (hd : z.length = d) :
    (w ++ (x ++ (y ++ (z ++ r)))).drop (a + (b + (c + d))) = r := by
  subst ha; rw [drop_len_add, drop_app3 hb hc hd]

theorem fun_enc_flatMap {α β : Type} [Enum α] {n : ℕ} (e : FixedEnc β n) (f : α → β) :
    (FixedEnc.fun e).enc f = (Enum.list (α := α)).flatMap fun a => e.enc (f a) := by
  show ((Enum.list (α := α)).map f).flatMap e.enc = _
  rw [List.flatMap_map]

theorem sd_dropB (sd : SimData hk c) :
    ((sdEnc hk c).enc sd).drop (offB c) =
      (Enum.list (α := JT N K k hk)).flatMap (fun j => rowW N K k (sd.mpk.Bj j)) ++
        ((ringEnc N K).enc sd.mpk.p ++ ((matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc sd.c₀ ++
        ((rmEnc c).enc sd.Rm ++ ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k))).enc sd.W ++
        ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc sd.Ψ ++ dateEnc.enc sd.x))))) := by
  rw [sdEnc_enc]
  have e : (pkEnc hk c).enc sd.mpk = (matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc sd.mpk.B₀ ++
      ((matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc sd.mpk.B₁ ++
        ((FixedEnc.fun (α := JT N K k hk) (matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))).enc sd.mpk.Bj ++
          (ringEnc N K).enc sd.mpk.p)) := rfl
  rw [e, List.append_assoc, List.append_assoc, offB, drop_app2 (length_enc_fixLen _ _)
    (length_enc_fixLen _ _), fun_enc_flatMap, List.append_assoc]
  congr 1
  refine List.flatMap_congr fun j _ => ?_
  rw [matEnc_cols]
  rfl

theorem sd_dropW (sd : SimData hk c) :
    ((sdEnc hk c).enc sd).drop (offW hk c) =
      (Enum.list (α := JT N K k hk)).flatMap (fun j => colsW N K k c.d (sd.W j)) ++
        ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc sd.Ψ ++ dateEnc.enc sd.x) := by
  rw [sdEnc_enc, offW, drop_app3 (length_enc_fixLen _ _) (length_enc_fixLen _ _)
    (length_enc_fixLen _ _), fun_enc_flatMap]
  congr 1
  refine List.flatMap_congr fun j _ => ?_
  rw [matEnc_cols]

theorem sd_dropR (sd : SimData hk c) :
    ((sdEnc hk c).enc sd).drop (offR hk c) =
      (List.finRange 10).flatMap (fun i => colsW N K k c.d (sd.Rm i)) ++
        ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin c.d) (RingBTVW.Col k))).enc sd.W ++
        ((FixedEnc.fun (matEnc (N := N) (K := K) (Fin 2) (RingBTVW.Col k))).enc sd.Ψ ++ dateEnc.enc sd.x)) := by
  rw [sdEnc_enc, offR, drop_app2 (length_enc_fixLen _ _) (length_enc_fixLen _ _), rmEnc,
    fun_enc_flatMap]
  congr 1
  refine List.flatMap_congr fun j _ => ?_
  rw [matEnc_cols]

theorem sd_dropPsi (sd : SimData hk c) :
    ((sdEnc hk c).enc sd).drop (offPsi hk c) =
      (List.finRange 10).flatMap (fun i => colsW N K k 2 (sd.Ψ i)) ++ dateEnc.enc sd.x := by
  rw [sdEnc_enc, offPsi, drop_app4 (length_enc_fixLen _ _) (length_enc_fixLen _ _)
    (length_enc_fixLen _ _) (length_enc_fixLen _ _), fun_enc_flatMap]
  congr 1
  refine List.flatMap_congr fun j _ => ?_
  rw [matEnc_cols]

/-! ### The two builders -/

/-- **The input store of the simulation of `f̂`.** -/
noncomputable def insTP : Prog 9 :=
  bldP (offB c) (offW hk c) (lenA N K k 1) (lenA N K k c.d) (N * K) (VT N K k c.d)
    (psiBitP N K k (posBit hk c)) (Enum.list (α := JT N K k hk)) (simOneW N K k c.d (gadW N K k))

/-- **The input store of the simulation of the predicate.** -/
noncomputable def insGP : Prog 9 :=
  bldP (offPsi hk c) (offR hk c) (lenA N K k 2) (lenA N K k c.d) (N * K) (VG N K k c.d)
    (xBitP N K (posX hk c)) (List.finRange 10) (simOneW N K k c.d (gswGadW N K k))

theorem length_gswGadW' : (gswGadW N K k).length = lenA N K k 2 := by
  rw [gswGadW_eq, List.length_append, List.length_append, length_gadW, length_zeroW,
    List.length_take, length_gadW, lenA, min_eq_left (Nat.mul_le_mul_right _ (by omega))]; ring

theorem length_simOneT : (simOneW N K k c.d (gadW N K k)).length = VT N K k c.d := by
  rw [simOneW, length_jointW, length_gadW, length_zeroW, length_oneW, VT, lenA]; ring

theorem length_simOneG : (simOneW N K k c.d (gswGadW N K k)).length = VG N K k c.d := by
  rw [simOneW, length_jointW, length_gswGadW', length_zeroW, length_oneW]

theorem run_insTP (hN : 0 < N) (hK : 0 < K) (sd : SimData hk c) (s : Store 9)
    (h0 : s 0 = (sdEnc hk c).enc sd) (hb : ∀ t : Fin 9, 3 ≤ t.val → s t = []) :
    run (insTP hk c) s = Function.update s 1 (s 1 ++
      List.replicate ((s 2).length * VT N K k c.d) false ++
        (insTW sd ++ [simOneW N K k c.d (gadW N K k)]).flatten) := by
  rw [insTP]
  refine Eq.trans (run_bldP (α := JT N K k hk) (P := psiBitP N K k (posBit hk c)) (fA := fun j => rowW N K k (sd.mpk.Bj j)) (fB := fun j => colsW N K k c.d (sd.W j))
    (fC := fun j => psiBitsW N K k (fun i => colsW N K k 2 (sd.Ψ i)) j) (sd := (sdEnc hk c).enc sd)
    (fun _ => length_rowW' _) (fun _ => length_colsW' _ _)
    (fun _ => by simp only [psiBitsW, bitsW]; rw [SigabaNeo.Tape.Prog.length_constW (length_bitW _ _)])
    (fun j r hr0 hr1 => by
      rw [run_psiBitP hk c hN hK sd j r hr0, hr1, ite_self]
      funext t
      simp only [Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all)
    _ _ (length_simOneT c) (sd_dropB hk c sd) (sd_dropW hk c sd) s h0 hb) ?_
  rfl

theorem run_insGP (hN : 0 < N) (hK : 0 < K) (sd : SimData hk c) (s : Store 9)
    (h0 : s 0 = (sdEnc hk c).enc sd) (hb : ∀ t : Fin 9, 3 ≤ t.val → s t = []) :
    run (insGP hk c) s = Function.update s 1 (s 1 ++
      List.replicate ((s 2).length * VG N K k c.d) false ++
        (insGW sd ++ [simOneW N K k c.d (gswGadW N K k)]).flatten) := by
  rw [insGP]
  refine Eq.trans (run_bldP (fA := fun i => colsW N K k 2 (sd.Ψ i)) (fB := fun i => colsW N K k c.d (sd.Rm i))
    (fC := fun i => constW N K (bitW K (DateWindow.bitsOf sd.x i))) (sd := (sdEnc hk c).enc sd)
    (fun _ => length_colsW' _ _) (fun _ => length_colsW' _ _)
    (fun _ => SigabaNeo.Tape.Prog.length_constW (length_bitW _ _))
    (fun i r hr0 hr1 => by
      rw [run_xBitP hk c hN hK sd i r hr0]
      funext t
      simp only [Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all)
    _ _ (length_simOneG c) (sd_dropPsi hk c sd) (sd_dropR hk c sd) s h0 hb) ?_
  rfl

theorem coinFree_insTP : (insTP hk c).CoinFree :=
  coinFree_bldP (fun j => coinFree_psiBitP _ j) _ _

theorem coinFree_insGP : (insGP hk c).CoinFree :=
  coinFree_bldP (fun i => coinFree_xBitP _ i) _ _

theorem wf_insTP : (insTP hk c).WF := wf_bldP (fun j => wf_psiBitP _ j) _ _

theorem wf_insGP : (insGP hk c).WF := wf_bldP (fun i => wf_xBitP _ i) _ _

end AdvancedEncryption.DualUse.Prog
