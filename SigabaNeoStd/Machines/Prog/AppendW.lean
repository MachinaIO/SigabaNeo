import SigabaNeoStd.Machines.Prog.Stream
import SigabaNeoStd.Machines.Prog.Pass

/-!
# Appending words: constant runs, tapes, and dropping by a length

Coin-free building blocks of `Prog k` that **lengthen** a word (outside the `NoGrow` fragment; their
laws come from `Prog.law_eq_run_of_coinFree`):

* `snocN o b n`: append `n` copies of `b` to `o` (`run_snocN`);
* `appT o x a b`: append the word of tape `x` to `o`, through the blank scratch tapes `a`, `b`
  (`run_appT`);
* `dropT t x a`: drop `|s x|` bits of `t`, through the blank scratch `a` (`run_dropT`);
* `dynE o a xs b sa sb`: `a` ones, the words of the tapes `xs` in order, `b` zeros
  (`run_dynE`); with the tapes holding ones then zeros it appends a unary number
  (`unaryApp_eq`).
-/

namespace SigabaNeo.Tape

namespace Prog

open scoped Prog

variable {k : ℕ}

/-! ### Constant runs -/

/-- Append `n` copies of `b` to `o`. -/
def snocN (o : Fin k) (b : Bool) : ℕ → Prog k
  | 0 => nop o
  | n + 1 => snocN o b n ⨾ prim (.snoc o b)

theorem run_snocN (o : Fin k) (b : Bool) : ∀ (n : ℕ) (s : Store k),
    run (snocN o b n) s = Function.update s o (s o ++ List.replicate n b)
  | 0, s => by simp [snocN]
  | n + 1, s => by
    rw [snocN, run_seq, run_snocN o b n s, run_prim]
    simp [Prim.apply, List.replicate_succ', List.append_assoc]

theorem coinFree_snocN (o : Fin k) (b : Bool) : ∀ n, (snocN o b n).CoinFree
  | 0 => rfl
  | n + 1 => by
    simpa [CoinFree, snocN, coinFreeB] using coinFree_snocN o b n

theorem wf_snocN (o : Fin k) (b : Bool) : ∀ n, (snocN o b n).WF
  | 0 => trivial
  | n + 1 => ⟨wf_snocN o b n, trivial⟩

/-- `j` ones then `S - j` zeros appended to `o`. -/
def emitU (o : Fin k) (S j : ℕ) : Prog k := snocN o true j ⨾ snocN o false (S - j)

theorem run_emitU (o : Fin k) (S j : ℕ) (s : Store k) :
    run (emitU o S j) s =
      Function.update s o (s o ++ (List.replicate j true ++ List.replicate (S - j) false)) := by
  rw [emitU, run_seq, run_snocN, run_snocN]
  simp [List.append_assoc]

theorem coinFree_emitU (o : Fin k) (S j : ℕ) : (emitU o S j).CoinFree := by
  simp only [CoinFree, emitU, coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_snocN _ _ _, coinFree_snocN _ _ _⟩

theorem wf_emitU (o : Fin k) (S j : ℕ) : (emitU o S j).WF := ⟨wf_snocN _ _ _, wf_snocN _ _ _⟩

/-! ### Appending a tape -/

/-- One round of `appT`: the next bit of the copy `b` to the end of `o`. -/
def appBody (o b : Fin k) : Prog k := prim (.snocHead o b) ⨾ tl b

/-- Append the word of `x` to `o` (`a`, `b` scratch). -/
def appT (o x a b : Fin k) : Prog k := cp b x ⨾ forN a x (appBody o b) ⨾ clr b

theorem run_appT {o x a b : Fin k} (hoa : o ≠ a) (hob : o ≠ b) (hab : a ≠ b) (s : Store k) :
    run (appT o x a b) s =
      Function.update (Function.update (Function.update s o (s o ++ s x)) a []) b [] := by
  have hba : b ≠ a := Ne.symm hab
  have hbo : b ≠ o := Ne.symm hob
  set s1 := Function.update s b (s x) with hs1
  let G : List Bool × List Bool → Store k := fun p =>
    Function.update (Function.update s1 o p.1) b p.2
  let step : List Bool × List Bool → List Bool × List Bool := fun p =>
    (p.1 ++ p.2.take 1, p.2.tail)
  have hstep : ∀ p w, run (appBody o b) (Function.update (G p) a w) =
      Function.update (G (step p)) a w := by
    intro p w
    simp only [appBody, run_seq, run_prim, Prim.apply, G, step]
    funext t
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  have hit : ∀ (n : ℕ) (u r : List Bool), step^[n] (u, r) = (u ++ r.take n, r.drop n) := by
    intro n
    induction n with
    | zero => intro u r; simp
    | succ n ih =>
      intro u r
      rw [Function.iterate_succ_apply', ih]
      simp only [step, List.append_assoc, List.tail_drop, ← List.take_add]
  have hx : s1 x = s x := by
    by_cases h : x = b
    · subst h; simp [hs1]
    · simp [hs1, Function.update_of_ne h]
  have hG : G (s o, s x) = s1 := by
    funext t
    simp only [G, hs1, Function.update_apply]
    split_ifs <;> simp_all
  rw [appT, run_seq, run_seq, run_copy, ← hs1,
    run_forN a x (appBody o b) G step hstep (s o, s x) s1 (by rw [hG]), hx, hit,
    List.take_length, List.drop_length, run_clear]
  funext t
  simp only [G, hs1, Function.update_apply]
  split_ifs <;> simp_all

/-- `appT` with blank scratch. -/
theorem run_appT_blank {o x a b : Fin k} (hoa : o ≠ a) (hob : o ≠ b) (hab : a ≠ b) (s : Store k)
    (ha : s a = []) (hb : s b = []) :
    run (appT o x a b) s = Function.update s o (s o ++ s x) := by
  rw [run_appT hoa hob hab]
  funext t
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem coinFree_appT (o x a b : Fin k) : (appT o x a b).CoinFree := rfl

theorem wf_appT {o x a b : Fin k} (hoa : o ≠ a) (hba : b ≠ a) : (appT o x a b).WF := by
  refine ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩, ?_⟩, trivial⟩
  simp [appBody, Preserves, Prim.writes, Ne.symm hoa, hba.symm]

/-! ### Dropping by a length -/

/-- Drop `|s x|` bits of `t` (`a` scratch). -/
def dropT (t x a : Fin k) : Prog k := forN a x (tl t)

theorem run_dropT {t x a : Fin k} (hta : t ≠ a) (s : Store k) :
    run (dropT t x a) s = Function.update (Function.update s t ((s t).drop (s x).length)) a [] := by
  let G : List Bool → Store k := fun v => Function.update s t v
  have hstep : ∀ v w, run (tl t) (Function.update (G v) a w) = Function.update (G v.tail) a w := by
    intro v w
    simp only [run_tail, G]
    funext u
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  have hit : ∀ (n : ℕ) (v : List Bool), (List.tail)^[n] v = v.drop n := by
    intro n; induction n with
    | zero => intro v; simp
    | succ n ih => intro v; rw [Function.iterate_succ_apply', ih, List.tail_drop]
  rw [dropT, run_forN a x (tl t) G List.tail hstep (s t) s (by
    simp only [G, Function.update_eq_self])]
  rw [hit]

theorem run_dropT_blank {t x a : Fin k} (hta : t ≠ a) (s : Store k) (ha : s a = []) :
    run (dropT t x a) s = Function.update s t ((s t).drop (s x).length) := by
  rw [run_dropT hta]
  funext u
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem coinFree_dropT (t x a : Fin k) : (dropT t x a).CoinFree := rfl

theorem wf_dropT {t x a : Fin k} (hta : t ≠ a) : (dropT t x a).WF := by
  refine ⟨trivial, trivial, ?_⟩
  simp [Preserves, Prim.writes, Ne.symm hta]

/-! ### Appending a list of tapes -/

/-- Append the words of the tapes `xs`, in order. -/
def appL (o sa sb : Fin k) : List (Fin k) → Prog k
  | [] => nop o
  | x :: xs => appT o x sa sb ⨾ appL o sa sb xs

theorem run_appL {o sa sb : Fin k} (hoa : o ≠ sa) (hob : o ≠ sb) (hab : sa ≠ sb) :
    ∀ (xs : List (Fin k)) (s : Store k), s sa = [] → s sb = [] → (∀ x ∈ xs, x ≠ o) →
      run (appL o sa sb xs) s = Function.update s o (s o ++ (xs.map s).flatten)
  | [], s, _, _, _ => by simp [appL]
  | x :: xs, s, ha, hb, hx => by
    rw [appL, run_seq, run_appT_blank hoa hob hab s ha hb,
      run_appL hoa hob hab xs _ (by rw [Function.update_of_ne (Ne.symm hoa)]; exact ha)
        (by rw [Function.update_of_ne (Ne.symm hob)]; exact hb)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))]
    have hxs : ∀ y ∈ xs, Function.update s o (s o ++ s x) y = s y := fun y hy =>
      Function.update_of_ne (hx y (List.mem_cons_of_mem _ hy)) _ _
    rw [List.map_congr_left hxs, Function.update_self, Function.update_idem]
    simp [List.append_assoc]

theorem coinFree_appL (o sa sb : Fin k) : ∀ xs, (appL o sa sb xs).CoinFree
  | [] => rfl
  | x :: xs => by
    simp only [CoinFree, appL, coinFreeB, Bool.and_eq_true]
    exact ⟨coinFree_appT _ _ _ _, coinFree_appL o sa sb xs⟩

theorem wf_appL {o sa sb : Fin k} (hoa : o ≠ sa) (hba : sb ≠ sa) : ∀ xs, (appL o sa sb xs).WF
  | [] => trivial
  | _ :: xs => ⟨wf_appT hoa hba, wf_appL hoa hba xs⟩

/-- **A dynamic emitter**: `a` ones, the words of `xs`, `b` zeros. -/
def dynE (o sa sb : Fin k) (a : ℕ) (xs : List (Fin k)) (b : ℕ) : Prog k :=
  snocN o true a ⨾ appL o sa sb xs ⨾ snocN o false b

theorem run_dynE {o sa sb : Fin k} (hoa : o ≠ sa) (hob : o ≠ sb) (hab : sa ≠ sb) (a b : ℕ)
    (xs : List (Fin k)) (s : Store k) (ha : s sa = []) (hb : s sb = []) (hx : ∀ x ∈ xs, x ≠ o) :
    run (dynE o sa sb a xs b) s = Function.update s o
      (s o ++ (List.replicate a true ++ (xs.map s).flatten ++ List.replicate b false)) := by
  rw [dynE, run_seq, run_seq, run_snocN o true a s,
    run_appL hoa hob hab xs _ (by rw [Function.update_of_ne (Ne.symm hoa)]; exact ha)
      (by rw [Function.update_of_ne (Ne.symm hob)]; exact hb) hx, run_snocN]
  have hxs : ∀ y ∈ xs, Function.update s o (s o ++ List.replicate a true) y = s y := fun y hy =>
    Function.update_of_ne (hx y hy) _ _
  rw [List.map_congr_left hxs]
  simp [List.append_assoc]

theorem coinFree_dynE (o sa sb : Fin k) (a : ℕ) (xs : List (Fin k)) (b : ℕ) :
    (dynE o sa sb a xs b).CoinFree := by
  simp only [CoinFree, dynE, coinFreeB, Bool.and_eq_true]
  exact ⟨coinFree_snocN _ _ _, coinFree_appL _ _ _ _, coinFree_snocN _ _ _⟩

theorem wf_dynE {o sa sb : Fin k} (hoa : o ≠ sa) (hba : sb ≠ sa) (a : ℕ) (xs : List (Fin k))
    (b : ℕ) : (dynE o sa sb a xs b).WF :=
  ⟨wf_snocN _ _ _, wf_appL hoa hba xs, wf_snocN _ _ _⟩

/-- Ones then zeros, as a unary number. -/
theorem unary_split (a b c d : ℕ) :
    List.replicate a true ++ (List.replicate b true ++ List.replicate c false) ++
        List.replicate d false =
      List.replicate (a + b) true ++ List.replicate (c + d) false := by
  rw [List.replicate_add, List.replicate_add]
  simp only [List.append_assoc]


/-! ### Dropping a constant number of bits -/

/-- Drop `n` bits of `i`. -/
def tlN (i : Fin k) : ℕ → Prog k
  | 0 => nop i
  | n + 1 => tlN i n ⨾ tl i

theorem run_tlN (i : Fin k) : ∀ (n : ℕ) (s : Store k),
    run (tlN i n) s = Function.update s i ((s i).drop n)
  | 0, s => by simp [tlN]
  | n + 1, s => by
    rw [tlN, run_seq, run_tlN i n s, run_tail]
    simp [List.tail_drop]

theorem coinFree_tlN (i : Fin k) : ∀ n, (tlN i n).CoinFree
  | 0 => rfl
  | n + 1 => by simpa [CoinFree, tlN, coinFreeB] using coinFree_tlN i n

theorem wf_tlN (i : Fin k) : ∀ n, (tlN i n).WF
  | 0 => trivial
  | n + 1 => ⟨wf_tlN i n, trivial⟩

/-! ### Counted loops on an indexed state -/

/-- **A loop of at most `N` rounds** on states indexed by the round: the body need only be known
on the rounds `j < N`. -/
theorem run_loop_count (i : Fin k) (body : Prog k) (G : ℕ → Store k) (N : ℕ)
    (hstep : ∀ j < N, ∀ w, run body (Function.update (G j) i w) = Function.update (G (j + 1)) i w) :
    ∀ (w : List Bool) (j : ℕ), j + w.length ≤ N →
      run (loop i body) (Function.update (G j) i w) = Function.update (G (j + w.length)) i []
  | [], j, _ => by rw [run_loop, Function.update_self]; rfl
  | x :: w, j, h => by
    rw [run_loop, Function.update_self, List.length_cons, Function.iterate_succ_apply]
    have h1 : run body (tailAt i (Function.update (G j) i (x :: w))) =
        Function.update (G (j + 1)) i w := by
      rw [tailAt, Function.update_self, Function.update_idem]
      exact hstep j (by simp at h; omega) w
    have h2 := run_loop_count i body G N hstep w (j + 1) (by simp at h; omega)
    rw [run_loop, Function.update_self] at h2
    rw [h1, h2, show j + 1 + w.length = j + (w.length + 1) by omega]

/-! ### Coin-freeness and the tapes written, compositionally -/

theorem CoinFree.seq' {p q : Prog k} (hp : p.CoinFree) (hq : q.CoinFree) : (p ⨾ q).CoinFree := by
  simp only [CoinFree, coinFreeB, Bool.and_eq_true]; exact ⟨hp, hq⟩

theorem CoinFree.ifBit' {i : Fin k} {p q : Prog k} (hp : p.CoinFree) (hq : q.CoinFree) :
    (ifBit i p q).CoinFree := by
  simp only [CoinFree, coinFreeB, Bool.and_eq_true]; exact ⟨hp, hq⟩

theorem CoinFree.ifBlank' {i : Fin k} {p q : Prog k} (hp : p.CoinFree) (hq : q.CoinFree) :
    (ifBlank i p q).CoinFree := by
  simp only [CoinFree, coinFreeB, Bool.and_eq_true]; exact ⟨hp, hq⟩

theorem CoinFree.loop' {i : Fin k} {p : Prog k} (hp : p.CoinFree) : (loop i p).CoinFree := hp

theorem CoinFree.prim' (q : Prim k) : (prim q).CoinFree := rfl

/-- `p` writes only tapes in `S`. -/
def WritesIn (S : Fin k → Prop) (p : Prog k) : Prop := ∀ i, ¬ S i → p.Preserves i

theorem WritesIn.seq {S : Fin k → Prop} {p q : Prog k} (hp : WritesIn S p) (hq : WritesIn S q) :
    WritesIn S (p ⨾ q) := fun i hi => ⟨hp i hi, hq i hi⟩

theorem WritesIn.ifBit {S : Fin k → Prop} {j : Fin k} {p q : Prog k} (hp : WritesIn S p)
    (hq : WritesIn S q) : WritesIn S (ifBit j p q) := fun i hi => ⟨hp i hi, hq i hi⟩

theorem WritesIn.ifBlank {S : Fin k → Prop} {j : Fin k} {p q : Prog k} (hp : WritesIn S p)
    (hq : WritesIn S q) : WritesIn S (ifBlank j p q) := fun i hi => ⟨hp i hi, hq i hi⟩

theorem WritesIn.loop {S : Fin k → Prop} {j : Fin k} {p : Prog k} (hj : S j) (hp : WritesIn S p) :
    WritesIn S (loop j p) := fun i hi => ⟨fun e => hi (e ▸ hj), hp i hi⟩

theorem WritesIn.prim {S : Fin k → Prop} (q : Prim k) (h : ∀ i ∈ q.writes, S i) :
    WritesIn S (prim q) := fun i hi hw => hi (h i hw)

theorem WritesIn.mono {S S' : Fin k → Prop} {p : Prog k} (hp : WritesIn S p) (h : ∀ i, S i → S' i) :
    WritesIn S' p := fun i hi => hp i fun hs => hi (h i hs)

theorem writesIn_snocN {S : Fin k → Prop} {o : Fin k} (ho : S o) (b : Bool) :
    ∀ n, WritesIn S (snocN o b n)
  | 0 => WritesIn.prim _ (by simp [Prim.writes, ho])
  | n + 1 => (writesIn_snocN ho b n).seq (WritesIn.prim _ (by simp [Prim.writes, ho]))

theorem writesIn_tlN {S : Fin k → Prop} {o : Fin k} (ho : S o) : ∀ n, WritesIn S (tlN o n)
  | 0 => WritesIn.prim _ (by simp [Prim.writes, ho])
  | n + 1 => (writesIn_tlN ho n).seq (WritesIn.prim _ (by simp [Prim.writes, ho]))

theorem writesIn_emitU {S : Fin k → Prop} {o : Fin k} (ho : S o) (n j : ℕ) :
    WritesIn S (emitU o n j) := (writesIn_snocN ho _ _).seq (writesIn_snocN ho _ _)

theorem writesIn_appT {S : Fin k → Prop} {o x a b : Fin k} (ho : S o) (ha : S a) (hb : S b) :
    WritesIn S (appT o x a b) :=
  (WritesIn.prim _ (by simp [Prim.writes, hb])).seq <|
    ((WritesIn.prim _ (by simp [Prim.writes, ha])).seq (WritesIn.loop ha
      ((WritesIn.prim _ (by simp [Prim.writes, ho])).seq (WritesIn.prim _ (by simp [Prim.writes, hb]))))).seq
      (WritesIn.prim _ (by simp [Prim.writes, hb]))

theorem writesIn_dropT {S : Fin k → Prop} {t x a : Fin k} (ht : S t) (ha : S a) :
    WritesIn S (dropT t x a) :=
  (WritesIn.prim _ (by simp [Prim.writes, ha])).seq
    (WritesIn.loop ha (WritesIn.prim _ (by simp [Prim.writes, ht])))

theorem writesIn_appL {S : Fin k → Prop} {o a b : Fin k} (ho : S o) (ha : S a) (hb : S b) :
    ∀ xs, WritesIn S (appL o a b xs)
  | [] => WritesIn.prim _ (by simp [Prim.writes, ho])
  | _ :: xs => (writesIn_appT ho ha hb).seq (writesIn_appL ho ha hb xs)

theorem writesIn_dynE {S : Fin k → Prop} {o a b : Fin k} (ho : S o) (ha : S a) (hb : S b)
    (n : ℕ) (xs : List (Fin k)) (m : ℕ) : WritesIn S (dynE o a b n xs m) :=
  (writesIn_snocN ho _ _).seq ((writesIn_appL ho ha hb xs).seq (writesIn_snocN ho _ _))

end Prog

end SigabaNeo.Tape
