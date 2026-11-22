import SigabaNeo.Lib.Machines.Prog.Stream
import SigabaNeo.Lib.Machines.Prog.Macros
import SigabaNeo.Lib.Machines.Prog.Machine
import SigabaNeo.Lib.Machines.Prog.Arith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic

/-!
# Parsing framed words in one pass

cslib's word encodings frame their fields: `frame u` is `u` with every bit `b` written `[true, b]`,
followed by `[false]`; a list of words is the concatenation of their frames (`encList`). The
encoding of a Module-LWE pair (`Cslib.Crypto.ModuleLWE.encodeSample`) nests three levels: a frame
around the rows of a matrix, a frame around each row, a frame around each entry (a natural number in
binary, least significant bit first, variable length), followed by a list of framed numbers.

`FPS.step neg tK` is a one-bit-at-a-time parser of such words, a cascade of three frame readers
(`l1` feeds the data bits of the outer frame to `l2`, `l2` those of the row frames to `l3`, `l3`
those of the entry frames to the emitter `g3`). It emits, as fixed-width words of `K = |tK|` bits:

* the **first entry of every row** (two's complement negated when `neg`), and
* **every number after the matrix**,

each padded with `false` to `K` bits (`encE`), shifting the bits into an output register `O` of fixed
width. `foldl_step_word` is its specification on words of that shape.

`decodeP neg K T : Prog 13` is the parser as a tape program (input on tape `0`, output on tape `2`):
a setup writing the templates (the `K`-bit counter template, the output register of `T + 1` bits,
the one-bit control registers), then a deterministic, non-lengthening loop over the input bits
(`coreP`). Its output is `true` followed by the `T` emitted bits when `T` is their number
(`law_decodeP`, `decodeW_word`); `decodeM` is the explicit machine, with `run_decodeM` and its cost
(`cost_decodeM`, `time_decodeM_le`).
-/

namespace SigabaNeo.Tape

open Cslib
open Turing.MultiTapeTM (frame)

/-! ### Padding and negation of little-endian words -/

/-- `u` padded with `false` to `K` bits. -/
def padK (K : ℕ) (u : List Bool) : List Bool := u ++ List.replicate (K - u.length) false

/-- Two's complement negation, bit-serially from the least significant bit; the carry `c` records
whether a `1` was seen. -/
def negS : Bool → List Bool → List Bool
  | _, [] => []
  | c, b :: u => xor b c :: negS (c || b) u

/-- The emitted word of a number: padded to `K` bits, negated when `neg`. -/
def encE (neg : Bool) (K : ℕ) (u : List Bool) : List Bool :=
  if neg then negS false (padK K u) else padK K u

theorem length_negS : ∀ (c : Bool) (u : List Bool), (negS c u).length = u.length
  | _, [] => rfl
  | c, b :: u => by simp [negS, length_negS (c || b) u]

theorem length_padK {K : ℕ} {u : List Bool} (h : u.length ≤ K) : (padK K u).length = K := by
  simp [padK]; omega

theorem length_encE (neg : Bool) {K : ℕ} {u : List Bool} (h : u.length ≤ K) :
    (encE neg K u).length = K := by
  unfold encE; split <;> simp [length_negS, length_padK h]

theorem negS_replicate (c : Bool) : ∀ n, negS c (List.replicate n false) = List.replicate n c
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, negS, Bool.or_false, negS_replicate c n, List.replicate_succ]; simp

theorem negS_append_replicate : ∀ (c : Bool) (u : List Bool) (n : ℕ),
    negS c (u ++ List.replicate n false) = negS c u ++ List.replicate n (c || u.any id)
  | c, [], n => by simp [negS_replicate, negS]
  | c, b :: u, n => by
    rw [List.cons_append, negS, negS, negS_append_replicate (c || b) u n]
    simp [Bool.or_assoc]

/-- Shifting words into a register: two shifts are one. -/
theorem drop_shift (O x y : List Bool) {n : ℕ} (hn : n ≤ x.length) (m : ℕ) :
    ((O ++ x).drop n ++ y).drop m = (O ++ x ++ y).drop (n + m) := by
  rw [← List.drop_append_of_le_length (by simp; omega), List.drop_drop, Nat.add_comm]

/-! ### The parser on an abstract state -/

/-- The state of the parser: the phases of the three frame readers (`p1`, `p2`, `p3`: a data bit
is expected; `dn`: the outer frame is over), whether every entry is emitted (`all`: after the
matrix) or only the first of the row (`fst`), the carry `c` of the negation, the counter `C` of
the bits still to pad, and the output register `O`. -/
structure FPS where
  p1 : Bool
  dn : Bool
  p2 : Bool
  p3 : Bool
  all : Bool
  fst : Bool
  c : Bool
  C : List Bool
  O : List Bool

namespace FPS

variable (neg : Bool) (tK : List Bool)

/-- Negation is active (in the matrix, when `neg`). -/
def nact (a : FPS) : Bool := neg && !a.all

/-- A data bit of an entry: emitted (negated when active) if the entry is emitted. -/
def g3 (a : FPS) (b : Bool) : FPS :=
  if a.all || a.fst then
    { a with O := (a.O ++ [if nact neg a then xor b a.c else b]).tail,
             c := if nact neg a then a.c || b else a.c, C := a.C.tail }
  else a

/-- The end of an entry: pad an emitted entry to `K` bits. -/
def e3 (a : FPS) : FPS :=
  if a.all || a.fst then
    { a with O := (a.O ++ List.replicate a.C.length a.c).drop a.C.length, C := tK, c := false,
             fst := a.fst && a.all }
  else a

/-- The reader of the entry frames. -/
def l3 (a : FPS) (b : Bool) : FPS :=
  if a.p3 then g3 neg { a with p3 := false } b else if b then { a with p3 := true } else e3 tK a

/-- The reader of the row frames; a row's end makes the next entry the first of its row. -/
def l2 (a : FPS) (b : Bool) : FPS :=
  if a.p2 then l3 neg tK { a with p2 := false } b
  else if b then { a with p2 := true } else { a with fst := true }

/-- The reader of the outer frame; its end switches to emitting every entry. -/
def l1 (a : FPS) (b : Bool) : FPS :=
  if a.p1 then l2 neg tK { a with p1 := false } b
  else if b then { a with p1 := true } else { a with dn := true, all := true }

/-- **One input bit.** -/
def step (a : FPS) (b : Bool) : FPS := if a.dn then l3 neg tK a b else l1 neg tK a b

/-- The initial state, with the output register `O`. -/
def init (O : List Bool) : FPS :=
  ⟨false, false, false, false, false, true, false, tK, O⟩

/-! #### Fields left alone -/

section Fields

variable {neg tK} (a : FPS) (b : Bool)

@[simp] theorem g3_p1 : (g3 neg a b).p1 = a.p1 := by unfold g3; split <;> rfl
@[simp] theorem g3_dn : (g3 neg a b).dn = a.dn := by unfold g3; split <;> rfl
@[simp] theorem g3_p2 : (g3 neg a b).p2 = a.p2 := by unfold g3; split <;> rfl
@[simp] theorem g3_p3 : (g3 neg a b).p3 = a.p3 := by unfold g3; split <;> rfl
@[simp] theorem g3_all : (g3 neg a b).all = a.all := by unfold g3; split <;> rfl
@[simp] theorem g3_fst : (g3 neg a b).fst = a.fst := by unfold g3; split <;> rfl
@[simp] theorem e3_p1 : (e3 tK a).p1 = a.p1 := by unfold e3; split <;> rfl
@[simp] theorem e3_dn : (e3 tK a).dn = a.dn := by unfold e3; split <;> rfl
@[simp] theorem e3_p2 : (e3 tK a).p2 = a.p2 := by unfold e3; split <;> rfl
@[simp] theorem e3_p3 : (e3 tK a).p3 = a.p3 := by unfold e3; split <;> rfl
@[simp] theorem e3_all : (e3 tK a).all = a.all := by unfold e3; split <;> rfl

@[simp] theorem l3_p1 : (l3 neg tK a b).p1 = a.p1 := by
  unfold l3; split
  · simp
  · split <;> simp
@[simp] theorem l3_dn : (l3 neg tK a b).dn = a.dn := by
  unfold l3; split
  · simp
  · split <;> simp
@[simp] theorem l3_p2 : (l3 neg tK a b).p2 = a.p2 := by
  unfold l3; split
  · simp
  · split <;> simp
@[simp] theorem l3_all : (l3 neg tK a b).all = a.all := by
  unfold l3; split
  · simp
  · split <;> simp
@[simp] theorem l2_p1 : (l2 neg tK a b).p1 = a.p1 := by
  unfold l2; split
  · simp
  · split <;> simp
@[simp] theorem l2_dn : (l2 neg tK a b).dn = a.dn := by
  unfold l2; split
  · simp
  · split <;> simp

end Fields

/-! #### One frame at each level -/

theorem with_p3 (a : FPS) (h : a.p3 = false) : { { a with p3 := true } with p3 := false } = a := by
  cases a; cases h; rfl

theorem with_p2 (a : FPS) (h : a.p2 = false) : { { a with p2 := true } with p2 := false } = a := by
  cases a; cases h; rfl

theorem with_p1 (a : FPS) (h : a.p1 = false) : { { a with p1 := true } with p1 := false } = a := by
  cases a; cases h; rfl

/-- **An entry frame**: its data bits go to `g3`, its end to `e3`. -/
theorem foldl_l3_frame (u : List Bool) (a : FPS) (h : a.p3 = false) :
    (frame u).foldl (l3 neg tK) a = e3 tK (u.foldl (g3 neg) a) := by
  unfold frame
  rw [List.foldl_append]
  have key : ∀ (u : List Bool) (a : FPS), a.p3 = false →
      (u.flatMap fun b => [true, b]).foldl (l3 neg tK) a = u.foldl (g3 neg) a ∧
        (u.foldl (g3 neg) a).p3 = false := by
    intro u
    induction u with
    | nil => intro a h; exact ⟨rfl, h⟩
    | cons b u ih =>
      intro a h
      have h1 : l3 neg tK a true = { a with p3 := true } := by simp [l3, h]
      have h2 : l3 neg tK { a with p3 := true } b = g3 neg a b := by
        rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩; subst h; simp [l3]
      have := ih (g3 neg a b) (by simp [h])
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, h1, h2,
        this.1]
      exact ⟨trivial, this.2⟩
  obtain ⟨k1, k2⟩ := key u a h
  rw [k1, List.foldl_cons, List.foldl_nil]
  simp [l3, k2]

/-- **A row frame**: its data bits go to `l3`; its end makes the next entry first. -/
theorem foldl_l2_frame (x : List Bool) (a : FPS) (h : a.p2 = false) :
    (frame x).foldl (l2 neg tK) a = { x.foldl (l3 neg tK) a with fst := true } := by
  unfold frame
  rw [List.foldl_append]
  have key : ∀ (u : List Bool) (a : FPS), a.p2 = false →
      (u.flatMap fun b => [true, b]).foldl (l2 neg tK) a = u.foldl (l3 neg tK) a ∧
        (u.foldl (l3 neg tK) a).p2 = false := by
    intro u
    induction u with
    | nil => intro a h; exact ⟨rfl, h⟩
    | cons b u ih =>
      intro a h
      have h1 : l2 neg tK a true = { a with p2 := true } := by simp [l2, h]
      have h2 : l2 neg tK { a with p2 := true } b = l3 neg tK a b := by
        rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩; subst h; simp [l2]
      have := ih (l3 neg tK a b) (by simp [h])
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, h1, h2,
        this.1]
      exact ⟨trivial, this.2⟩
  obtain ⟨k1, k2⟩ := key x a h
  rw [k1, List.foldl_cons, List.foldl_nil]
  simp [l2, k2]

/-- **The outer frame**: its data bits go to `l2`; its end switches to emitting every entry. -/
theorem foldl_step_frame (x : List Bool) (a : FPS) (h1 : a.p1 = false) (hd : a.dn = false) :
    (frame x).foldl (step neg tK) a = { x.foldl (l2 neg tK) a with dn := true, all := true } := by
  unfold frame
  rw [List.foldl_append]
  have key : ∀ (u : List Bool) (a : FPS), a.p1 = false → a.dn = false →
      (u.flatMap fun b => [true, b]).foldl (step neg tK) a = u.foldl (l2 neg tK) a ∧
        (u.foldl (l2 neg tK) a).p1 = false ∧ (u.foldl (l2 neg tK) a).dn = false := by
    intro u
    induction u with
    | nil => intro a h hd; exact ⟨rfl, h, hd⟩
    | cons b u ih =>
      intro a h hd
      have e1 : step neg tK a true = { a with p1 := true } := by simp [step, l1, h, hd]
      have e2 : step neg tK { a with p1 := true } b = l2 neg tK a b := by
        rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩; subst h hd; simp [step, l1]
      have := ih (l2 neg tK a b) (by simp [h]) (by simp [hd])
      simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, e1, e2,
        this.1]
      exact ⟨trivial, this.2⟩
  obtain ⟨k1, k2, k3⟩ := key x a h1 hd
  rw [k1, List.foldl_cons, List.foldl_nil]
  simp [step, l1, k2, k3]

/-! #### Emitting an entry -/

/-- The bits written for the data bits `u` (negated when `n`, from the carry `c`). -/
def outS (n c : Bool) (u : List Bool) : List Bool := if n then negS c u else u

/-- The data bits of an emitted entry. -/
theorem foldl_g3 : ∀ (u : List Bool) (a : FPS), (a.all || a.fst) = true →
    u.foldl (g3 neg) a =
      { a with O := (a.O ++ outS (nact neg a) a.c u).drop u.length,
               c := if nact neg a then a.c || u.any id else a.c, C := a.C.drop u.length }
  | [], a, _ => by cases a; simp [outS, negS]
  | b :: u, a, h => by
    rw [List.foldl_cons, foldl_g3 u (g3 neg a b) (by simpa using h)]
    obtain ⟨p1, dn, p2, p3, al, f, c, C, O⟩ := a
    simp only at h
    simp only [g3, h, ite_true, nact, outS]
    cases neg <;> cases al <;>
      simp [negS, List.drop_tail, tail_append_drop, Bool.or_assoc]

/-- **An emitted entry** of at most `K` bits: its word `encE` is shifted into the register. -/
theorem foldl_l3_emit (u : List Bool) (a : FPS) (hp : a.p3 = false) (he : (a.all || a.fst) = true)
    (hc : a.c = false) (hC : a.C = tK) (hu : u.length ≤ tK.length) :
    (frame u).foldl (l3 neg tK) a =
      { a with O := (a.O ++ encE (nact neg a) tK.length u).drop tK.length,
               fst := a.fst && a.all } := by
  rw [foldl_l3_frame neg tK u a hp, foldl_g3 neg u a he]
  obtain ⟨p1, dn, p2, p3, al, f, c, C, O⟩ := a
  simp only at hp he hc hC ⊢
  subst hc hC
  simp only [e3, he, ite_true, List.length_drop]
  congr 1
  · rw [drop_shift _ _ _ (by unfold outS; split <;> simp [length_negS]),
      Nat.add_sub_cancel' hu, List.append_assoc]
    congr 2
    unfold encE outS padK
    cases nact neg ⟨p1, dn, p2, p3, al, f, false, C, O⟩ <;> simp [negS_append_replicate]

/-- A skipped entry changes nothing. -/
theorem foldl_l3_skip (u : List Bool) (a : FPS) (hp : a.p3 = false) (ha : a.all = false)
    (hf : a.fst = false) : (frame u).foldl (l3 neg tK) a = a := by
  rw [foldl_l3_frame neg tK u a hp]
  have : ∀ (u : List Bool), u.foldl (g3 neg) a = a := by
    intro u
    induction u with
    | nil => rfl
    | cons b u ih => rw [List.foldl_cons, show g3 neg a b = a by simp [g3, ha, hf], ih]
  rw [this]
  simp [e3, ha, hf]

theorem foldl_flatMap {α β : Type} (f : α → List β) (g : FPS → β → FPS) :
    ∀ (l : List α) (a : FPS), (l.flatMap f).foldl g a = l.foldl (fun a x => (f x).foldl g a) a
  | [], _ => rfl
  | x :: l, a => by rw [List.flatMap_cons, List.foldl_append, foldl_flatMap f g l]; rfl

/-! #### The words of the shape of the Module-LWE encoding -/

/-- The word of a row: its framed entries, framed. -/
def rowW (r : List (List Bool)) : List Bool := frame (r.flatMap frame)

/-- **A row**: its first entry is emitted. -/
theorem foldl_l2_row (u : List Bool) (rest : List (List Bool)) (a : FPS) (h2 : a.p2 = false)
    (h3 : a.p3 = false) (ha : a.all = false) (hf : a.fst = true) (hc : a.c = false)
    (hC : a.C = tK) (hu : u.length ≤ tK.length) :
    (rowW (u :: rest)).foldl (l2 neg tK) a =
      { a with O := (a.O ++ encE neg tK.length u).drop tK.length } := by
  rw [rowW, foldl_l2_frame neg tK _ a h2, List.flatMap_cons, List.foldl_append,
    foldl_l3_emit neg tK u a h3 (by simp [hf]) hc hC hu]
  have hs : ∀ (l : List (List Bool)) (b : FPS), b.p3 = false → b.all = false → b.fst = false →
      (l.flatMap frame).foldl (l3 neg tK) b = b := by
    intro l
    induction l with
    | nil => intro b _ _ _; rfl
    | cons x l ih =>
      intro b hp ha hf
      rw [List.flatMap_cons, List.foldl_append, foldl_l3_skip neg tK x b hp ha hf, ih b hp ha hf]
  rw [hs rest _ (by simpa using h3) (by simpa using ha) (by simp [ha])]
  obtain ⟨p1, dn, p2, p3, al, f, c, C, O⟩ := a
  simp only at ha hf ⊢
  subst ha hf
  simp [nact]

/-- **The rows**: the first entry of each is emitted, in order. -/
theorem foldl_l2_rows (rows : List (List (List Bool))) (hne : ∀ r ∈ rows, r ≠ [])
    (hK : ∀ r ∈ rows, (r.headD []).length ≤ tK.length) (O : List Bool) :
    (rows.flatMap rowW).foldl (l2 neg tK) (init tK O) =
      init tK ((O ++ rows.flatMap fun r => encE neg tK.length (r.headD [])).drop
        (rows.length * tK.length)) := by
  induction rows generalizing O with
  | nil => simp [init]
  | cons r rows ih =>
    obtain ⟨u, rest, rfl⟩ : ∃ u rest, r = u :: rest := List.exists_cons_of_ne_nil (hne _ List.mem_cons_self)
    rw [List.flatMap_cons, List.foldl_append,
      foldl_l2_row neg tK u rest _ rfl rfl rfl rfl rfl rfl (by simpa using hK _ List.mem_cons_self)]
    change List.foldl (l2 neg tK) (init tK ((O ++ encE neg tK.length u).drop tK.length))
      (rows.flatMap rowW) = _
    rw [ih (fun r hr => hne r (by simp [hr])) (fun r hr => hK r (by simp [hr])),
      drop_shift _ _ _ (by rw [length_encE _ (by simpa using hK _ List.mem_cons_self)]),
      List.flatMap_cons, List.append_assoc, List.length_cons, Nat.succ_mul, Nat.add_comm]
    rfl

/-- **The numbers after the matrix**: every one is emitted, not negated. -/
theorem foldl_l3_all (us : List (List Bool)) (hK : ∀ u ∈ us, u.length ≤ tK.length) (a : FPS)
    (h3 : a.p3 = false) (ha : a.all = true) (hc : a.c = false) (hC : a.C = tK) :
    (us.flatMap frame).foldl (l3 neg tK) a =
      { a with O := (a.O ++ us.flatMap (encE false tK.length)).drop (us.length * tK.length) } := by
  induction us generalizing a with
  | nil => simp
  | cons u us ih =>
    rw [List.flatMap_cons, List.foldl_append,
      foldl_l3_emit neg tK u a h3 (by simp [ha]) hc hC (hK u (by simp)),
      ih (fun u hu => hK u (by simp [hu])) _ (by simpa using h3) (by simpa using ha)
        (by simpa using hc) (by simpa using hC)]
    obtain ⟨p1, dn, p2, p3, al, f, c, C, O⟩ := a
    simp only at ha ⊢
    subst ha
    simp only [nact, Bool.not_true, Bool.and_false, Bool.and_true, FPS.mk.injEq, true_and]
    rw [drop_shift _ _ _ (by rw [length_encE _ (hK u (by simp))]), List.flatMap_cons,
      List.append_assoc, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- **The parser on a word of the shape of the Module-LWE encoding**: the rows of a matrix (each a
nonempty list of entries), then numbers; the first entry of each row (negated when `neg`), then the
numbers, are shifted into the register, `K = |tK|` bits each. -/
theorem foldl_step_word (rows : List (List (List Bool))) (us : List (List Bool))
    (hne : ∀ r ∈ rows, r ≠ []) (hK : ∀ r ∈ rows, (r.headD []).length ≤ tK.length)
    (hKu : ∀ u ∈ us, u.length ≤ tK.length) (O : List Bool) :
    ((frame (rows.flatMap rowW) ++ us.flatMap frame).foldl (step neg tK) (init tK O)).O =
      (O ++ ((rows.flatMap fun r => encE neg tK.length (r.headD [])) ++
        us.flatMap (encE false tK.length))).drop ((rows.length + us.length) * tK.length) := by
  rw [List.foldl_append, foldl_step_frame neg tK _ _ rfl rfl, foldl_l2_rows neg tK rows hne hK]
  set a : FPS := { init tK ((O ++ rows.flatMap fun r => encE neg tK.length (r.headD [])).drop
    (rows.length * tK.length)) with dn := true, all := true }
  have hst : ∀ (l : List Bool) (b : FPS), b.dn = true → l.foldl (step neg tK) b = l.foldl (l3 neg tK) b := by
    intro l
    induction l with
    | nil => intro b _; rfl
    | cons x l ih => intro b hb; rw [List.foldl_cons, List.foldl_cons, show step neg tK b x = l3 neg tK b x by
        simp [step, hb], ih _ (by simpa using hb)]
  rw [hst _ a rfl, foldl_l3_all neg tK us hKu a rfl rfl rfl rfl]
  have hl : rows.length * tK.length ≤
      (rows.flatMap fun r => encE neg tK.length (r.headD [])).length := by
    rw [List.length_flatMap]
    have : ∀ (l : List (List (List Bool))), (∀ r ∈ l, (r.headD []).length ≤ tK.length) →
        (l.map fun r => (encE neg tK.length (r.headD [])).length).sum = l.length * tK.length := by
      intro l hl
      induction l with
      | nil => simp
      | cons r l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul,
          length_encE _ (hl r (by simp)), ih (fun r hr => hl r (by simp [hr]))]
        omega
    rw [this rows hK]
  simp only [a, init]
  rw [drop_shift _ _ _ hl, List.append_assoc, Nat.add_mul]

end FPS

/-! ### The parser as a tape program -/

namespace Prog

open scoped Prog

/-! Tapes: `0` the input stream, `1` the loop counter, `2` the output register `O`, `3` the pad
counter `C`, `4` the template `tK`, `5` the current bit; the one-bit registers `6` `p1`, `7` `dn`,
`8` `p2`, `9` `p3`, `10` `all`, `11` `fst`, `12` `c`. -/

/-- A data bit of an entry (`FPS.g3`). -/
def fpG3 (neg : Bool) : Prog 13 :=
  br 10 fun al => br 11 fun f =>
    if al || f then
      br 12 fun cb => br 5 fun b =>
        sin (if neg && !al then xor b cb else b) 2 ⨾ sin (if neg && !al then cb || b else cb) 12 ⨾ tl 3
    else nop 5

/-- Shift `|C|` copies of the carry into the register. -/
def fpPad : Prog 13 := loop 3 (br 12 fun cb => sin cb 2)

/-- The end of an entry (`FPS.e3`). -/
def fpE3 : Prog 13 :=
  br 10 fun al => br 11 fun f =>
    if al || f then fpPad ⨾ cp 3 4 ⨾ sin false 12 ⨾ sin (f && al) 11 else nop 5

/-- The reader of the entry frames (`FPS.l3`). -/
def fpL3 (neg : Bool) : Prog 13 :=
  br 9 fun p => if p then sin false 9 ⨾ fpG3 neg else br 5 fun b => if b then sin true 9 else fpE3

/-- The reader of the row frames (`FPS.l2`). -/
def fpL2 (neg : Bool) : Prog 13 :=
  br 8 fun p => if p then sin false 8 ⨾ fpL3 neg else br 5 fun b => if b then sin true 8 else sin true 11

/-- The reader of the outer frame (`FPS.l1`). -/
def fpL1 (neg : Bool) : Prog 13 :=
  br 6 fun p => if p then sin false 6 ⨾ fpL2 neg
    else br 5 fun b => if b then sin true 6 else sin true 7 ⨾ sin true 10

/-- One input bit (`FPS.step`). -/
def fpStep (neg : Bool) : Prog 13 := br 7 fun d => if d then fpL3 neg else fpL1 neg

/-- A round of the main loop: pop the next input bit, parse it. -/
def fpBody (neg : Bool) : Prog 13 := pp 0 5 ⨾ fpStep neg ⨾ clr 5

/-- **The parsing loop** (deterministic, non-lengthening): from the templates, one round per input
bit. -/
def coreP (neg : Bool) : Prog 13 := cp 3 4 ⨾ sin true 2 ⨾ cp 1 0 ⨾ loop 1 (fpBody neg)

/-- The setup: the template of `K` bits, the output register of `T + 1` bits, the one-bit
registers. -/
def setupP (K T : ℕ) : Prog 13 :=
  setConst 4 (List.replicate K false) ⨾ setConst 2 (List.replicate (T + 1) false) ⨾
    setConst 6 [false] ⨾ setConst 7 [false] ⨾ setConst 8 [false] ⨾ setConst 9 [false] ⨾
    setConst 10 [false] ⨾ setConst 11 [true] ⨾ setConst 12 [false]

/-- **The parser**: input on tape `0`, output on tape `2`. -/
def decodeP (neg : Bool) (K T : ℕ) : Prog 13 := setupP K T ⨾ coreP neg

/-! #### The stores of the abstract states -/

/-- The store of the abstract state `a`, with the stream `W`, the counter `q`, the bit tape `x`. -/
def fpSt (tK W q x : List Bool) (a : FPS) : Store 13 :=
  ![W, q, a.O, a.C, tK, x, [a.p1], [a.dn], [a.p2], [a.p3], [a.all], [a.fst], [a.c]]

section St

variable (tK W q x : List Bool) (a : FPS)

@[simp] theorem fpSt_0 : fpSt tK W q x a 0 = W := rfl
@[simp] theorem fpSt_1 : fpSt tK W q x a 1 = q := rfl
@[simp] theorem fpSt_2 : fpSt tK W q x a 2 = a.O := rfl
@[simp] theorem fpSt_3 : fpSt tK W q x a 3 = a.C := rfl
@[simp] theorem fpSt_4 : fpSt tK W q x a 4 = tK := rfl
@[simp] theorem fpSt_5 : fpSt tK W q x a 5 = x := rfl
@[simp] theorem fpSt_6 : fpSt tK W q x a 6 = [a.p1] := rfl
@[simp] theorem fpSt_7 : fpSt tK W q x a 7 = [a.dn] := rfl
@[simp] theorem fpSt_8 : fpSt tK W q x a 8 = [a.p2] := rfl
@[simp] theorem fpSt_9 : fpSt tK W q x a 9 = [a.p3] := rfl
@[simp] theorem fpSt_10 : fpSt tK W q x a 10 = [a.all] := rfl
@[simp] theorem fpSt_11 : fpSt tK W q x a 11 = [a.fst] := rfl
@[simp] theorem fpSt_12 : fpSt tK W q x a 12 = [a.c] := rfl

@[simp] theorem fpSt_upd0 (v : List Bool) :
    Function.update (fpSt tK W q x a) 0 v = fpSt tK v q x a := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd1 (v : List Bool) :
    Function.update (fpSt tK W q x a) 1 v = fpSt tK W v x a := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd2 (v : List Bool) :
    Function.update (fpSt tK W q x a) 2 v = fpSt tK W q x { a with O := v } := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd3 (v : List Bool) :
    Function.update (fpSt tK W q x a) 3 v = fpSt tK W q x { a with C := v } := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd5 (v : List Bool) :
    Function.update (fpSt tK W q x a) 5 v = fpSt tK W q v a := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd6 (b : Bool) :
    Function.update (fpSt tK W q x a) 6 [b] = fpSt tK W q x { a with p1 := b } := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd7 (b : Bool) :
    Function.update (fpSt tK W q x a) 7 [b] = fpSt tK W q x { a with dn := b } := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd8 (b : Bool) :
    Function.update (fpSt tK W q x a) 8 [b] = fpSt tK W q x { a with p2 := b } := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd9 (b : Bool) :
    Function.update (fpSt tK W q x a) 9 [b] = fpSt tK W q x { a with p3 := b } := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd10 (b : Bool) :
    Function.update (fpSt tK W q x a) 10 [b] = fpSt tK W q x { a with all := b } := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd11 (b : Bool) :
    Function.update (fpSt tK W q x a) 11 [b] = fpSt tK W q x { a with fst := b } := by
  funext t; fin_cases t <;> rfl
@[simp] theorem fpSt_upd12 (b : Bool) :
    Function.update (fpSt tK W q x a) 12 [b] = fpSt tK W q x { a with c := b } := by
  funext t; fin_cases t <;> rfl

end St

/-! #### Each block realizes its abstract step -/

section Blocks

variable (neg : Bool) (tK W q x : List Bool)

theorem run_fpG3 (a : FPS) :
    run (fpG3 neg) (fpSt tK W q x a) = fpSt tK W q x (FPS.g3 neg a (hd x)) := by
  rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩
  simp only [fpG3, run_br, fpSt_10, fpSt_11, hd_cons, FPS.g3, FPS.nact]
  cases al <;> cases f <;> cases c <;> cases hx : hd x <;> simp [hx]

theorem iter_shift (c : Bool) : ∀ (n : ℕ) (O : List Bool),
    (fun O : List Bool => (O ++ [c]).tail)^[n] O = (O ++ List.replicate n c).drop n
  | 0, O => by simp
  | n + 1, O => by
    rw [Function.iterate_succ_apply, iter_shift c n, tail_append_drop, List.replicate_succ]

theorem run_fpPad (a : FPS) :
    run fpPad (fpSt tK W q x a) =
      fpSt tK W q x { a with O := (a.O ++ List.replicate a.C.length a.c).drop a.C.length, C := [] } := by
  have h := run_loop_iter 3 (br 12 fun cb => sin cb 2) (fun O => fpSt tK W q x { a with O := O })
    (fun O => (O ++ [a.c]).tail) (fun _ => True) (fun O w _ => by simp) (fun _ _ => trivial)
    a.C a.O trivial
  simp only [fpSt_upd3] at h
  rw [iter_shift] at h
  exact h

theorem run_fpE3 (a : FPS) : run fpE3 (fpSt tK W q x a) = fpSt tK W q x (FPS.e3 tK a) := by
  rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩
  simp only [fpE3, run_br, fpSt_10, fpSt_11, hd_cons, FPS.e3]
  cases al <;> cases f <;> simp [run_fpPad]

theorem run_fpL3 (a : FPS) : run (fpL3 neg) (fpSt tK W q x a) = fpSt tK W q x (FPS.l3 neg tK a (hd x)) := by
  rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩
  simp only [fpL3, run_br, fpSt_9, hd_cons, FPS.l3]
  cases p3 <;> cases hx : hd x <;> simp [hx, run_fpG3, run_fpE3]

theorem run_fpL2 (a : FPS) : run (fpL2 neg) (fpSt tK W q x a) = fpSt tK W q x (FPS.l2 neg tK a (hd x)) := by
  rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩
  simp only [fpL2, run_br, fpSt_8, hd_cons, FPS.l2]
  cases p2 <;> cases hx : hd x <;> simp [hx, run_fpL3]

theorem run_fpL1 (a : FPS) : run (fpL1 neg) (fpSt tK W q x a) = fpSt tK W q x (FPS.l1 neg tK a (hd x)) := by
  rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩
  simp only [fpL1, run_br, fpSt_6, hd_cons, FPS.l1]
  cases p1 <;> cases hx : hd x <;> simp [hx, run_fpL2]

theorem run_fpStep (a : FPS) :
    run (fpStep neg) (fpSt tK W q x a) = fpSt tK W q x (FPS.step neg tK a (hd x)) := by
  rcases a with ⟨p1, dn, p2, p3, al, f, c, C, O⟩
  simp only [fpStep, run_br, fpSt_7, hd_cons, FPS.step]
  cases dn <;> simp [run_fpL3, run_fpL1]

theorem run_fpBody (a : FPS) :
    run (fpBody neg) (fpSt tK W q [] a) = fpSt tK W.tail q [] (FPS.step neg tK a (hd W)) := by
  simp [fpBody, run_fpStep]

end Blocks

/-- The parser's abstract run over a stream. -/
theorem iter_fp (neg : Bool) (tK : List Bool) : ∀ (W : List Bool) (a : FPS),
    (fun p : List Bool × FPS => (p.1.tail, FPS.step neg tK p.2 (hd p.1)))^[W.length] (W, a) =
      ([], W.foldl (FPS.step neg tK) a)
  | [], _ => rfl
  | b :: W, a => by
    rw [List.length_cons, Function.iterate_succ_apply]
    exact iter_fp neg tK W (FPS.step neg tK a b)

/-- **The parsing loop.** -/
theorem run_coreP (neg : Bool) (tK w O : List Bool) :
    run (coreP neg) (fpSt tK w [] [] ⟨false, false, false, false, false, true, false, [], O⟩) =
      fpSt tK [] [] [] (w.foldl (FPS.step neg tK) (FPS.init tK ((O ++ [true]).tail))) := by
  have h := run_loop_iter 1 (fpBody neg) (fun p : List Bool × FPS => fpSt tK p.1 [] [] p.2)
    (fun p => (p.1.tail, FPS.step neg tK p.2 (hd p.1))) (fun _ => True)
    (fun p w _ => by simp [run_fpBody]) (fun _ _ => trivial) w (w, FPS.init tK ((O ++ [true]).tail))
    trivial
  simp only [fpSt_upd1, iter_fp] at h
  simp only [coreP, run_seq, run_copy, run_sin, fpSt_4, fpSt_2, fpSt_upd3, fpSt_upd2, fpSt_0, fpSt_upd1]
  exact h

/-- The store after the setup. -/
theorem setup_store (K T : ℕ) (w : List Bool) :
    (setupP K T).denote (inputStore 0 w) =
      pure (fpSt (List.replicate K false) w [] []
        ⟨false, false, false, false, false, true, false, [], List.replicate (T + 1) false⟩) := by
  simp only [setupP, denote, denote_setConst, pure_bind]
  congr 1
  funext t
  fin_cases t <;> rfl

theorem noGrow_coreP (neg : Bool) : (coreP neg).NoGrow := by cases neg <;> decide

/-- The output of the parser: the register after the parsing loop. -/
def decodeW (neg : Bool) (K T : ℕ) (w : List Bool) : List Bool :=
  (w.foldl (FPS.step neg (List.replicate K false))
    (FPS.init (List.replicate K false) ((List.replicate (T + 1) false ++ [true]).tail))).O

/-- **The law of the parser**: a point mass. -/
theorem law_decodeP (neg : Bool) (K T : ℕ) (w : List Bool) :
    (law (decodeP neg K T) (inputStore 0 w)).map (fun s => s 2) = PMF.pure (decodeW neg K T w) := by
  rw [law, decodeP, denote, setup_store, pure_bind, denote_eq_run _ (noGrow_coreP neg),
    ProbComp.eval_pure, PMF.pure_map, run_coreP]
  rfl

/-- **The parser on a word of the shape of the Module-LWE encoding**: `true`, then the emitted
words, when `T` is their total length. -/
theorem decodeW_word (neg : Bool) (K : ℕ) (rows : List (List (List Bool))) (us : List (List Bool))
    (hne : ∀ r ∈ rows, r ≠ []) (hK : ∀ r ∈ rows, (r.headD []).length ≤ K)
    (hKu : ∀ u ∈ us, u.length ≤ K) :
    decodeW neg K ((rows.length + us.length) * K) (frame (rows.flatMap FPS.rowW) ++ us.flatMap frame) =
      true :: ((rows.flatMap fun r => encE neg K (r.headD [])) ++ us.flatMap (encE false K)) := by
  have h := FPS.foldl_step_word neg (List.replicate K false) rows us hne (by simpa using hK)
    (by simpa using hKu) ((List.replicate ((rows.length + us.length) * K + 1) false ++ [true]).tail)
  simp only [List.length_replicate] at h
  rw [decodeW, h, List.replicate_succ, List.cons_append, List.tail_cons, List.append_assoc,
    List.drop_left' (List.length_replicate ..), List.singleton_append]

/-! #### The machine -/

theorem wf_decodeP (neg : Bool) (K T : ℕ) : (decodeP neg K T).WF :=
  ⟨⟨wf_setConst _ _, wf_setConst _ _, wf_setConst _ _, wf_setConst _ _, wf_setConst _ _,
    wf_setConst _ _, wf_setConst _ _, wf_setConst _ _, wf_setConst _ _⟩,
    wf_of_wfB (by cases neg <;> decide)⟩

/-- **The parser as an explicit machine**, for inputs of at most `n` bits. -/
noncomputable def decodeM (neg : Bool) (K T n : ℕ) : Machine := (decodeP neg K T).toMachine 0 2 n

/-- **The output of the parsing machine.** -/
theorem run_decodeM (neg : Bool) (K T n : ℕ) (w : List Bool) (hw : w.length ≤ n) :
    (decodeM neg K T n).run w = PMF.pure (decodeW neg K T w) := by
  rw [decodeM, run_toMachine _ (wf_decodeP neg K T) 0 2 n w hw, law_decodeP]

/-! #### Bounds -/

theorem setConst_cons (i : Fin k) (b : Bool) (w : List Bool) :
    setConst i (b :: w) = seq (setConst i w) (prim (.cons i b)) := rfl

theorem lenBound_setConst (i : Fin k) (w : List Bool) (L : ℕ) :
    lenBound (setConst i w) L = L + w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [setConst_cons, lenBound, ih, lenBound]
    simp [Prim.grow]; omega

theorem timeBound_setConst (i : Fin k) (w : List Bool) (L : ℕ) :
    timeBound (setConst i w) L ≤ (w.length + 1) * (2 * (L + w.length) + 5) := by
  induction w with
  | nil => simp [setConst, timeBound, Prim.pad]
  | cons b w ih =>
    rw [setConst_cons, timeBound, lenBound_setConst, timeBound]
    simp only [Prim.pad, List.length_cons]
    nlinarith

theorem size_setConst (i : Fin k) (w : List Bool) : size (setConst i w) = 36 + 60 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [setConst_cons, size, ih, size]; simp [Prim.pad]; ring

theorem lenBound_setupP (K T n : ℕ) : lenBound (setupP K T) n = n + K + T + 8 := by
  simp only [setupP, lenBound, lenBound_setConst, List.length_replicate, List.length_cons,
    List.length_nil]
  omega

theorem timeBound_setupP (K T n : ℕ) :
    timeBound (setupP K T) n ≤ (K + T + 17) * (2 * (n + K + T + 8) + 5) := by
  simp only [setupP, timeBound, lenBound_setConst, List.length_replicate,
    List.length_cons, List.length_nil]
  have B := fun (i : Fin 13) (w : List Bool) (L : ℕ) (h : L + w.length ≤ n + K + T + 8) =>
    (timeBound_setConst i w L).trans (Nat.mul_le_mul_left (w.length + 1)
      (show 2 * (L + w.length) + 5 ≤ 2 * (n + K + T + 8) + 5 by omega))
  have h1 := B 4 (List.replicate K false) n (by simp; omega)
  have h2 := B 2 (List.replicate (T + 1) false) (n + K) (by simp; omega)
  have h3 := B 6 [false] (n + K + (T + 1)) (by simp; omega)
  have h4 := B 7 [false] (n + K + (T + 1) + 1) (by simp; omega)
  have h5 := B 8 [false] (n + K + (T + 1) + 1 + 1) (by simp; omega)
  have h6 := B 9 [false] (n + K + (T + 1) + 1 + 1 + 1) (by simp; omega)
  have h7 := B 10 [false] (n + K + (T + 1) + 1 + 1 + 1 + 1) (by simp; omega)
  have h8 := B 11 [true] (n + K + (T + 1) + 1 + 1 + 1 + 1 + 1) (by simp; omega)
  have h9 := B 12 [false] (n + K + (T + 1) + 1 + 1 + 1 + 1 + 1 + 1) (by simp; omega)
  simp only [List.length_replicate, List.length_cons, List.length_nil] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  nlinarith

theorem tbC_coreP (neg : Bool) : tbC (coreP neg) = 439 := by cases neg <;> rfl
theorem tbD_coreP (neg : Bool) : tbD (coreP neg) = 3 := by cases neg <;> rfl
theorem size_coreP (neg : Bool) : size (coreP neg) = 4710 := by cases neg <;> rfl

theorem size_decodeP (neg : Bool) (K T : ℕ) : size (decodeP neg K T) = 60 * (K + T) + 5514 := by
  simp only [decodeP, setupP, size, size_setConst, size_coreP, List.length_replicate,
    List.length_cons, List.length_nil]
  ring

/-- **The clock of the parsing machine**: cubic in the input bound, the width and the length of
the output. (Every primitive of the tape language sweeps its tapes, so even one pass over the input
costs quadratic time; the bound of the deterministic fragment charges every loop the longest word.) -/
theorem totalTime_decodeP_le (neg : Bool) (K T n : ℕ) :
    totalTime (decodeP neg K T) n ≤ 500 * (n + K + T + 9) ^ 3 := by
  have hc := timeBound_le (coreP neg) (noGrow_coreP neg) (n + K + T + 8)
  rw [tbC_coreP, tbD_coreP] at hc
  have hs := timeBound_setupP K T n
  have hl : lenBound (decodeP neg K T) n = n + K + T + 8 := by
    rw [decodeP, lenBound, lenBound_setupP, lenBound_eq _ (noGrow_coreP neg)]
  have ht : timeBound (decodeP neg K T) n =
      timeBound (setupP K T) n + timeBound (coreP neg) (n + K + T + 8) := by
    rw [decodeP, timeBound, lenBound_setupP]
  rw [totalTime, ht, hl]
  set B := n + K + T + 9
  have hB : 1 ≤ B := by omega
  have e1 : (K + T + 17) * (2 * (n + K + T + 8) + 5) ≤ 45 * B ^ 3 := by
    have : (K + T + 17) * (2 * (n + K + T + 8) + 5) ≤ (9 * B) * (5 * B) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have e2 : (n + K + T + 8 + 1) ^ 3 = B ^ 3 := rfl
  have e3 : 4 * B + 4 ≤ 8 * B ^ 3 := by
    have : B ≤ B ^ 3 := Nat.le_self_pow (by norm_num) B
    omega
  rw [e2] at hc
  omega

/-- **The cost of the parsing machine**: its clock plus the description of `13` tapes and
`60 (K + T) + 5518` states. -/
theorem cost_decodeM_le (neg : Bool) (K T n : ℕ) :
    (decodeM neg K T n).cost ≤
      500 * (n + K + T + 9) ^ 3 + 6 * 3 ^ 13 * (60 * (K + T) + 5518) * (60 * (K + T) + 5574) := by
  rw [decodeM, cost_toMachine, size_decodeP]
  have h1 := totalTime_decodeP_le neg K T n
  have h2 : Machine.entryBits 13 (60 * (K + T) + 5514 + 4) 0 ≤ 60 * (K + T) + 5574 := by
    unfold Machine.entryBits
    have : Nat.size (60 * (K + T) + 5514 + 4) ≤ 60 * (K + T) + 5514 + 4 :=
      Nat.size_le.mpr (Nat.lt_two_pow_self)
    simp only [Nat.size_zero]
    omega
  have h3 := Nat.mul_le_mul_left (6 * (60 * (K + T) + 5514 + 4) * 3 ^ 13 * 3 ^ 0) h2
  have e : 6 * (60 * (K + T) + 5514 + 4) * 3 ^ 13 * 3 ^ 0 * (60 * (K + T) + 5574) =
      6 * 3 ^ 13 * (60 * (K + T) + 5518) * (60 * (K + T) + 5574) := by ring
  omega

end Prog

end SigabaNeo.Tape
