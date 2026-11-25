import PE.Impl.ExpLUT.Prog.EncInit
import PE.Impl.ExpLUT.Prog.EncCoins

/-! # Scheme input words and the concrete encryption loader -/
namespace AdvancedEncryption.ExpLUT.Prog.EncW

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo
  SigabaNeo.Lattices.Algo.NegaG SigabaNeo.Tape SigabaNeo.Tape.Prog Matrix
open PE.BranchingProgram

@[simp] theorem takeD_encoded_append {α : Type} {n : ℕ} (e : FixedEnc α n) (a : α)
    (rest : List Bool) : takeD n (e.enc a ++ rest) = e.enc a := by
  rw [takeD_eq_take (by simp [e.length])]
  simpa only [e.length a] using (@List.take_left Bool (e.enc a) rest)

@[simp] theorem drop_encoded_append {α : Type} {n : ℕ} (e : FixedEnc α n) (a : α)
    (rest : List Bool) : (e.enc a ++ rest).drop n = rest := by
  simpa only [e.length a] using (@List.drop_left Bool (e.enc a) rest)

variable (D : Dims)

/-- The intended public-data tape writes, independent of the loading algorithm. -/
noncomputable def publicWrites (mpk : MPKt D) (x : Attribute w8) (μ : Bool) : List InitOp :=
  [.word (bSlot 4) ((matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B),
   .word (helperSlot 2) ((FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H),
   .word (autSlot 2) ((FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H),
   .word (tailSlot 4) ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a),
   .word (tailSlot 5) ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a),
   .word (tailSlot 6) ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a),
   .word (tailSlot 11) ((matE D (Fin 2) (Col D.K)).enc mpk.A0),
   .word (tailSlot 9) ((FixedEnc.fun (α := Pos)
     (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Ain),
   .word (autSlot 4) ((FixedEnc.fun (α := Fin D.b)
     (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut),
   .word (tailSlot 13) ((vecE D (Fin 2)).enc mpk.d),
   .word (tailSlot 2) (encAttribute w8 x), .word (tailSlot 3) (encAttribute w8 x),
   .word (tailSlot 15) [μ]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Loading an actual public key and plaintext sets exactly the specified tapes. -/
theorem eval_publicInitOps (S : Store 326) (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (hs : S (sourceTape 1) = (mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ])) :
    initEval (publicInitOps D) S =
      initEval (publicWrites D mpk x μ) (Function.update S (sourceTape 1) []) := by
  have hm : (mpkEnc D).enc mpk =
      (matE D (Fin 2) (BCol (Wb D) D.K)).enc mpk.B ++
      (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))).enc mpk.H ++
      (FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc mpk.a ++
      (matE D (Fin 2) (Col D.K)).enc mpk.A0 ++
      (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K)
        (matE D (Fin 2) (Col D.K)))).enc mpk.Ain ++
      (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K)
        (matE D (Fin 2) (Col D.K)))).enc mpk.Aaut ++
      (vecE D (Fin 2)).enc mpk.d := by
    simp only [mpkEnc, FixedEnc.comap, FixedEnc.prod, List.append_assoc]
  have hx : takeD 128 (encAttribute w8 x ++ [μ]) = encAttribute w8 x := by
    rw [takeD_eq_take (by simp [length_encAttribute])]
    simpa only [length_encAttribute] using (@List.take_left Bool (encAttribute w8 x) [μ])
  have hxd : (encAttribute w8 x ++ [μ]).drop 128 = [μ] := by
    simpa only [length_encAttribute] using (@List.drop_left Bool (encAttribute w8 x) [μ])
  simp only [hm, List.append_assoc] at hs
  simp [sourceTape] at hs
  funext i
  by_cases hi : i = 322
  all_goals simp [initEval, publicInitOps, publicWrites, InitOp.eval, fixedSize,
    bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape,
    hs, hi, hx, hxd, (show takeD 1 [μ] = [μ] from rfl), -List.drop_drop, takeD_encoded_append (matE D (Fin 2) (BCol (Wb D) D.K)) mpk.B,
    drop_encoded_append (matE D (Fin 2) (BCol (Wb D) D.K)) mpk.B,
    takeD_encoded_append (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))) mpk.H,
    drop_encoded_append (FixedEnc.fun (α := Jh D) (matE D (Fin 2) (Col D.K))) mpk.H,
    takeD_encoded_append (FixedEnc.fun (α := Pos) (vecE D (Col D.K))) mpk.a,
    drop_encoded_append (FixedEnc.fun (α := Pos) (vecE D (Col D.K))) mpk.a,
    takeD_encoded_append (matE D (Fin 2) (Col D.K)) mpk.A0,
    drop_encoded_append (matE D (Fin 2) (Col D.K)) mpk.A0,
    takeD_encoded_append (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))) mpk.Ain,
    drop_encoded_append (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))) mpk.Ain,
    takeD_encoded_append (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))) mpk.Aaut,
    drop_encoded_append (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (matE D (Fin 2) (Col D.K)))) mpk.Aaut,
    takeD_encoded_append (vecE D (Fin 2)) mpk.d,
    drop_encoded_append (vecE D (Fin 2)) mpk.d]

  all_goals simp [Function.update_apply, hi]

@[simp] theorem takeD_encoded {α : Type} {n : ℕ} (e : FixedEnc α n) (a : α) :
    takeD n (e.enc a) = e.enc a := takeD_of_length' (e.length a)

@[simp] theorem drop_encoded {α : Type} {n : ℕ} (e : FixedEnc α n) (a : α) :
    (e.enc a).drop n = [] := by
  simpa only [e.length a] using (@List.drop_length Bool (e.enc a))

/-- The intended coin-data writes, independently of stream splitting. -/
noncomputable def coinWrites (r : EncCoins (setting D) (Wb D) (Jh D) Pos) : List InitOp :=
  [.word (bSlot 1) ((rEnc D).enc r.s), .word (helperSlot 1) ((rEnc D).enc r.s),
   .word (autSlot 1) ((rEnc D).enc r.s), .word (tailSlot 1) ((rEnc D).enc r.s),
   .word (bSlot 5) ((vecE D (BCol (Wb D) D.K)).enc r.eb),
   .word (helperSlot 3) ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc r.eh),
   .word (autSlot 3) ((FixedEnc.fun (α := Jh D) (vecE D (Col D.K))).enc r.eh),
   .word (autSlot 5) ((FixedEnc.fun (α := Fin D.b)
     (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc r.eaut),
   .word (tailSlot 7) ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.ein),
   .word (tailSlot 8) ((FixedEnc.fun (α := Pos) (vecE D (Col D.K))).enc r.ein),
   .word (tailSlot 10) ((FixedEnc.fun (α := Pos)
     (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))).enc r.edin),
   .word (tailSlot 12) ((vecE D (Col D.K)).enc r.e0), .word (tailSlot 14) ((rEnc D).enc r.em)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Loading an actual sampled coin word assigns all copies and exhausts the coin stream. -/
theorem eval_coinInitOps (S : Store 326) (r : EncCoins (setting D) (Wb D) (Jh D) Pos)
    (hs : S (sourceTape 0) = encCoinWord D r) :
    initEval (coinInitOps D) S =
      initEval (coinWrites D r) (Function.update S (sourceTape 0) []) := by
  simp only [encCoinWord, floodEnc, FixedEnc.prod, List.append_assoc] at hs
  simp [sourceTape] at hs
  funext i
  by_cases hi : i = 321
  all_goals simp [initEval, coinInitOps, coinWrites, InitOp.eval, fixedSize,
    bSlot, helperSlot, autSlot, tailSlot, phaseSlot, coreTape, sourceTape,
    hs, hi, -List.drop_drop,
takeD_encoded_append (rEnc D) r.s,
    drop_encoded_append (rEnc D) r.s,
    takeD_encoded_append (vecE D (BCol (Wb D) D.K)) r.eb,
    drop_encoded_append (vecE D (BCol (Wb D) D.K)) r.eb,
    takeD_encoded_append (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))) r.eh,
    drop_encoded_append (FixedEnc.fun (α := Jh D) (vecE D (Col D.K))) r.eh,
    takeD_encoded_append (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))) r.eaut,
    drop_encoded_append (FixedEnc.fun (α := Fin D.b) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))) r.eaut,
    takeD_encoded_append (FixedEnc.fun (α := Pos) (vecE D (Col D.K))) r.ein,
    drop_encoded_append (FixedEnc.fun (α := Pos) (vecE D (Col D.K))) r.ein,
    takeD_encoded_append (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))) r.edin,
    drop_encoded_append (FixedEnc.fun (α := Pos) (FixedEnc.fun (α := Dig D.K) (vecE D (Col D.K)))) r.edin,
    takeD_encoded_append (vecE D (Col D.K)) r.e0,
    drop_encoded_append (vecE D (Col D.K)) r.e0, takeD_encoded (rEnc D) r.em, drop_encoded (rEnc D) r.em]
  all_goals simp [Function.update_apply, hi]

/-- Instructions that do not consume either source stream. -/
def InitOp.NoRead : InitOp → Prop
  | .read _ _ _ => False
  | _ => True

@[simp] theorem sourceTape_ne_coreTape (src : Fin 2) (dst : Fin 321) :
    sourceTape src ≠ coreTape dst := by
  simp [sourceTape, coreTape, Fin.ext_iff]; omega

@[simp] theorem coreTape_ne_sourceTape (dst : Fin 321) (src : Fin 2) :
    coreTape dst ≠ sourceTape src := (sourceTape_ne_coreTape src dst).symm

theorem InitOp.source (op : InitOp) (hn : op.NoRead) (S : Store 326) (src : Fin 2) :
    op.eval S (sourceTape src) = S (sourceTape src) := by
  cases op <;> simp_all [InitOp.NoRead, InitOp.eval]

theorem InitOp.update_source (op : InitOp) (hn : op.NoRead) (S : Store 326)
    (src : Fin 2) (w : List Bool) :
    op.eval (Function.update S (sourceTape src) w) =
      Function.update (op.eval S) (sourceTape src) w := by
  cases op with
  | read _ _ _ => exact False.elim hn
  | copy dst src' =>
    funext i
    by_cases hi : i = sourceTape src
    · subst i; simp [InitOp.eval]
    · simp [InitOp.eval, Function.update_apply, hi]
  | word dst v =>
    funext i
    by_cases hi : i = sourceTape src
    · subst i; simp [InitOp.eval]
    · simp [InitOp.eval, Function.update_apply, hi]

theorem initEval_source (ops : List InitOp) (hn : ∀ op ∈ ops, op.NoRead)
    (S : Store 326) (src : Fin 2) : initEval ops S (sourceTape src) = S (sourceTape src) := by
  induction ops generalizing S with
  | nil => rfl
  | cons op ops ih =>
    change initEval ops (op.eval S) (sourceTape src) = _
    rw [ih (fun a ha ↦ hn a (by simp [ha])) (op.eval S), op.source (hn op (by simp)) S src]

theorem initEval_update_source (ops : List InitOp) (hn : ∀ op ∈ ops, op.NoRead)
    (S : Store 326) (src : Fin 2) (w : List Bool) :
    initEval ops (Function.update S (sourceTape src) w) =
      Function.update (initEval ops S) (sourceTape src) w := by
  induction ops generalizing S with
  | nil => rfl
  | cons op ops ih =>
    change initEval ops (op.eval (Function.update S (sourceTape src) w)) = _
    rw [op.update_source (hn op (by simp)), ih (fun a ha ↦ hn a (by simp [ha]))]
    rfl

theorem initEval_append (xs ys : List InitOp) (S : Store 326) :
    initEval (xs ++ ys) S = initEval ys (initEval xs S) := by
  simp [initEval, List.foldl_append]

theorem publicWrites_noRead (mpk : MPKt D) (x : Attribute w8) (μ : Bool) :
    ∀ op ∈ publicWrites D mpk x μ, op.NoRead := by
  simp [publicWrites, InitOp.NoRead]

theorem coinWrites_noRead (r : EncCoins (setting D) (Wb D) (Jh D) Pos) :
    ∀ op ∈ coinWrites D r, op.NoRead := by
  simp [coinWrites, InitOp.NoRead]

/-- Exact initialized store: the declared public and coin data, followed by constant templates. -/
noncomputable def loadedState (S : Store 326) (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) : Store 326 :=
  initEval (templateInitOps D) (initEval (coinWrites D r)
    (initEval (publicWrites D mpk x μ)
      (Function.update (Function.update S (sourceTape 1) []) (sourceTape 0) [])))

/-- The complete executable loader agrees with the declared field placement on actual inputs. -/
theorem run_encInitP_loaded (S : Store 326) (h : InitClean S)
    (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos)
    (hpub : S (sourceTape 1) = (mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ]))
    (hcoins : S (sourceTape 0) = encCoinWord D r) :
    (encInitP D).run S = loadedState D S mpk x μ r := by
  rw [run_encInitP D S h, encInitOps, initEval_append, initEval_append,
    eval_publicInitOps D S mpk x μ hpub]
  rw [eval_coinInitOps D _ r (by
    rw [initEval_source _ (publicWrites_noRead D mpk x μ)]
    simpa [sourceTape] using hcoins)]
  rw [← initEval_update_source _ (publicWrites_noRead D mpk x μ)]
  rfl

/-- The input layout after parsing and coin generation, before initialization. -/
def encStart (coins publicWord : List Bool) : Store 326 :=
  fun i ↦ if i = sourceTape 0 then coins else if i = sourceTape 1 then publicWord else []

/-- The fully initialized scheme store with all unassigned tapes blank. -/
noncomputable def preparedState (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) : Store 326 :=
  loadedState D (fun _ ↦ []) mpk x μ r

/-- The actual initializer reaches the declared blank-scratch scheme state. -/
theorem run_encInitP_start (mpk : MPKt D) (x : Attribute w8) (μ : Bool)
    (r : EncCoins (setting D) (Wb D) (Jh D) Pos) :
    (encInitP D).run (encStart (encCoinWord D r)
      ((mpkEnc D).enc mpk ++ (encAttribute w8 x ++ [μ]))) = preparedState D mpk x μ r := by
  rw [run_encInitP_loaded D _ (by simp [InitClean, encStart, sourceTape]) mpk x μ r
    (by simp [encStart, sourceTape]) (by simp [encStart, sourceTape])]
  have hc (coins pub : List Bool) :
      Function.update (Function.update (encStart coins pub) (sourceTape 1) [])
        (sourceTape 0) [] = fun _ ↦ [] := by
    funext i
    by_cases h0 : i = sourceTape 0 <;> by_cases h1 : i = sourceTape 1 <;>
      simp_all [encStart, sourceTape, Function.update_apply]
  have hz : Function.update (Function.update (fun _ : Fin 326 ↦ ([] : List Bool))
      (sourceTape 1) []) (sourceTape 0) [] = fun _ ↦ [] := by
    funext i; simp [Function.update_apply]
  simp only [preparedState, loadedState, hc, hz]

end AdvancedEncryption.ExpLUT.Prog.EncW
