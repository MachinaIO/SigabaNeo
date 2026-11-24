import PE.Impl.ExpLUT.Prog.DecMul

/-!
# The steps of the evaluation on the ring-word machine (Dec, package F4)

`stepC i last`: `Mul` at position `i` (`mulC`), the table segment of step `i` of the predicate
word on `174` (`tblC`), the table (`lutC`), the new pair on `177` (public matrix), `176`
(encoding). **`exec_stepC`**: the pair becomes the sums of `SMul` of the pairs of `j` of the
product, i.e. `lutPK`/`lutCT` of `mulPK`/`mulCT` (`DecAlg.lutPK_eq`).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

/-- `174 :=` the predicate word (on `73`) after `i` segments of `|reg 78|` bits. -/
def tblC (i : ℕ) : Code := ofList [.cp 174 73, dropsC 174 78 i]

/-- **One step of the evaluation.** -/
def stepC (i : ℕ) (last : Bool) : Code := ofList [mulC i, tblC i, lutC last, .cp 177 162, .cp 176 163]

/-- The product of `Mul` on the public side. -/
noncomputable def mulA (A : Matrix (Fin 2) (Col D.K) (Rg D)) (Ain : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)) :
    Matrix (Fin 2) (Col D.K) (Rg D) :=
  fun r j => ∑ ri : Col D.K, (Ain (ri.1, j, ri.2) r ᵥ* (setting D).ginv A) ri

/-- The product of `Mul` on the encoding side. -/
noncomputable def mulCv (A : Matrix (Fin 2) (Col D.K) (Rg D)) (c : Col D.K → Rg D)
    (cin : Dig D.K → Col D.K → Rg D) (a bot : Col D.K → Rg D) : Col D.K → Rg D :=
  fun j => (∑ ri : Col D.K, (cin (ri.1, j, ri.2) ᵥ* (setting D).ginv A) ri) +
    (c ᵥ* (setting D).ginv ![a, bot]) j

set_option maxHeartbeats 4000000 in
theorem exec_stepC (i : ℕ) (last : Bool) (w : St) {A : Matrix (Fin 2) (Col D.K) (Rg D)}
    {c a bot : Col D.K → Rg D} {Ain : Dig D.K → Matrix (Fin 2) (Col D.K) (Rg D)}
    {cin : Dig D.K → Col D.K → Rg D} (h : MulIn D i w A c Ain cin a bot)
    {rd : RData} {P : AutPub (setting D)} {hd : AutData (setting D)} (hok : RDOk D rd P hd)
    (hH : w 59 = sH rd 0) (hh : w 67 = sh rd 0) (hAa : w 63 = sA rd 0) (hca : w 68 = sc rd 0)
    {cf : ℕ → Rg D}
    (hcoef : ∀ (w' : St) (j : ℕ), CK D.N D.K (2 ^ 22) 22 (κD D) (ρD D.N) w' → j < 2 ^ 22 →
      w' 140 = toBits 22 j → w' 141 = (w 73).drop (i * (w 78).length) →
      ((exec D.N D.K (coefC last) w') 142).length = D.N * D.K ∧
        decRM D.N D.K ((exec D.N D.K (coefC last) w') 142) = cf j ∧
        ∀ r : Fin 200, r.val ≤ 140 → (exec D.N D.K (coefC last) w') r = w' r) :
    (∃ as, (exec D.N D.K (stepC i last) w) 177 = as.flatten ∧
        RepM D as (fun r c' => ∑ j ∈ Finset.range (2 ^ 22),
          smulPK (setting D) (cf j) (bitRounds P hd (mulA A Ain, mulCv A c cin a bot) j 22).1 r c')) ∧
      (∃ cs, (exec D.N D.K (stepC i last) w) 176 = cs.flatten ∧
        RepV D cs (fun c' => ∑ j ∈ Finset.range (2 ^ 22),
          smulCT (setting D) (cf j) (bitRounds P hd (mulA A Ain, mulCv A c cin a bot) j 22).2 c')) ∧
      ∀ r : Fin 200, r.val < 80 → (exec D.N D.K (stepC i last) w) r = w r := by
  obtain ⟨⟨am, a160, q160⟩, ⟨cm, a161, q161⟩, fm⟩ := exec_mulC i w h
  set w1 := exec D.N D.K (mulC i) w
  have lo1 : ∀ r : Fin 200, r.val < 80 → w1 r = w r := fun r hr => fm r (Or.inl hr)
  set w2 := exec D.N D.K (tblC i) w1 with hw2
  have e2 : w2 = Function.update w1 174 ((w1 73).drop (i * (w1 78).length)) := by
    simp only [hw2, tblC, exec_ofList_cons, exec_ofList_nil]
    rw [exec_dropsC 174 78 (by decide)]
    simp [exec]
  have v2 : ∀ r : Fin 200, r ≠ 174 → w2 r = w1 r := fun r hr => by rw [e2, Function.update_of_ne hr]
  have hin : LIn D rd (mulA A Ain, mulCv A c cin a bot) ((w 73).drop (i * (w 78).length)) w2 :=
    { lc := h.lc.of_agree fun r hr => by rw [v2 r (by intro e; subst e; simp at hr), lo1 r hr]
      A := ⟨am, by rw [v2 160 (by decide), a160], q160⟩
      c := ⟨cm, by rw [v2 161 (by decide), a161], q161⟩
      H := by rw [v2 59 (by decide), lo1 59 (by decide), hH]
      h := by rw [v2 67 (by decide), lo1 67 (by decide), hh]
      Aa := by rw [v2 63 (by decide), lo1 63 (by decide), hAa]
      ca := by rw [v2 68 (by decide), lo1 68 (by decide), hca]
      T := by rw [e2, Function.update_self, lo1 73 (by decide), lo1 78 (by decide)] }
  obtain ⟨_, ⟨as, l162, r162⟩, ⟨cs, l163, r163⟩, fl⟩ := exec_lutC last hok hcoef hin
  set w3 := exec D.N D.K (lutC last) w2
  have e : exec D.N D.K (stepC i last) w =
      Function.update (Function.update w3 177 (w3 162)) 176 (Function.update w3 177 (w3 162) 163) := rfl
  refine ⟨⟨as, by rw [e, Function.update_of_ne (by decide), Function.update_self, l162], r162⟩,
    ⟨cs, by rw [e, Function.update_self, Function.update_of_ne (by decide), l163], r163⟩,
    fun r hr => ?_⟩
  rw [e, Function.update_of_ne (by intro e; subst e; simp at hr),
    Function.update_of_ne (by intro e; subst e; simp at hr), fl r (Or.inl hr),
    v2 r (by intro e; subst e; simp at hr), lo1 r hr]

/-! ### The steps at the scheme level -/

theorem mulA_eq (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D))
    (Ain : Dig (setting D).τ → Matrix (Fin 2) (Col (setting D).τ) (Rg D)) :
    mulA A Ain = mulPK (setting D) A Ain := by
  funext r j; exact (mulPK_eq (S := setting D) A Ain r j).symm

theorem mulCv_eq (A Cin : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (c : Col (setting D).τ → Rg D)
    (cin : Dig (setting D).τ → Col (setting D).τ → Rg D) :
    mulCv A c cin (Cin 0) (Cin 1) = mulCT (setting D) A Cin cin c := by
  funext j
  have : (![Cin 0, Cin 1] : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) = Cin := by
    funext r; fin_cases r <;> rfl
  unfold mulCv
  rw [this]
  exact (mulCT_eq (S := setting D) A Cin cin c j).symm

theorem lut_sum_eq (hb : D.b = 22) (P : AutPub (setting D)) (hd : AutData (setting D)) (cf : ℕ → Rg D)
    (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (c : Col (setting D).τ → Rg D) (r : Fin 2)
    (c' : Col (setting D).τ) :
    ∑ j ∈ Finset.range (2 ^ 22), smulPK (setting D) (cf j) (bitRounds P hd (A, c) j 22).1 r c' =
      lutPK P cf A r c' := by
  rw [lutPK_eq P cf A hd c, Matrix.sum_apply]
  simp only [setting_W, setting_b, hb]

theorem lut_sumCT_eq (hb : D.b = 22) (P : AutPub (setting D)) (hd : AutData (setting D))
    (cf : ℕ → Rg D) (A : Matrix (Fin 2) (Col (setting D).τ) (Rg D)) (c : Col (setting D).τ → Rg D)
    (c' : Col (setting D).τ) :
    ∑ j ∈ Finset.range (2 ^ 22), smulCT (setting D) (cf j) (bitRounds P hd (A, c) j 22).2 c' =
      lutCT P cf A hd c c' := by
  rw [lutCT_eq P cf A hd c, Finset.sum_apply]
  simp only [setting_W, setting_b, hb]

/-! ### The evaluation -/

/-- The first `n` steps. -/
def stepsN : ℕ → Code
  | 0 => .nop
  | n + 1 => .seq (stepsN n) (stepC n (decide (n = 15)))

/-- **`EvalPK` and `EvalCT` on the machine**: `A₀` from `61`, `c₀` from `71`, then the 16 steps. -/
def evalC : Code := ofList [.cp 177 61, .cp 176 71, stepsN 16]

variable (D) in
/-- **The inputs of the evaluation** (registers below `80`). -/
structure EvIn (C : List Bool) (pp : EvalPub (setting D) Pos) (ctd : EvalCTData (setting D) Pos)
    (rd : RData) (w : St) : Prop where
  lc : LC D w
  hC73 : w 73 = C
  r78 : w 78 = List.replicate (14 * 2 ^ 22) false
  ok : RDOk D rd pp.aut ctd.aut
  H : w 59 = sH rd 0
  h : w 67 = sh rd 0
  Aa : w 63 = sA rd 0
  ca : w 68 = sc rd 0
  A0 : ∃ as, w 61 = as.flatten ∧ RepM D as pp.A0
  c0 : ∃ cs, w 71 = cs.flatten ∧ RepV D cs ctd.c0
  Ain : ∀ i < 16, ∃ f₀ f₁, ((w 62).drop (i * famMLen D)).take (famMLen D) = famMW f₀ f₁ ∧
    (i + 1) * famMLen D ≤ (w 62).length ∧
    RepFV D f₀ (fun d => pp.Ain ((bpOf (progOf C)).read i) d 0) ∧
    RepFV D f₁ (fun d => pp.Ain ((bpOf (progOf C)).read i) d 1)
  cin : ∀ i < 16, ∃ fc, ((w 70).drop (i * (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))))).take
      (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))) = famVW fc ∧
    (i + 1) * (2 * (2 * D.K) * D.K * (2 * D.K * (D.N * D.K))) ≤ (w 70).length ∧
    RepFV D fc (ctd.cin ((bpOf (progOf C)).read i))
  a : ∀ i < 16, ∃ vs, ((w 60).drop (i * (2 * D.K * (D.N * D.K)))).take (2 * D.K * (D.N * D.K)) =
      vs.flatten ∧ (i + 1) * (2 * D.K * (D.N * D.K)) ≤ (w 60).length ∧
    RepV D vs (ctd.Cin ((bpOf (progOf C)).read i) 0)
  bot : ∀ i < 16, ∃ vs, ((w 69).drop (i * (2 * D.K * (D.N * D.K)))).take (2 * D.K * (D.N * D.K)) =
      vs.flatten ∧ (i + 1) * (2 * D.K * (D.N * D.K)) ≤ (w 69).length ∧
    RepV D vs (ctd.Cin ((bpOf (progOf C)).read i) 1)

theorem EvIn.of_agree {C : List Bool} {pp : EvalPub (setting D) Pos} {ctd : EvalCTData (setting D) Pos}
    {rd : RData} {w w' : St} (h : EvIn D C pp ctd rd w) (hw : ∀ r : Fin 200, r.val < 80 → w' r = w r) :
    EvIn D C pp ctd rd w' where
  lc := h.lc.of_agree hw
  hC73 := by rw [hw 73 (by decide), h.hC73]
  r78 := by rw [hw 78 (by decide), h.r78]
  ok := h.ok
  H := by rw [hw 59 (by decide), h.H]
  h := by rw [hw 67 (by decide), h.h]
  Aa := by rw [hw 63 (by decide), h.Aa]
  ca := by rw [hw 68 (by decide), h.ca]
  A0 := by obtain ⟨as, h1, h2⟩ := h.A0; exact ⟨as, by rw [hw 61 (by decide), h1], h2⟩
  c0 := by obtain ⟨cs, h1, h2⟩ := h.c0; exact ⟨cs, by rw [hw 71 (by decide), h1], h2⟩
  Ain i hi := by rw [hw 62 (by decide)]; exact h.Ain i hi
  cin i hi := by rw [hw 70 (by decide)]; exact h.cin i hi
  a i hi := by rw [hw 60 (by decide)]; exact h.a i hi
  bot i hi := by rw [hw 69 (by decide)]; exact h.bot i hi

set_option maxHeartbeats 4000000 in
/-- **The steps**: after `n ≤ 16` steps the pair is `(evalPKAt n, evalCTAt n)`. -/
theorem exec_stepsN (hb : D.b = 22) {C : List Bool} (hC : C.length = predLen)
    {pp : EvalPub (setting D) Pos} {ctd : EvalCTData (setting D) Pos} {rd : RData} {w : St}
    (hin : EvIn D C pp ctd rd w)
    (h177 : ∃ as, w 177 = as.flatten ∧ RepM D as pp.A0)
    (h176 : ∃ cs, w 176 = cs.flatten ∧ RepV D cs ctd.c0) :
    ∀ n ≤ 16, (∃ as, (exec D.N D.K (stepsN n) w) 177 = as.flatten ∧
        RepM D as (evalPKAt (bpOf (progOf C)) pp n)) ∧
      (∃ cs, (exec D.N D.K (stepsN n) w) 176 = cs.flatten ∧
        RepV D cs (evalCTAt (bpOf (progOf C)) pp ctd n)) ∧
      ∀ r : Fin 200, r.val < 80 → (exec D.N D.K (stepsN n) w) r = w r
  | 0, _ => ⟨h177, h176, fun _ _ => rfl⟩
  | n + 1, hn => by
    obtain ⟨⟨as, a177, rA⟩, ⟨cs, a176, rc⟩, fr⟩ := exec_stepsN hb hC hin h177 h176 n (by omega)
    set w' := exec D.N D.K (stepsN n) w
    have hin' : EvIn D C pp ctd rd w' := hin.of_agree fr
    set F := bpOf (progOf C)
    have hmul : MulIn D n w' (evalPKAt F pp n) (evalCTAt F pp ctd n) (pp.Ain (F.read n))
        (ctd.cin (F.read n)) (ctd.Cin (F.read n) 0) (ctd.Cin (F.read n) 1) :=
      { lc := hin'.lc, A := ⟨as, a177, rA⟩, c := ⟨cs, a176, rc⟩, Ain := hin'.Ain n (by omega),
        cin := hin'.cin n (by omega), a := hin'.a n (by omega), bot := hin'.bot n (by omega) }
    have l78 : (w' 78).length = 14 * 2 ^ 22 := by rw [hin'.r78, List.length_replicate]
    have hcoef : ∀ (w'' : St) (j : ℕ), CK D.N D.K (2 ^ 22) 22 (κD D) (ρD D.N) w'' → j < 2 ^ 22 →
        w'' 140 = toBits 22 j → w'' 141 = (w' 73).drop (n * (w' 78).length) →
        ((exec D.N D.K (coefC (decide (n = 15))) w'') 142).length = D.N * D.K ∧
          decRM D.N D.K ((exec D.N D.K (coefC (decide (n = 15))) w'') 142) = F.coefs (setting D) n j ∧
          ∀ r : Fin 200, r.val ≤ 140 → (exec D.N D.K (coefC (decide (n = 15))) w'') r = w'' r := by
      intro w'' j hck hj h140 h141
      rw [hin'.hC73, l78] at h141
      by_cases h15 : n = 15
      · subst h15
        have := exec_coefC_vcoef D hb w'' hck hC hj h140 (by rw [h141]; norm_num)
        simp only [decide_true]
        refine ⟨this.1, ?_, this.2.2⟩
        rw [this.2.1, BP.coefs, if_neg (by show ¬(15 + 1 < 16); omega)]
      · have := exec_coefC_alpha D hb w'' hck hC (i := n) (by omega) hj h140 (by rw [h141, mul_comm])
        simp only [h15, decide_false]
        refine ⟨this.1, ?_, this.2.2⟩
        rw [this.2.1, BP.coefs, if_pos (by show n + 1 < 16; omega)]
    obtain ⟨⟨as', b177, rb⟩, ⟨cs', b176, rcb⟩, fb⟩ := exec_stepC n (decide (n = 15)) w' hmul
      hin'.ok hin'.H hin'.h hin'.Aa hin'.ca hcoef
    refine ⟨⟨as', b177, rb.congr fun r c' => ?_⟩, ⟨cs', b176, rcb.congr fun c' => ?_⟩,
      fun r hr => by rw [show exec D.N D.K (stepsN (n + 1)) w =
        exec D.N D.K (stepC n (decide (n = 15))) w' from rfl, fb r hr, fr r hr]⟩
    · rw [mulA_eq, mulCv_eq]
      exact lut_sum_eq hb _ _ _ _ _ r c'
    · rw [mulA_eq, mulCv_eq]
      exact lut_sumCT_eq hb _ _ _ _ _ c'

/-- **`EvalPK` and `EvalCT` on the machine**: `A_F` on `177`, `c_F` on `176`. -/
theorem exec_evalC (hb : D.b = 22) {C : List Bool} (hC : C.length = predLen)
    {pp : EvalPub (setting D) Pos} {ctd : EvalCTData (setting D) Pos} {rd : RData} {w : St}
    (hin : EvIn D C pp ctd rd w) :
    (∃ as, (exec D.N D.K evalC w) 177 = as.flatten ∧ RepM D as (evalPK (bpOf (progOf C)) pp)) ∧
      (∃ cs, (exec D.N D.K evalC w) 176 = cs.flatten ∧
        RepV D cs (evalCT (bpOf (progOf C)) pp ctd)) ∧
      ∀ r : Fin 200, r.val < 80 → (exec D.N D.K evalC w) r = w r := by
  set w1 := Function.update (Function.update w 177 (w 61)) 176 (w 71) with hw1
  have e : exec D.N D.K evalC w = exec D.N D.K (stepsN 16) w1 := by
    simp only [evalC, exec_ofList_cons, exec_ofList_nil, exec, hw1]
    rw [Function.update_of_ne (by decide)]
  have lo : ∀ r : Fin 200, r.val < 80 → w1 r = w r := fun r hr => by
    rw [hw1, Function.update_of_ne (by intro e; subst e; simp at hr),
      Function.update_of_ne (by intro e; subst e; simp at hr)]
  obtain ⟨as, a61, rA⟩ := hin.A0
  obtain ⟨cs, a71, rc⟩ := hin.c0
  obtain ⟨h1, h2, h3⟩ := exec_stepsN hb hC (hin.of_agree lo)
    ⟨as, by rw [hw1, Function.update_of_ne (by decide), Function.update_self, a61], rA⟩
    ⟨cs, by rw [hw1, Function.update_self, a71], rc⟩ 16 le_rfl
  rw [e]
  exact ⟨h1, h2, fun r hr => by rw [h3 r hr, lo r hr]⟩

/-- **The evaluation of `Dec` at the scheme's objects**: on inputs representing `mpk`, `ct`
(`EvIn` with `evalPub`, `evalData`), `A_F = keyPK` on `177` and `c_F = evalCiphertext` on `176`. -/
theorem exec_evalC_scheme (hb : D.b = 22) {C : List Bool} (hC : C.length = predLen)
    {mpk : MPKt D} {ct : CTt D} {rd : RData} {w : St}
    (hin : EvIn D C (evalPub (helperMap D) mpk) (evalData (helperMap D) mpk ct) rd w) :
    (∃ as, (exec D.N D.K evalC w) 177 = as.flatten ∧
        RepM D as (keyPK (helperMap D) mpk (bpOf (progOf C)))) ∧
      (∃ cs, (exec D.N D.K evalC w) 176 = cs.flatten ∧
        RepV D cs (evalCiphertext (helperMap D) mpk (bpOf (progOf C)) ct)) ∧
      ∀ r : Fin 200, r.val < 80 → (exec D.N D.K evalC w) r = w r :=
  exec_evalC hb hC hin

end AdvancedEncryption.ExpLUT.Prog
