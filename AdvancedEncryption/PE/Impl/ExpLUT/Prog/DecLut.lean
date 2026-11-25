import PE.Impl.ExpLUT.Prog.DecRounds

/-!
# The lookup table `LUT` on the ring-word machine (Dec, package F4)

`lutC last`: one loop over `j < W = 2^22`. Round `j` recomputes the pair of `j` from the input pair
(`160`, `161`) along the bits of `j` (`roundsN 22`, the counter `J` on `140`), computes the
coefficient `α_{g^j, L}` (or `v`) from the table segment on `174` (`coefC`), the words of `α G`
(`gadC`), and accumulates `SMul_α` of the pair into `162` (public matrix) and `163` (encoding).
-/

namespace AdvancedEncryption.ExpLUT.Prog

open SigabaNeo SigabaNeo.Tape SigabaNeo.Tape.RingVM SigabaNeo.Lattices SigabaNeo.Lattices.Algo
open AdvancedEncryption.ExpLUT Matrix

variable {D : Dims}

/-! ### Helpers -/

/-- `dst := a + b` entrywise on matrices (`4K` words). -/
def addMCall (a b dst : Fin 200) : Code := ofList [.cp 110 a, .cp 111 b, vecAddC 76 7, .cp dst 112]

theorem exec_addMCall (w : St) (hw : EC D w) (a b dst : Fin 200) (ha : b ≠ 110)
    {us vs : List (List Bool)} {U V : Matrix (Fin 2) (Col D.K) (Rg D)} (hu : RepM D us U)
    (hv : RepM D vs V) (h1 : w a = us.flatten) (h2 : w b = vs.flatten) :
    (exec D.N D.K (addMCall a b dst) w) dst = (List.zipWith (addRMW D.N D.K) us vs).flatten ∧
      RepM D (List.zipWith (addRMW D.N D.K) us vs) (U + V) ∧
      Fr dst w (exec D.N D.K (addMCall a b dst) w) := by
  set w1 := Function.update (Function.update w 110 (w a)) 111 (w b) with hw1
  have hc1 : Consts D.N D.K w1 := consts_update (consts_update hw.ck.c 110 (by decide) _) 111
    (by decide) _
  obtain ⟨a112, af⟩ := exec_vecAddC w1 hc1 76 7 (by decide) hu.wid hv.wid (by rw [hu.len, hv.len])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_self, h1])
    (by rw [hw1, Function.update_self, h2])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hw.r76,
      List.length_replicate, hu.len])
    (by rw [hw1, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hw.ck.mat,
      List.length_replicate, hu.len])
  have e : exec D.N D.K (addMCall a b dst) w =
      Function.update (exec D.N D.K (vecAddC 76 7) w1) dst ((exec D.N D.K (vecAddC 76 7) w1) 112) := by
    simp only [addMCall, exec_ofList_cons, exec_ofList_nil, exec, hw1]
    rw [Function.update_of_ne ha]
  refine ⟨by rw [e, Function.update_self, a112], hu.zip_add hv, fun j hj hd => ?_⟩
  rw [e, Function.update_of_ne hd, af j (not_mem_mid rfl hj), hw1,
    Function.update_of_ne (mid_ne hj (by decide)), Function.update_of_ne (mid_ne hj (by decide))]

theorem idxM_lt (a : Fin 2) (c : Col D.K) : 2 * D.K * a.val + cidx D.K c < 4 * D.K := by
  have := cidx_lt c; have := a.isLt
  rcases (show a.val = 0 ∨ a.val = 1 by omega) with e | e <;> rw [e] <;> omega

/-- The zero matrix. -/
theorem repM_zero : RepM D (List.replicate (4 * D.K) (List.replicate (D.N * D.K) false)) 0 where
  len := List.length_replicate
  wid x hx := by rw [List.eq_of_mem_replicate hx, List.length_replicate]
  val a c := by
    rw [List.getD_eq_getElem _ _ (by simpa using idxM_lt a c), List.getElem_replicate,
      decRM_replicate]; rfl

/-- The zero vector. -/
theorem repV_zero : RepV D (List.replicate (2 * D.K) (List.replicate (D.N * D.K) false)) 0 where
  len := List.length_replicate
  wid x hx := by rw [List.eq_of_mem_replicate hx, List.length_replicate]
  val c := by
    rw [List.getD_eq_getElem _ _ (by simpa using cidx_lt c), List.getElem_replicate,
      decRM_replicate]; rfl

/-- The words of `α G`. -/
theorem repM_gad {x : List Bool} (hx : x.length = D.N * D.K) :
    RepM D (gadMatWords D.N D.K x) (decRM D.N D.K x • (setting D).G) where
  len := length_gadMatWords _ _ _
  wid _ hy := mem_gadMatWords hx hy
  val a c := by
    have := decRM_gadMatWords D hx a c
    rw [cidx, show c.1.val * D.K + c.2.val = D.K * c.1.val + c.2.val by ring, ← add_assoc]
    exact this

/-! ### One round `j` of the table -/

/-- The writes of the coefficient blocks are in `[140, 160)`. -/
theorem not_mem_coef {l : List (Fin 200)}
    (hl : l.all (fun x => decide (140 ≤ x.val ∧ x.val < 160)) = true) {j : Fin 200}
    (hj : j.val < 140 ∨ 160 ≤ j.val) : j ∉ l := fun hm => by
  have := List.all_eq_true.mp hl j hm; simp at this; omega

theorem wr_coefC_in (last : Bool) :
    (wr (coefC last)).all (fun x => decide (140 ≤ x.val ∧ x.val < 160)) = true := by
  cases last <;> rfl

/-- **One round `j` of the table.** -/
def jBody (last : Bool) : Code := ofList [.cp 120 160, .cp 121 161, .cp 164 59, .cp 165 67,
  .cp 166 63, .cp 167 68, .cp 169 140, .cp 122 7, .cp 123 7, .cp 124 6, .cp 125 6, .cp 126 77,
  .cp 127 10, .cp 170 1, roundsN 22, .cp 141 174, coefC last, gadC, matCall 120 143 171,
  addMCall 162 171 162, ginvCall 121 143 172, addCall 163 172 163, incC]

variable (D) in
/-- The constants of the table. -/
structure LC (w : St) : Prop where
  ec : EC D w
  r77 : w 77 = List.replicate (famMLen D) false

theorem LC.of_agree {w w' : St} (h : LC D w) (hw : ∀ j : Fin 200, j.val < 80 → w' j = w j) :
    LC D w' := ⟨h.ec.of_agree hw, by rw [hw 77 (by decide)]; exact h.r77⟩

variable (D) in
/-- The inputs of the table, on the registers outside `[80, 140) ∪ [160, 176)` except `162`, `163`,
`171`, `172`: the pair, the helper streams, the table segment. -/
structure LIn (rd : RData) (x : Matrix (Fin 2) (Col D.K) (Rg D) × (Col D.K → Rg D)) (T : List Bool)
    (w : St) : Prop where
  lc : LC D w
  A : ∃ as, w 160 = as.flatten ∧ RepM D as x.1
  c : ∃ cs, w 161 = cs.flatten ∧ RepV D cs x.2
  H : w 59 = sH rd 0
  h : w 67 = sh rd 0
  Aa : w 63 = sA rd 0
  ca : w 68 = sc rd 0
  T : w 174 = T

theorem LIn.of_agree {rd : RData} {x : Matrix (Fin 2) (Col D.K) (Rg D) × (Col D.K → Rg D)}
    {T : List Bool} {w w' : St} (h : LIn D rd x T w)
    (hw : ∀ j : Fin 200, (j.val < 80 ∨ j.val = 160 ∨ j.val = 161 ∨ j.val = 174) → w' j = w j) :
    LIn D rd x T w' where
  lc := h.lc.of_agree fun j hj => hw j (Or.inl hj)
  A := by obtain ⟨as, h1, h2⟩ := h.A; exact ⟨as, by rw [hw 160 (by decide), h1], h2⟩
  c := by obtain ⟨cs, h1, h2⟩ := h.c; exact ⟨cs, by rw [hw 161 (by decide), h1], h2⟩
  H := by rw [hw 59 (by decide), h.H]
  h := by rw [hw 67 (by decide), h.h]
  Aa := by rw [hw 63 (by decide), h.Aa]
  ca := by rw [hw 68 (by decide), h.ca]
  T := by rw [hw 174 (by decide), h.T]

theorem getD_toBits22 (j s : ℕ) (hs : s < 22) : (toBits 22 j).getD s false = j.testBit s := by
  rw [getD_toBits]; simp [hs]

set_option maxHeartbeats 4000000 in
/-- **One round `j` of the table**: the pair of `j`, `SMul` by the coefficient, accumulated. -/
theorem exec_jBody (last : Bool) {rd : RData} {P : AutPub (setting D)} {hd : AutData (setting D)}
    (hok : RDOk D rd P hd) {x : Matrix (Fin 2) (Col D.K) (Rg D) × (Col D.K → Rg D)} {T : List Bool}
    {cf : ℕ → Rg D}
    (hcoef : ∀ (w : St) (j : ℕ), CK D.N D.K (2 ^ 22) 22 (κD D) (ρD D.N) w → j < 2 ^ 22 →
      w 140 = toBits 22 j → w 141 = T →
      ((exec D.N D.K (coefC last) w) 142).length = D.N * D.K ∧
        decRM D.N D.K ((exec D.N D.K (coefC last) w) 142) = cf j ∧
        ∀ r : Fin 200, r.val ≤ 140 → (exec D.N D.K (coefC last) w) r = w r)
    {j : ℕ} (hj : j < 2 ^ 22) {w : St} (hin : LIn D rd x T w) (h140 : w 140 = toBits 22 j)
    {accA : Matrix (Fin 2) (Col D.K) (Rg D)} {accC : Col D.K → Rg D}
    (hA : ∃ as, w 162 = as.flatten ∧ RepM D as accA)
    (hC : ∃ cs, w 163 = cs.flatten ∧ RepV D cs accC) :
    LIn D rd x T (exec D.N D.K (jBody last) w) ∧
      (exec D.N D.K (jBody last) w) 140 = toBits 22 (j + 1) ∧
      (∃ as, (exec D.N D.K (jBody last) w) 162 = as.flatten ∧
        RepM D as (fun a c => accA a c + smulPK (setting D) (cf j) (bitRounds P hd x j 22).1 a c)) ∧
      (∃ cs, (exec D.N D.K (jBody last) w) 163 = cs.flatten ∧
        RepV D cs (fun c => accC c + smulCT (setting D) (cf j) (bitRounds P hd x j 22).2 c)) ∧
      ∀ r : Fin 200, (r.val < 80 ∨ 176 ≤ r.val) → (exec D.N D.K (jBody last) w) r = w r := by
  have hlc := hin.lc
  obtain ⟨asm, hAm0, hAm⟩ := hin.A
  obtain ⟨csm, hcm0, hcm⟩ := hin.c
  obtain ⟨acA, hacA0, hacA⟩ := hA
  obtain ⟨acC, hacC0, hacC⟩ := hC
  -- the prelude
  set u0 := exec D.N D.K (ofList [.cp 120 160, .cp 121 161, .cp 164 59, .cp 165 67, .cp 166 63,
    .cp 167 68, .cp 169 140, .cp 122 7, .cp 123 7, .cp 124 6, .cp 125 6, .cp 126 77, .cp 127 10,
    .cp 170 1]) w with hu0
  have u0v : ∀ k : Fin 200, (k.val < 120 ∨ (128 ≤ k.val ∧ k.val < 164) ∨ 171 ≤ k.val ∨ k.val = 168) →
      u0 k = w k := fun k hk => by
    have nv : ∀ d : Fin 200, (d.val = 120 ∨ d.val = 121 ∨ d.val = 122 ∨ d.val = 123 ∨ d.val = 124 ∨
        d.val = 125 ∨ d.val = 126 ∨ d.val = 127 ∨ d.val = 164 ∨ d.val = 165 ∨ d.val = 166 ∨
        d.val = 167 ∨ d.val = 169 ∨ d.val = 170) → k ≠ d := fun d hd e => by subst e; omega
    simp only [hu0, exec_ofList_cons, exec_ofList_nil, exec]
    rw [Function.update_of_ne (nv 170 (by decide)), Function.update_of_ne (nv 127 (by decide)),
      Function.update_of_ne (nv 126 (by decide)), Function.update_of_ne (nv 125 (by decide)),
      Function.update_of_ne (nv 124 (by decide)), Function.update_of_ne (nv 123 (by decide)),
      Function.update_of_ne (nv 122 (by decide)), Function.update_of_ne (nv 169 (by decide)),
      Function.update_of_ne (nv 167 (by decide)), Function.update_of_ne (nv 166 (by decide)),
      Function.update_of_ne (nv 165 (by decide)), Function.update_of_ne (nv 164 (by decide)),
      Function.update_of_ne (nv 121 (by decide)), Function.update_of_ne (nv 120 (by decide))]
  have u0s : u0 120 = w 160 ∧ u0 121 = w 161 ∧ u0 164 = w 59 ∧ u0 165 = w 67 ∧ u0 166 = w 63 ∧
      u0 167 = w 68 ∧ u0 169 = w 140 ∧ u0 122 = w 7 ∧ u0 123 = w 7 ∧ u0 124 = w 6 ∧
      u0 125 = w 6 ∧ u0 126 = w 77 ∧ u0 127 = w 10 ∧ u0 170 = w 1 := by
    simp only [hu0, exec_ofList_cons, exec_ofList_nil, exec, Function.update_apply, Fin.reduceEq,
      ↓reduceIte]
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial, trivial, trivial, trivial⟩
  obtain ⟨s120, s121, s164, s165, s166, s167, s169, s122, s123, s124, s125, s126, s127, s170⟩ := u0s
  have lc0 : LC D u0 := hlc.of_agree fun k hk => u0v k (by omega)
  have hJ := getD_toBits22 j
  have inv0 : RsInv D rd P hd x j (toBits 22 j) u0 0 u0 :=
    { ec := lc0.ec, r77 := lc0.r77
      s164 := by rw [s164, hin.H]
      s165 := by rw [s165, hin.h]
      s166 := by rw [s166, hin.Aa]
      s167 := by rw [s167, hin.ca]
      s169 := by rw [s169, h140]; rfl
      l122 := by rw [s122, hlc.ec.ck.mat, List.length_replicate]
      l123 := by rw [s123, hlc.ec.ck.mat, List.length_replicate]
      l124 := by rw [s124, hlc.ec.r6, List.length_replicate]
      l125 := by rw [s125, hlc.ec.r6, List.length_replicate]
      l126 := by rw [s126, hlc.r77, List.length_replicate]
      l127 := by rw [s127, hlc.ec.r10, List.length_replicate]
      l170 := by rw [s170, hlc.ec.ck.c.one]; rfl
      A := ⟨asm, by rw [s120, hAm0], hAm⟩
      c := ⟨csm, by rw [s121, hcm0], hcm⟩
      fr := fun _ _ => rfl }
  have inv22 := exec_roundsN hok hJ (by simp) inv0 22 le_rfl
  set u1 := exec D.N D.K (roundsN 22) u0
  obtain ⟨pas, p120, pA⟩ := inv22.A
  obtain ⟨pcs, p121, pc⟩ := inv22.c
  have u1v : ∀ k : Fin 200, (k.val < 80 ∨ (140 ≤ k.val ∧ (k.val < 164 ∨ 171 ≤ k.val))) →
      u1 k = w k := fun k hk => by
    rw [inv22.fr k hk, u0v k (by omega)]
  -- the coefficient
  set u2 := Function.update u1 141 (u1 174) with hu2
  have u2v : ∀ k : Fin 200, k ≠ 141 → u2 k = u1 k := fun k hk => by rw [hu2, Function.update_of_ne hk]
  have ec2 : EC D u2 := hlc.ec.of_agree fun k hk => by
    rw [u2v k (by intro e; subst e; simp at hk), u1v k (Or.inl hk)]
  obtain ⟨c1, c2, c3⟩ := hcoef u2 j ec2.ck hj
    (by rw [u2v 140 (by decide), u1v 140 (by decide), h140])
    (by rw [hu2, Function.update_self, u1v 174 (by decide), hin.T])
  set u3 := exec D.N D.K (coefC last) u2
  have u3v : ∀ k : Fin 200, (k.val < 140 ∨ 160 ≤ k.val) → u3 k = u2 k := fun k hk =>
    exec_not_mem _ _ k (not_mem_coef (wr_coefC_in last) hk)
  have ec3 : EC D u3 := ec2.of_agree fun k hk => u3v k (Or.inl (by omega))
  obtain ⟨g1, g2⟩ := exec_gadC_words D.K_pos u3 ec3.ck c1
  set u4 := exec D.N D.K gadC u3
  have u4v : ∀ k : Fin 200, (k.val < 140 ∨ 160 ≤ k.val) → u4 k = u3 k := fun k hk =>
    exec_not_mem _ _ k (not_mem_coef rfl hk)
  have ec4 : EC D u4 := ec3.of_agree fun k hk => u4v k (Or.inl (by omega))
  have rg := repM_gad (D := D) c1
  rw [c2] at rg
  -- SMul of the public matrix
  have a120 : u4 120 = pas.flatten := by
    rw [u4v 120 (by decide), u3v 120 (by decide), u2v 120 (by decide), p120]
  obtain ⟨sm, m171, rm, f5⟩ := exec_matCall u4 ec4 120 143 171 (by decide) pA rg a120 g1
  set u5 := exec D.N D.K (matCall 120 143 171) u4
  have ec5 := EC.of_fr ec4 f5 (by decide)
  have a162 : u5 162 = acA.flatten := by
    rw [frs f5 (by decide), u4v 162 (by decide), u3v 162 (by decide), u2v 162 (by decide),
      u1v 162 (by decide), hacA0]
  obtain ⟨n162, rn, f6⟩ := exec_addMCall u5 ec5 162 171 162 (by decide) hacA rm a162 m171
  set u6 := exec D.N D.K (addMCall 162 171 162) u5
  have ec6 := EC.of_fr ec5 f6 (by decide)
  -- SMul of the encoding
  have a121 : u6 121 = pcs.flatten := by
    rw [frs f6 (by decide), frs f5 (by decide), u4v 121 (by decide), u3v 121 (by decide),
      u2v 121 (by decide), p121]
  have a143 : u6 143 = (gadMatWords D.N D.K (u3 142)).flatten := by
    rw [frs f6 (by decide), frs f5 (by decide), g1]
  obtain ⟨sc', m172, rc, f7⟩ := exec_ginvCall u6 ec6 121 143 172 (by decide) pc rg a121 a143
  set u7 := exec D.N D.K (ginvCall 121 143 172) u6
  have ec7 := EC.of_fr ec6 f7 (by decide)
  have a163 : u7 163 = acC.flatten := by
    rw [frs f7 (by decide), frs f6 (by decide), frs f5 (by decide), u4v 163 (by decide),
      u3v 163 (by decide), u2v 163 (by decide), u1v 163 (by decide), hacC0]
  obtain ⟨n163, rn', f8⟩ := exec_addCall u7 ec7 163 172 163 (by decide) hacC rc a163 m172
  set u8 := exec D.N D.K (addCall 163 172 163) u7
  have ec8 := EC.of_fr ec7 f8 (by decide)
  -- the counter
  have a140 : u8 140 = toBits 22 j := by
    rw [frs f8 (by decide), frs f7 (by decide), frs f6 (by decide), frs f5 (by decide),
      g2 140 (by decide), c3 140 (by decide),
      u2v 140 (by decide), u1v 140 (by decide), h140]
  obtain ⟨i140, _⟩ := exec_incC_toBits u8 ec8.ck.c.one ec8.ck.one a140
  set u9 := exec D.N D.K incC u8
  have u9v : ∀ k : Fin 200, (k.val < 140 ∨ 160 ≤ k.val) → u9 k = u8 k := fun k hk =>
    exec_not_mem _ _ k (not_mem_coef rfl hk)
  have e : exec D.N D.K (jBody last) w = u9 := rfl
  have back : ∀ k : Fin 200, (k.val < 80 ∨ k.val = 160 ∨ k.val = 161 ∨ 174 ≤ k.val) → u9 k = w k :=
    fun k hk => by
      have h1 : k ≠ 163 := by intro e; subst e; simp at hk
      have h2 : k ≠ 172 := by intro e; subst e; simp at hk
      have h3 : k ≠ 162 := by intro e; subst e; simp at hk
      have h4 : k ≠ 171 := by intro e; subst e; simp at hk
      have h5 : k ≠ 141 := by intro e; subst e; simp at hk
      have hk' : k.val < 80 ∨ 120 ≤ k.val := by omega
      rw [u9v k (by omega), f8 k hk' h1, f7 k hk' h2, f6 k hk' h3, f5 k hk' h4, u4v k (by omega),
        u3v k (by omega), u2v k h5, u1v k (by omega)]
  refine ⟨hin.of_agree fun k hk => back k (by omega), by rw [e, i140], ?_, ?_, fun r hr => ?_⟩
  · refine ⟨_, by rw [e, u9v 162 (by decide), frs f8 (by decide), frs f7 (by decide), n162],
      rn.congr fun a c => ?_⟩
    show accA a c + ((bitRounds P hd x j 22).1 a ᵥ* (setting D).ginv (cf j • (setting D).G)) c = _
    exact congrArg (accA a c + ·) (congrFun (smulPK_row (S := setting D) (cf j) (bitRounds P hd x j 22).1 a) c).symm
  · exact ⟨_, by rw [e, u9v 163 (by decide), n163], rn'.congr fun c => rfl⟩
  · rw [e]; exact back r (by omega)

/-! ### The table -/

/-- **The table**: `2^22` rounds `j` from zero accumulators and `J = 0`. -/
def lutC (last : Bool) : Code := ofList [.cp 162 7, .cp 163 6, .cp 140 13, .cp 173 12, .rep 173 (jBody last)]

set_option maxRecDepth 100000 in
theorem wr_tStep_173 (n : ℕ) : (wr (tStep n)).all (fun x => x != 173) = true := by
  rfl

theorem wr_roundsN_173 : ∀ n, (wr (roundsN n)).all (fun x => x != 173) = true
  | 0 => rfl
  | n + 1 => by
    show (wr (roundsN n) ++ wr (tStep n)).all _ = true
    rw [List.all_append, wr_roundsN_173 n, wr_tStep_173 n]; rfl

set_option maxRecDepth 100000 in
theorem wr_jBody_173 (last : Bool) : (wr (jBody last)).all (fun x => x != 173) = true := by
  have e : wr (jBody last) = [120, 121, 164, 165, 166, 167, 169, 122, 123, 124, 125, 126, 127, 170] ++
      (wr (roundsN 22) ++ ([141] ++ wr (coefC last) ++ wr gadC ++ wr (matCall 120 143 171) ++
        wr (addMCall 162 171 162) ++ wr (ginvCall 121 143 172) ++ wr (addCall 163 172 163) ++
        wr incC)) := by
    simp [jBody, wr_ofList, wr]
  rw [e, List.all_append, List.all_append, wr_roundsN_173]
  cases last <;> rfl

theorem toBits_zero' : ∀ K : ℕ, toBits K 0 = List.replicate K false
  | 0 => rfl
  | K + 1 => by rw [toBits, toBits_zero' K]; simp [List.replicate_succ]

theorem toBits22_zero : toBits 22 0 = List.replicate 22 false := toBits_zero' 22

set_option maxHeartbeats 4000000 in
/-- **The table on the machine**: the sums `Σ_{j < 2^22} SMul_{cf j}` of the pairs of `j`. -/
theorem exec_lutC (last : Bool) {rd : RData} {P : AutPub (setting D)} {hd : AutData (setting D)}
    (hok : RDOk D rd P hd) {x : Matrix (Fin 2) (Col D.K) (Rg D) × (Col D.K → Rg D)} {T : List Bool}
    {cf : ℕ → Rg D}
    (hcoef : ∀ (w : St) (j : ℕ), CK D.N D.K (2 ^ 22) 22 (κD D) (ρD D.N) w → j < 2 ^ 22 →
      w 140 = toBits 22 j → w 141 = T →
      ((exec D.N D.K (coefC last) w) 142).length = D.N * D.K ∧
        decRM D.N D.K ((exec D.N D.K (coefC last) w) 142) = cf j ∧
        ∀ r : Fin 200, r.val ≤ 140 → (exec D.N D.K (coefC last) w) r = w r)
    {w : St} (hin : LIn D rd x T w) :
    LIn D rd x T (exec D.N D.K (lutC last) w) ∧
      (∃ as, (exec D.N D.K (lutC last) w) 162 = as.flatten ∧
        RepM D as (fun a c => ∑ j ∈ Finset.range (2 ^ 22),
          smulPK (setting D) (cf j) (bitRounds P hd x j 22).1 a c)) ∧
      (∃ cs, (exec D.N D.K (lutC last) w) 163 = cs.flatten ∧
        RepV D cs (fun c => ∑ j ∈ Finset.range (2 ^ 22),
          smulCT (setting D) (cf j) (bitRounds P hd x j 22).2 c)) ∧
      ∀ r : Fin 200, (r.val < 80 ∨ 176 ≤ r.val) → (exec D.N D.K (lutC last) w) r = w r := by
  have hlc := hin.lc
  set w1 := Function.update (Function.update (Function.update (Function.update w 162 (w 7)) 163
    (w 6)) 140 (w 13)) 173 (w 12) with hw1
  have e : exec D.N D.K (lutC last) w = exec D.N D.K (.rep 173 (jBody last)) w1 := rfl
  have w1v : ∀ k : Fin 200, (k.val < 80 ∨ k.val = 160 ∨ k.val = 161 ∨ 174 ≤ k.val) → w1 k = w k :=
    fun k hk => by
      rw [hw1, Function.update_of_ne (by intro e; subst e; simp at hk),
        Function.update_of_ne (by intro e; subst e; simp at hk),
        Function.update_of_ne (by intro e; subst e; simp at hk),
        Function.update_of_ne (by intro e; subst e; simp at hk)]
  have h173 : (w1 173).length = 2 ^ 22 := by rw [hw1, Function.update_self, hlc.ec.ck.tw,
    List.length_replicate]
  let Pinv : ℕ → St → Prop := fun i w' =>
    LIn D rd x T w' ∧ w' 140 = toBits 22 i ∧
      (∃ as, w' 162 = as.flatten ∧ RepM D as (fun a c => ∑ j ∈ Finset.range i,
        smulPK (setting D) (cf j) (bitRounds P hd x j 22).1 a c)) ∧
      (∃ cs, w' 163 = cs.flatten ∧ RepV D cs (fun c => ∑ j ∈ Finset.range i,
        smulCT (setting D) (cf j) (bitRounds P hd x j 22).2 c)) ∧
      ∀ r : Fin 200, (r.val < 80 ∨ 176 ≤ r.val) → w' r = w r
  have hP := exec_rep_inv (N := D.N) (K := D.K) 173 (jBody last)
    (fun hm => by have := List.all_eq_true.mp (wr_jBody_173 last) 173 hm; simp at this) Pinv w1
    ⟨hin.of_agree fun k hk => w1v k (by omega),
      by rw [hw1]; simp [hlc.ec.ck.tb, toBits22_zero],
      ⟨_, by rw [hw1]; simp [hlc.ec.ck.mat, flatten_replicate_replicate], repM_zero.congr fun a c => by
        simp⟩,
      ⟨_, by rw [hw1]; simp [hlc.ec.r6, flatten_replicate_replicate], repV_zero.congr fun c => by
        simp⟩,
      fun r hr => w1v r (by omega)⟩
    (fun i hi w' hw' _ => by
      rw [h173] at hi
      obtain ⟨li, j140, ⟨as, a162, ra⟩, ⟨cs, a163, rc⟩, fr⟩ := hw'
      have li' : LIn D rd x T (Function.update w' 173 (w' 173).tail) := li.of_agree fun k hk => by
        rw [Function.update_of_ne (by intro e; subst e; simp at hk)]
      obtain ⟨l2, b140, ⟨as', b162, rb⟩, ⟨cs', b163, rcb⟩, fr2⟩ := exec_jBody last hok hcoef hi li'
        (by rw [Function.update_of_ne (by decide), j140])
        ⟨as, by rw [Function.update_of_ne (by decide), a162], ra⟩
        ⟨cs, by rw [Function.update_of_ne (by decide), a163], rc⟩
      refine ⟨l2, b140, ⟨as', b162, rb.congr fun a c => by rw [Finset.sum_range_succ]⟩,
        ⟨cs', b163, rcb.congr fun c => by rw [Finset.sum_range_succ]⟩, fun r hr => ?_⟩
      rw [fr2 r hr, Function.update_of_ne (by intro e; subst e; simp at hr), fr r hr])
  rw [h173] at hP
  obtain ⟨l, -, hA, hC, fr⟩ := hP
  rw [e]
  exact ⟨l, hA, hC, fr⟩

end AdvancedEncryption.ExpLUT.Prog
