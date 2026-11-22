import PE.Impl.DualUse.Prog.Core

/-!
# The fields of the packed inputs of the components

The secret words of the three reductions are nested products (`FixedEnc.prod`) of the instance's
and the secret's fields. A field is read by `getB o L` with `o` the sum of the lengths
(`fencLen`) of the fields before it, written `f₁ + (f₂ + (… + 0))`, and `L` its length: after
flattening the products (`FixedEnc.prod_enc`), `drop_enc` skips one field at a time
(`f3_*`, `f5_*`, `fI_*`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Lattices SigabaNeo.Lattices.Algo SigabaNeo.Tape Matrix
  AdvancedEncryption.RingBTVW
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow AdvancedEncryption.PE.Gates
open AdvancedEncryption.PE.Gates.DateWindow

/-! ### Skipping fields -/

theorem drop_enc {β : Type} {n : ℕ} (e : FixedEnc β n) (b : β) (W : List Bool) (o : ℕ) :
    (e.enc b ++ W).drop (fencLen e + o) = W.drop o := by
  have h : (e.enc b).length = fencLen e := e.length b
  rw [← List.drop_drop, List.drop_left' h]

theorem takeD_enc_app {β : Type} {n : ℕ} (e : FixedEnc β n) (b : β) (W : List Bool) :
    takeD (fencLen e) ((e.enc b ++ W).drop 0) = e.enc b := by
  have h : (e.enc b).length = fencLen e := e.length b
  rw [List.drop_zero, takeD_eq_take (by simp [h]), List.take_left' h]

theorem takeD_enc {β : Type} {n : ℕ} (e : FixedEnc β n) (b : β) :
    takeD (fencLen e) ((e.enc b).drop 0) = e.enc b := by
  rw [List.drop_zero]; exact takeD_of_length' (e.length b : (e.enc b).length = fencLen e)

theorem comap_enc' {α β : Type} {n : ℕ} (e : FixedEnc β n) (f : α → β) (hf : Function.Injective f)
    (a : α) : (e.comap f hf).enc a = e.enc (f a) := rfl

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-! ### The encodings as concatenations -/

theorem pair_enc {β γ : Type} {n m : ℕ} (e : FixedEnc β n) (f : FixedEnc γ m) (a : β) (b : γ) :
    (e.prod f).enc (a, b) = e.enc a ++ f.enc b := rfl

theorem inst3Enc_enc (ab : Inst3T N K k) : (inst3Enc (N := N) (K := K) (k := k)).enc ab =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.1 ++
      (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.2 := rfl

theorem sec3Enc_enc (σ : Sec3 hk c) : (sec3Enc hk c).enc σ =
    dateEnc.enc σ.1 ++ ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 ++
      ((wEnc hk c).enc σ.2.2.1 ++ ((ringEnc N K).enc σ.2.2.2.1 ++
        ((restEnc c).enc σ.2.2.2.2.1 ++ (eEnc (N := N) hk).enc σ.2.2.2.2.2)))) := rfl

theorem restEnc_enc (r : Rest (Sdw (N := N) hk) (Fin c.d) (TrapCol k)) : (restEnc c).enc r =
    (ringEnc N K).enc r.1 ++ ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc r.2.1 ++
      ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc r.2.2.1 ++
        ((rmTEnc c).enc r.2.2.2.1 ++ (ringEnc N K).enc r.2.2.2.2))) := rfl

/-! ### Hybrid 3: `(a, b)`, then `x, B₀, w, p, (s, e₀, e₁, R, e'), e` -/

/-- The length of a row on the gadget columns. -/
abbrev fC (N K k : ℕ) : ℕ := fencLen (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k))
/-- The length of a row `1 × d`. -/
abbrev fD (N K : ℕ) (d : ℕ) : ℕ := fencLen (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin d))
/-- The length of a ring element. -/
abbrev fR (N K : ℕ) : ℕ := fencLen (ringEnc N K)

def o3x : ℕ := fC N K k + (fC N K k + 0)
def o3B : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + 0))
def o3w : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + (fD N K c.d + 0)))
def o3p : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + (fD N K c.d + (fencLen (wEnc hk c) + 0))))
def o3s : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + (fD N K c.d + (fencLen (wEnc hk c) +
  (fR N K + 0)))))
def o3e0 : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + (fD N K c.d + (fencLen (wEnc hk c) +
  (fR N K + (fR N K + 0))))))
def o3R : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + (fD N K c.d + (fencLen (wEnc hk c) +
  (fR N K + (fR N K + (fD N K c.d + (fencLen (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)) +
    0))))))))

def o3e1 : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + (fD N K c.d + (fencLen (wEnc hk c) +
  (fR N K + (fR N K + (fD N K c.d + 0)))))))
def o3e' : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + (fD N K c.d + (fencLen (wEnc hk c) +
  (fR N K + (fR N K + (fD N K c.d + (fencLen (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)) +
    (fencLen (rmTEnc c) + 0)))))))))
def o3e : ℕ := fC N K k + (fC N K k + (fencLen dateEnc + (fD N K c.d + (fencLen (wEnc hk c) +
  (fR N K + (fR N K + (fD N K c.d + (fencLen (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)) +
    (fencLen (rmTEnc c) + (fR N K + 0))))))))))

/-- The packed secret of hybrid 3. -/
abbrev W3 (ab : Inst3T N K k) (σ : Sec3 hk c) : List Bool :=
  ((inst3Enc (N := N) (K := K) (k := k)).prod (sec3Enc hk c)).enc (ab, σ)

section F3
variable (ab : Inst3T N K k) (σ : Sec3 hk c)

/-- **The packed secret of hybrid 3, flat.** -/
theorem W3_eq : W3 hk c ab σ =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.1 ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.2 ++
    (dateEnc.enc σ.1 ++ ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 ++
    ((wEnc hk c).enc σ.2.2.1 ++ ((ringEnc N K).enc σ.2.2.2.1 ++
    ((ringEnc N K).enc σ.2.2.2.2.1.1 ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.2.2.2.1.2.1 ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc σ.2.2.2.2.1.2.2.1 ++
    ((rmTEnc c).enc σ.2.2.2.2.1.2.2.2.1 ++ ((ringEnc N K).enc σ.2.2.2.2.1.2.2.2.2 ++
    (eEnc (N := N) hk).enc σ.2.2.2.2.2)))))))))) := by
  rw [show W3 hk c ab σ = ((DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.1 ++
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.2) ++
    (dateEnc.enc σ.1 ++ ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 ++
    ((wEnc hk c).enc σ.2.2.1 ++ ((ringEnc N K).enc σ.2.2.2.1 ++
    (((ringEnc N K).enc σ.2.2.2.2.1.1 ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.2.2.2.1.2.1 ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc σ.2.2.2.2.1.2.2.1 ++
    ((rmTEnc c).enc σ.2.2.2.2.1.2.2.2.1 ++ (ringEnc N K).enc σ.2.2.2.2.1.2.2.2.2)))) ++
    (eEnc (N := N) hk).enc σ.2.2.2.2.2))))) from rfl]
  simp only [List.append_assoc]

theorem f3_a : takeD (fC N K k) ((W3 hk c ab σ).drop 0) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.1 := by
  rw [W3_eq]; exact takeD_enc_app _ _ _
theorem f3_b : takeD (fC N K k) ((W3 hk c ab σ).drop (fC N K k + 0)) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.2 := by
  rw [W3_eq]; simp only [drop_enc, takeD_enc_app]
theorem f3_x : takeD (fencLen dateEnc) ((W3 hk c ab σ).drop (o3x (N := N) (K := K) (k := k))) =
    encDate σ.1 := by
  rw [W3_eq, o3x]; simp only [drop_enc, takeD_enc_app]; rfl
theorem f3_B : takeD (fD N K c.d) ((W3 hk c ab σ).drop (o3B (N := N) (K := K) (k := k))) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 := by
  rw [W3_eq, o3B]; simp only [drop_enc, takeD_enc_app]
theorem f3_w : takeD (fencLen (wEnc hk c)) ((W3 hk c ab σ).drop (o3w c)) = (wEnc hk c).enc σ.2.2.1 := by
  rw [W3_eq, o3w]; simp only [drop_enc, takeD_enc_app]
theorem f3_p : takeD (fR N K) ((W3 hk c ab σ).drop (o3p hk c)) = (ringEnc N K).enc σ.2.2.2.1 := by
  rw [W3_eq, o3p]; simp only [drop_enc, takeD_enc_app]
theorem f3_s : takeD (fR N K) ((W3 hk c ab σ).drop (o3s hk c)) = (ringEnc N K).enc σ.2.2.2.2.1.1 := by
  rw [W3_eq, o3s]; simp only [drop_enc, takeD_enc_app]
theorem f3_e0 : takeD (fD N K c.d) ((W3 hk c ab σ).drop (o3e0 hk c)) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.2.2.2.1.2.1 := by
  rw [W3_eq, o3e0]; simp only [drop_enc, takeD_enc_app]
theorem f3_R : takeD (fencLen (rmTEnc c)) ((W3 hk c ab σ).drop (o3R hk c)) =
    (rmTEnc c).enc σ.2.2.2.2.1.2.2.2.1 := by
  rw [W3_eq, o3R]; simp only [drop_enc]; exact takeD_enc_app _ _ _

theorem f3_e1 : takeD (fencLen (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)))
    ((W3 hk c ab σ).drop (o3e1 hk c)) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc σ.2.2.2.2.1.2.2.1 := by
  rw [W3_eq, o3e1]; simp only [drop_enc]; exact takeD_enc_app _ _ _
theorem f3_e' : takeD (fR N K) ((W3 hk c ab σ).drop (o3e' hk c)) =
    (ringEnc N K).enc σ.2.2.2.2.1.2.2.2.2 := by
  rw [W3_eq, o3e']; simp only [drop_enc]; erw [drop_enc]; exact takeD_enc_app _ _ _
theorem f3_e : takeD (fencLen (eEnc (N := N) hk)) ((W3 hk c ab σ).drop (o3e hk c)) =
    (eEnc (N := N) hk).enc σ.2.2.2.2.2 := by
  rw [W3_eq, o3e]; simp only [drop_enc]; erw [drop_enc]; simp only [drop_enc]; exact takeD_enc _ _

end F3

/-! ### The ideal side: `(a, b)`, then `x, B₀, w, p, (s, e₀, e₁, R, e_j, e'), ct` -/

/-- The packed secret of the ideal side. -/
abbrev WI (ab : Inst3T N K k) (σ : SecI hk c) : List Bool :=
  ((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc (ab, σ)

section FI
variable (ab : Inst3T N K k) (σ : SecI hk c)

/-- **The packed secret of the ideal side, flat.** -/
theorem WI_eq : WI hk c ab σ =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.1 ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.2 ++
    (dateEnc.enc σ.1 ++ ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 ++
    ((wEnc hk c).enc σ.2.2.1 ++ ((ringEnc N K).enc σ.2.2.2.1 ++
    ((ringEnc N K).enc σ.2.2.2.2.1.s ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.2.2.2.1.e₀ ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc σ.2.2.2.2.1.e₁ ++
    ((rmTEnc c).enc σ.2.2.2.2.1.Rm ++ ((eEnc (N := N) hk).enc σ.2.2.2.2.1.ej ++
    ((ringEnc N K).enc σ.2.2.2.2.1.e' ++ (ctEnc hk c).enc σ.2.2.2.2.2))))))))))) := by
  rw [show WI hk c ab σ = ((DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.1 ++
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.2) ++
    (dateEnc.enc σ.1 ++ ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 ++
    ((wEnc hk c).enc σ.2.2.1 ++ ((ringEnc N K).enc σ.2.2.2.1 ++
    (((ringEnc N K).enc σ.2.2.2.2.1.s ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.2.2.2.1.e₀ ++
    ((DualUse.matEnc (N := N) (K := K) (Fin 1) (TrapCol k)).enc σ.2.2.2.2.1.e₁ ++
    ((rmTEnc c).enc σ.2.2.2.2.1.Rm ++ ((eEnc (N := N) hk).enc σ.2.2.2.2.1.ej ++
      (ringEnc N K).enc σ.2.2.2.2.1.e'))))) ++
    (ctEnc hk c).enc σ.2.2.2.2.2))))) from rfl]
  simp only [List.append_assoc]

theorem fI_a : takeD (fC N K k) ((WI hk c ab σ).drop 0) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.1 := by
  rw [WI_eq]; exact takeD_enc_app _ _ _
theorem fI_b : takeD (fC N K k) ((WI hk c ab σ).drop (fC N K k + 0)) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (RingBTVW.Col k)).enc ab.2 := by
  rw [WI_eq]; simp only [drop_enc, takeD_enc_app]
theorem fI_x : takeD (fencLen dateEnc) ((WI hk c ab σ).drop (o3x (N := N) (K := K) (k := k))) =
    encDate σ.1 := by
  rw [WI_eq, o3x]; simp only [drop_enc, takeD_enc_app]; rfl
theorem fI_B : takeD (fD N K c.d) ((WI hk c ab σ).drop (o3B (N := N) (K := K) (k := k))) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.1 := by
  rw [WI_eq, o3B]; simp only [drop_enc, takeD_enc_app]
theorem fI_w : takeD (fencLen (wEnc hk c)) ((WI hk c ab σ).drop (o3w c)) = (wEnc hk c).enc σ.2.2.1 := by
  rw [WI_eq, o3w]; simp only [drop_enc, takeD_enc_app]
theorem fI_p : takeD (fR N K) ((WI hk c ab σ).drop (o3p hk c)) = (ringEnc N K).enc σ.2.2.2.1 := by
  rw [WI_eq, o3p]; simp only [drop_enc, takeD_enc_app]
theorem fI_s : takeD (fR N K) ((WI hk c ab σ).drop (o3s hk c)) = (ringEnc N K).enc σ.2.2.2.2.1.s := by
  rw [WI_eq, o3s]; simp only [drop_enc, takeD_enc_app]
theorem fI_e0 : takeD (fD N K c.d) ((WI hk c ab σ).drop (o3e0 hk c)) =
    (DualUse.matEnc (N := N) (K := K) (Fin 1) (Fin c.d)).enc σ.2.2.2.2.1.e₀ := by
  rw [WI_eq, o3e0]; simp only [drop_enc, takeD_enc_app]
theorem fI_R : takeD (fencLen (rmTEnc c)) ((WI hk c ab σ).drop (o3R hk c)) =
    (rmTEnc c).enc σ.2.2.2.2.1.Rm := by
  rw [WI_eq, o3R]; simp only [drop_enc]; exact takeD_enc_app _ _ _

end FI

end AdvancedEncryption.DualUse.Prog
