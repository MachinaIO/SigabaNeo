import SigabaNeo.Lib.Machines.Pack.TimeMain

/-!
# The packed machine with its explicit clock

**`run_packMachineT`**: for a well-formed framed program `p : XProg K` whose wide loops nest at most
`D` deep (`OkX w D 0 p`, e.g. from `XProg.loopDepth p ≤ D`), the machine `packMachineT p i₀ o n`
with `5 + w + D` tapes has the output law of `XProg.toMachineT p i₀ o n` on every input at most `n`
long:

  `(packMachineT p i₀ o n).run x = (p.law (inputStore i₀ x)).map (fun s => s o)`.

Its clock is `ZProg.totalTime n (topTime p i₀ o n) (lenBoundT p (inputBound i₀ n) o)`, where
`topTime` adds to `ptime` (the translated program, from the input bound) the setup (`K` empty frames,
the input written into its segment) and the final read of the output segment.
-/

namespace SigabaNeo.Tape.Pack

open Cslib Function

variable {K w D : ℕ}

/-- The time of the packed program `topZ`. -/
def topTime (w D : ℕ) (p : XProg K) (i₀ o : Fin K) (n : ℕ) : ℕ :=
  Prog.timeBoundT (Prog.snocN (packLayout w D).st false K)
      (fun y => if y = ioT w D then n else 0) +
    (putTime K n +
      (ptime w (Embedding.refl _) 0 p (Prog.inputBound i₀ n) 0 +
        (6 * Lam (Lafter (Embedding.refl _) p (Prog.inputBound i₀ n)) + 16)))

theorem io_ok : ioT w D ≠ (packLayout w D).st ∧ ioT w D ≠ flT w D ∧
    (packLayout w D).st ≠ flT w D := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have := congrArg Fin.val h <;>
    simp [ioT, flT, tp] at this

theorem io_put_ok : [(packLayout w D).st, ioT w D, flT w D, bufT w D].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true]
  refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩ <;>
    have := congrArg Fin.val h <;> simp [ioT, flT, bufT, tp] at this

/-- **The time of the packed program.** -/
theorem ht_topZ (hw : 3 ≤ w) (p : XProg K) (hp : OkX w D 0 p) (hwf : p.WF) (i₀ o : Fin K)
    (n : ℕ) (x : List Bool) (hx : x.length ≤ n) :
    (topZ (w := w) (D := D) p i₀ o).HT (fun s => s = inputStore (ioT w D) x)
      (topTime w D p i₀ o n) := by
  have hsi : (packLayout w D).st ≠ ioT w D := st_ne_io
  have hfi : flT w D ≠ ioT w D := fun h => by
    have := congrArg Fin.val h; simp [ioT, flT, tp] at this
  have hbi : bufT w D ≠ ioT w D := fun h => by
    have := congrArg Fin.val h; simp [ioT, bufT, tp] at this
  have hP0 : ∀ y, y ≠ ioT w D → inputStore (ioT w D) x y = [] := fun y hy => by
    simp [inputStore, update_of_ne hy]
  have hst0 : inputStore (ioT w D) x (packLayout w D).st = [] := hP0 _ hsi
  have hP1 : (XProg.prog (Prog.snocN (packLayout w D).st false K)).law
      (inputStore (ioT w D) x) =
      PMF.pure (update (inputStore (ioT w D) x) (packLayout w D).st (List.replicate K false)) := by
    rw [XProg.law_prog, Prog.law_eq_run_of_coinFree _ (Prog.coinFree_snocN _ _ _),
      Prog.run_snocN, hst0, List.nil_append]
  have hP1st : update (inputStore (ioT w D) x) (packLayout w D).st (List.replicate K false)
      (packLayout w D).st = pkW (fun _ : Fin K => ([] : List Bool)) := by
    rw [update_self, pkW_blank]
  have hput : (putPh i₀ (ioT w D) (packLayout w D).st (flT w D) (bufT w D)).f
      (update (inputStore (ioT w D) x) (packLayout w D).st (List.replicate K false)) =
      update (fun _ => ([] : List Bool)) (packLayout w D).st (pkW (inputStore i₀ x)) := by
    rw [putPh_f, putF_pkW i₀ _ _ _ _ hP1st, update_of_ne hsi.symm]
    have hS : update (fun _ : Fin K => ([] : List Bool)) i₀ (inputStore (ioT w D) x (ioT w D)) =
        inputStore i₀ x := by simp [inputStore]
    rw [hS]
    funext y
    by_cases hy : y = ioT w D
    · subst hy; rw [update_self, update_of_ne hsi.symm]
    · rw [update_of_ne hy]
      by_cases hys : y = (packLayout w D).st
      · subst hys; rw [update_self, update_self]
      · rw [update_of_ne hys, update_of_ne hys, update_of_ne hys, hP0 y hy]
  have hphys : Phys 0 0 (Prog.inputBound i₀ n)
      (update (fun _ => ([] : List Bool)) (packLayout w D).st (pkW (inputStore i₀ x))) := by
    refine ⟨fun y hy _ => by simp [update_of_ne hy], fun e => by
      simp [update_of_ne ((packLayout w D).hFst e)], _, update_self _ _ _,
      Prog.fits_inputStore i₀ hx⟩
  refine (ZProg.HT.seq'
    (Mid := fun s => s = update (inputStore (ioT w D) x) (packLayout w D).st
      (List.replicate K false))
    (ZProg.HT.xp' (ℓ := fun y => if y = ioT w D then n else 0)
      (p := XProg.prog (Prog.snocN (packLayout w D).st false K)) (Prog.wf_snocN _ _ _) ?_)
    ?_ (ZProg.HT.seq' (Mid := fun s => s =
        update (fun _ => ([] : List Bool)) (packLayout w D).st (pkW (inputStore i₀ x)))
      (ZProg.HT.ph' (t := putTime K n) ?_) ?_
      (ZProg.HT.seq' (Mid := Phys 0 0 (Lafter (Embedding.refl _) p (Prog.inputBound i₀ n)))
        ((ht_tr hw (Embedding.refl _) 0 p hp hwf (Prog.inputBound i₀ n) 0).mono
          (fun s hs => hs ▸ hphys) le_rfl)
        (fun P hP P' hP' => phys_post (sim_tr hw _ 0 p hp) (hP ▸ hphys) hP')
        (ZProg.HT.ph' ?_)))).mono (fun _ h => h) le_rfl
  · rintro s rfl y
    by_cases hy : y = ioT w D
    · subst hy; simp [inputStore, hx]
    · rw [hP0 y hy]; simp [hy]
  · rintro s rfl s' hs'
    rw [ZProg.law_xp, hP1, PMF.support_pure, Set.mem_singleton_iff] at hs'
    exact hs'
  · rintro s rfl
    refine ⟨putPh_pre io_put_ok _ ?_ ?_, ?_⟩
    · rw [update_of_ne fl_ne_st, hP0 _ hfi]
    · rw [update_of_ne buf_ne_st, hP0 _ hbi]
    · rw [putPh_time io_put_ok, hP1st, update_of_ne hsi.symm]
      simp only [inputStore, update_self]
      apply putTime_mono _ hx
      simp [pkW_blank]
  · rintro s rfl s' hs'
    rw [ZProg.law_ph, hput, PMF.support_pure, Set.mem_singleton_iff] at hs'
    exact hs'
  · rintro P ⟨hc, hF, S, hS, hL⟩
    refine ⟨getPh_pre io_ok _ ?_ (fl_clean hc), ?_⟩
    · exact hc _ hsi.symm (fun e _ h => by
        have := congrArg Fin.val h; simp [ioT, tp] at this; omega)
    · rw [getPh_time io_ok, hS]
      have := length_pkW_le hL
      omega

/-- **The packed machine with its clock**, `5 + w + D` tapes. -/
noncomputable def packMachineT (w D : ℕ) (p : XProg K) (i₀ o : Fin K) (n : ℕ) : Machine :=
  packMachine (w := w) (D := D) p i₀ o n (topTime w D p i₀ o n)
    (XProg.lenBoundT p (Prog.inputBound i₀ n) o)

/-- **The output law of the packed machine**: the same as `XProg.toMachineT p i₀ o n`
(`XProg.run_toMachineT`), on a machine with `5 + w + D` tapes. -/
theorem run_packMachineT (hw : 3 ≤ w) (p : XProg K) (hp : OkX w D 0 p) (hwf : p.WF)
    (i₀ o : Fin K) (n : ℕ) (x : List Bool) (hx : x.length ≤ n) :
    (packMachineT w D p i₀ o n).run x = (p.law (inputStore i₀ x)).map (fun s => s o) :=
  run_packMachine hw p hp i₀ o n _ _ x hx (ht_topZ hw p hp hwf i₀ o n x hx)
    (fun s hs => XProg.lenBoundT_spec p _ _ (Prog.fits_inputStore i₀ hx) s hs o)

theorem tapes_packMachineT (p : XProg K) (i₀ o : Fin K) (n : ℕ) :
    (packMachineT w D p i₀ o n).tapes = 5 + w + D := rfl

theorem time_packMachineT (p : XProg K) (i₀ o : Fin K) (n : ℕ) :
    (packMachineT w D p i₀ o n).time =
      (2 * n + 2) + topTime w D p i₀ o n + (2 * XProg.lenBoundT p (Prog.inputBound i₀ n) o + 2) :=
  rfl

theorem states_packMachineT (p : XProg K) (i₀ o : Fin K) (n : ℕ) :
    (packMachineT w D p i₀ o n).states =
      Fintype.card (topZ (w := w) (D := D) p i₀ o).State + 4 :=
  states_packMachine _ _ _ _ _ _

end SigabaNeo.Tape.Pack
