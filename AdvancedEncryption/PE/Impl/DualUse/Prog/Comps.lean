import PE.Impl.DualUse.Prog.Chal5
import PE.Impl.DualUse.Prog.KeyP
import PE.Impl.DualUse.ReductionOracle

/-!
# The reductions' components at the handlers' width

The handlers take components `XProg (R + 2)` with `R = 254` (`XProg 256`, as the key component
`keyP`). The public-key and challenge components of `PE.Impl.DualUse.Prog.{Pub3, Chal3, Pub5,
Chal5}` (`XProg 82`) are lifted (`liftP`), with their laws in the form of `Comps.law_pub` and
`Comps.law_chal` for the packed challenger `spPack` (`law_pub3L`, `law_pubIL`, `law_pub5L`,
`law_chal3L`, `law_chal5L`; the challenge of the ideal side is `chalIL`), their time bounds and
their output length bounds `io2 L 0 0` (`CompBoundsP`). The simulation-data components stay
`XProg 82`, framed by `keyP`: `sdSpec3`, `sdSpecI`, `sdSpec5` (`SdSpec`).
-/

namespace AdvancedEncryption.DualUse.Prog

open SigabaNeo SigabaNeo.Encode SigabaNeo.Tape SigabaNeo.Tape.XProg
open AdvancedEncryption.PE AdvancedEncryption.PE.DateWindow

theorem eighty_le : (80 : ℕ) ≤ 254 := by norm_num

/-- Lift an `XProg 82` component to the handlers' width `XProg 256`. -/
abbrev lift256 (p : XProg 82) : XProg 256 := liftP eighty_le p

theorem law_lift256 {p : XProg 82} {a b w : List Bool}
    (hp : p.law (ioS (R := 80) a b []) = PMF.pure (ioS (R := 80) w [] [])) :
    (lift256 p).law (io2 (R := 254) a b []) = PMF.pure (io2 (R := 254) w [] []) :=
  law_liftP_pure _ hp

theorem time_lift256 (p : XProg 82) (a b : ℕ) :
    timeBoundT (lift256 p) (io2 (R := 254) a b 0) = timeBoundT p (io2 (R := 80) a b 0) :=
  timeBoundT_liftP _ p a b

theorem len_lift256 {p : XProg 82} {a b L : ℕ} (hp : lenBoundT p (io2 (R := 80) a b 0) ≤ io2 L 0 0) :
    lenBoundT (lift256 p) (io2 (R := 254) a b 0) ≤ io2 L 0 0 :=
  lenBoundT_liftP_le _ p hp

variable {N K k : ℕ} (hk : 2 ^ K < 2 ^ k) (c : Conf N K k)

/-! ### Hybrid 3 -/

/-- **The public-key component of hybrid 3** at the handlers' width. -/
def pub3L : XProg 256 := lift256 (pub3P hk c)
/-- **The challenge component of hybrid 3** at the handlers' width. -/
def chal3L : XProg 256 := lift256 (chal3P hk c)

theorem wf_pub3L : (pub3L hk c).WF := wf_pub3P hk c
theorem wf_chal3L : (chal3L hk c).WF := wf_chal3P hk c

theorem law_pub3L [NeZero c.d] (hN : 0 < N) (hK : 0 < K) (st : dateUniverse.Attr → PMF (Inst3T N K k × Sec3 hk c))
    (p : Inst3T N K k × Sec3 hk c) :
    (pub3L hk c).law (io2 (R := 254) (((inst3Enc (N := N) (K := K) (k := k)).prod (sec3Enc hk c)).enc p) [] []) =
      PMF.pure (io2 (R := 254) ((spPack st (view3 hk c) (sd3 hk c)).pub p) [] []) :=
  law_lift256 (law_pub3P hk c hN hK p.1 p.2)

theorem law_chal3L [NeZero c.d] (hN : 0 < N) (hK : 1 ≤ K) (st : dateUniverse.Attr → PMF (Inst3T N K k × Sec3 hk c))
    (p : Inst3T N K k × Sec3 hk c) (μ : Bool) :
    (chal3L hk c).law (io2 (R := 254) (((inst3Enc (N := N) (K := K) (k := k)).prod (sec3Enc hk c)).enc p)
      (encMsg μ) []) =
      ((spPack st (view3 hk c) (sd3 hk c)).chal p μ).map fun ct => io2 (R := 254) ct [] [] := by
  refine (law_lift256 (law_chal3P hk c hN hK p.1 p.2 μ)).trans ?_
  simp [spPack]

theorem time_pub3L (a b : ℕ) :
    timeBoundT (pub3L hk c) (io2 (R := 254) a b 0) ≤
      timepub3 hk c (max a b + sizepub3 hk c) + timeFin (max a b + sizepub3 hk c) := by
  rw [pub3L, time_lift256]; exact time_pub3P hk c a b

theorem len_pub3L (a b : ℕ) :
    lenBoundT (pub3L hk c) (io2 (R := 254) a b 0) ≤ io2 (R := 254) (max a b + sizepub3 hk c) 0 0 :=
  len_lift256 (len_pub3P hk c a b)

theorem time_chal3L (a b : ℕ) :
    timeBoundT (chal3L hk c) (io2 (R := 254) a b 0) ≤
      timeChal3 hk c (max a b + sizeChal3 hk c) + timeFin (max a b + sizeChal3 hk c) := by
  rw [chal3L, time_lift256]; exact time_chal3P hk c a b

theorem len_chal3L (a b : ℕ) :
    lenBoundT (chal3L hk c) (io2 (R := 254) a b 0) ≤ io2 (R := 254) (max a b + sizeChal3 hk c) 0 0 :=
  len_lift256 (len_chal3P hk c a b)

/-- **The simulation-data component of hybrid 3** for `keyP`. -/
theorem sdSpec3 (hN : 0 < N) (hK : 0 < K) :
    SdSpec hk c (sd3P hk c) (((inst3Enc (N := N) (K := K) (k := k)).prod (sec3Enc hk c)).enc)
      (fun p => sd3 hk c p.1 p.2) (fun _ => True) :=
  ⟨wf_sd3P hk c, fun p _ => law_sd3P hk c hN hK p.1 p.2⟩

/-! ### The ideal side -/

/-- **The public-key component of the ideal side** at the handlers' width. -/
def pubIL : XProg 256 := lift256 (pubIP hk c)

theorem wf_pubIL : (pubIL hk c).WF := wf_pubIP hk c

theorem law_pubIL [NeZero c.d] (hN : 0 < N) (hK : 0 < K) (st : dateUniverse.Attr → PMF (Inst3T N K k × SecI hk c))
    (p : Inst3T N K k × SecI hk c) :
    (pubIL hk c).law (io2 (R := 254) (((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc p) [] []) =
      PMF.pure (io2 (R := 254) ((spPack st (viewI hk c) (sdI hk c)).pub p) [] []) :=
  law_lift256 (law_pubIP hk c hN hK p.1 p.2)

theorem time_pubIL (a b : ℕ) :
    timeBoundT (pubIL hk c) (io2 (R := 254) a b 0) ≤
      timepub3 hk c (max a b + sizepub3 hk c) + timeFin (max a b + sizepub3 hk c) := by
  rw [pubIL, time_lift256]; exact time_pubIP hk c a b

theorem len_pubIL (a b : ℕ) :
    lenBoundT (pubIL hk c) (io2 (R := 254) a b 0) ≤ io2 (R := 254) (max a b + sizepub3 hk c) 0 0 :=
  len_lift256 (len_pubIP hk c a b)

/-- **The simulation-data component of the ideal side** for `keyP`. -/
theorem sdSpecI (hN : 0 < N) (hK : 0 < K) :
    SdSpec hk c (sdIP hk c) (((inst3Enc (N := N) (K := K) (k := k)).prod (secIEnc hk c)).enc)
      (fun p => sdI hk c p.1 p.2) (fun _ => True) :=
  ⟨wf_sdIP hk c, fun p _ => law_sdIP hk c hN hK p.1 p.2⟩

/-! ### Hybrid 5 -/

/-- **The public-key component of hybrid 5** at the handlers' width. -/
def pub5L : XProg 256 := lift256 (pub5P hk c)
/-- **The challenge component of hybrid 5** at the handlers' width. -/
def chal5L : XProg 256 := lift256 (chal5P hk c)

theorem wf_pub5L : (pub5L hk c).WF := wf_pub5P hk c
theorem wf_chal5L : (chal5L hk c).WF := wf_chal5P hk c

theorem law_pub5L [NeZero c.d] (hN : 0 < N) (hK : 0 < K)
    (st : dateUniverse.Attr → PMF ((Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) × Sec5 hk c))
    (p : (Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) × Sec5 hk c) :
    (pub5L hk c).law (io2 (R := 254)
      (((inst5Enc (N := N) (K := K) (k := k) c.d).prod (sec5Enc hk c)).enc p) [] []) =
      PMF.pure (io2 (R := 254) ((spPack st (view5 hk c) (sd5 hk c)).pub p) [] []) :=
  law_lift256 (law_pub5P hk c hN hK p.1 p.2)

theorem law_chal5L [NeZero c.d] (hN : 0 < N) (hK : 1 ≤ K)
    (st : dateUniverse.Attr → PMF ((Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) × Sec5 hk c))
    (p : (Pub (Fin c.d) (Rg N K) k × Pub (Fin c.d) (Rg N K) k) × Sec5 hk c) (μ : Bool) :
    (chal5L hk c).law (io2 (R := 254)
      (((inst5Enc (N := N) (K := K) (k := k) c.d).prod (sec5Enc hk c)).enc p) (encMsg μ) []) =
      ((spPack st (view5 hk c) (sd5 hk c)).chal p μ).map fun ct => io2 (R := 254) ct [] [] := by
  refine (law_lift256 (law_chal5P hk c hN hK p.1 p.2 μ)).trans ?_
  simp [spPack]

theorem time_pub5L (a b : ℕ) :
    timeBoundT (pub5L hk c) (io2 (R := 254) a b 0) ≤
      timepub5 hk c (max a b + sizepub5 hk c) + timeFin (max a b + sizepub5 hk c) := by
  rw [pub5L, time_lift256]; exact time_pub5P hk c a b

theorem len_pub5L (a b : ℕ) :
    lenBoundT (pub5L hk c) (io2 (R := 254) a b 0) ≤ io2 (R := 254) (max a b + sizepub5 hk c) 0 0 :=
  len_lift256 (len_pub5P hk c a b)

theorem time_chal5L (a b : ℕ) :
    timeBoundT (chal5L hk c) (io2 (R := 254) a b 0) ≤
      timeChal5 hk c (max a b + sizeChal5 hk c) + timeFin (max a b + sizeChal5 hk c) := by
  rw [chal5L, time_lift256]; exact time_chal5P hk c a b

theorem len_chal5L (a b : ℕ) :
    lenBoundT (chal5L hk c) (io2 (R := 254) a b 0) ≤ io2 (R := 254) (max a b + sizeChal5 hk c) 0 0 :=
  len_lift256 (len_chal5P hk c a b)

/-- **The simulation-data component of hybrid 5** for `keyP`. -/
theorem sdSpec5 (hN : 0 < N) (hK : 0 < K) :
    SdSpec hk c (sd5P hk c) (((inst5Enc (N := N) (K := K) (k := k) c.d).prod (sec5Enc hk c)).enc)
      (fun p => sd5 hk c p.1 p.2) (fun _ => True) :=
  ⟨wf_sd5P hk c, fun p _ => law_sd5P hk c hN hK p.1 p.2⟩

end AdvancedEncryption.DualUse.Prog
