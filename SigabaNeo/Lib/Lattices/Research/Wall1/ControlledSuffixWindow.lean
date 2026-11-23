import SigabaNeo.Lib.Lattices.Research.Wall1.ControlledSuffixFamily

/-! Transport of the full marked window past any succession of designated horizontal freezes. -/

noncomputable section
namespace SigabaNeo.Wall1.ControlledPlane

open Submodule WithLp Real TerminalProjection TerminalProjection.Restart506
open TerminalProjection.ChainState
open scoped RealInnerProductSpace

/-- An isometric realization of the appended lattice and its signed tie-breaking axes. -/
structure WindowRealization {n d : ℕ} (s : ChainState n (CoordSpace d)) (c : Column)
    (t : ChainState (n+1) (CoordSpace (d+1))) where
  e : WindowSpace (CoordSpace d) ≃ₗᵢ[ℝ] CoordSpace (d+1)
  lattice : (s.append c).M.map (e.toLinearEquiv.toLinearMap.restrictScalars ℤ) = t.M
  axis (i : Fin (n+1)) : e (s.frame.append.axis i) = t.frame.axis i

def incomingRealization {n d : ℕ} (s : ChainState n (CoordSpace d)) (c : Column) :
    WindowRealization s c (incoming s c) where
  e := windowCoord d
  lattice := (transport_eq ..).symm
  axis _ := rfl

variable {n d : ℕ} {c : Column}

theorem WindowRealization.winner {s : ChainState n (CoordSpace d)}
    {t : ChainState (n+1) (CoordSpace (d+1))} (W : WindowRealization s c t) :
    t.winner = W.e (s.append c).winner := by
  rw [← reframe_winner]
  apply winner_eq
  · funext v i
    change ⟪t.frame.axis i,v⟫ = ⟪W.e (s.frame.append.axis i),v⟫
    rw [W.axis]
  · exact W.lattice.symm.trans (transport_eq ..).symm

private def freezeCoord (s : ChainState n (CoordSpace (d+1))) :
    (ℝ ∙ s.winner)ᗮ ≃ₗᵢ[ℝ] CoordSpace d :=
  coord (by
    have h := (ℝ ∙ s.winner).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton s.shortest.2.1,finrank_euclideanSpace_fin] at h
    omega)

private def collapse (s : ChainState n (CoordSpace (d+1))) : CoordSpace (d+1) →ₗ[ℝ] CoordSpace d :=
  (freezeCoord s).toLinearEquiv.toLinearMap.comp
    (ℝ ∙ s.winner)ᗮ.orthogonalProjectionOnto.toLinearMap

private theorem collapse_surjective (s : ChainState n (CoordSpace (d+1))) :
    Function.Surjective (collapse s) := by
  intro x
  let e := freezeCoord s
  refine ⟨(e.symm x).val,?_⟩
  change e ((ℝ ∙ s.winner)ᗮ.orthogonalProjectionOnto (e.symm x).val) = x
  rw [orthogonalProjectionOnto_mem_subspace_eq_self,e.apply_symm_apply]

private theorem collapse_M (s : ChainState n (CoordSpace (d+1))) :
    s.M.map ((collapse s).restrictScalars ℤ) = s.freeze.M := by
  dsimp only [freeze,reframe,project]
  rw [transport_eq,projectedModule,← Submodule.map_comp]
  rfl

private theorem collapse_norm (s : ChainState n (CoordSpace (d+1))) (x : CoordSpace (d+1)) :
    ‖collapse s x‖ = ‖(ℝ ∙ s.winner)ᗮ.starProjection x‖ :=
  (freezeCoord s).norm_map _

private def collapseHorizontal (s : ChainState n (CoordSpace (d+1))) :
    WindowSpace (CoordSpace (d+1)) →ₗ[ℝ] WindowSpace (CoordSpace d) :=
  ((collapse s).prodMap (LinearMap.id (R := ℝ) (M := ℝ))).withLpMap 2

private theorem collapse_append (s : ChainState n (CoordSpace (d+1))) (c : Column) :
    (s.append c).M.map ((collapseHorizontal s).restrictScalars ℤ) = (s.freeze.append c).M := by
  have hh : ((collapseHorizontal s).restrictScalars ℤ).comp (horizontalInclusion.restrictScalars ℤ)
      = (horizontalInclusion.restrictScalars ℤ).comp ((collapse s).restrictScalars ℤ) := rfl
  have hc : collapse s (columnLift s.g c) = columnLift s.freeze.g c := by
    unfold columnLift
    rw [map_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ map_nsmul ..
  change (appendWindow s.M _).map _ = appendWindow s.freeze.M _
  rw [appendWindow,appendWindow,Submodule.map_sup,← Submodule.map_comp,hh,Submodule.map_comp,
    collapse_M,map_span,Set.image_singleton]
  have hg : (collapseHorizontal s) (toLp 2 (columnLift s.g c,(1:ℝ))) =
      toLp 2 (columnLift s.freeze.g c,(1:ℝ)) := congrArg (fun x ↦ toLp 2 (x,(1:ℝ))) hc
  simp only [LinearMap.restrictScalars_apply,hg]

private theorem collapse_axis (s : ChainState n (CoordSpace (d+1))) (i : Fin (n+1)) :
    collapseHorizontal s (s.frame.append.axis i) = s.freeze.frame.append.axis i := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [AxisFrame.append,Fin.snoc_last]
    change toLp 2 (collapse s 0,(1:ℝ)) = _
    rw [map_zero]
  · simp only [AxisFrame.append,Fin.snoc_castSucc]
    rfl

private theorem horizontal_projection (v : CoordSpace (d+1)) (w : WindowSpace (CoordSpace (d+1))) :
    (ℝ ∙ horizontalInclusion v)ᗮ.starProjection w =
      toLp 2 ((ℝ ∙ v)ᗮ.starProjection w.fst, w.snd) := by
  rw [starProjection_orthogonal_val,starProjection_singleton,starProjection_orthogonal_val,
    starProjection_singleton]
  have h : ⟪horizontalInclusion v,w⟫ = ⟪v,w.fst⟫ := by
    change ⟪v,w.fst⟫ + w.snd * 0 = _
    ring
  rw [h,show ‖horizontalInclusion v‖ = ‖v‖ from WithLp.norm_toLp_fst 2 _ _ _]
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext rfl (by change w.snd - _ • (0:ℝ) = w.snd; simp)

private theorem horizontal_line (s : ChainState n (CoordSpace (d+1))) (c : Column)
    (ho : (s.append c).winner.snd = 0) :
    ℝ ∙ (s.append c).winner = ℝ ∙ horizontalInclusion s.winner :=
  agreement_of_order (s.append c).key (s.append c).key_injective s.shortest (s.append c).shortest
    (fun a ha ↦ s.key_horizontal_le c ((chosen_spec s.key s.M s.nonbot).2 a ha))
    (chosen_spec (s.append c).key (s.append c).M (s.append c).nonbot).2 ho

/-- Freezing a horizontal winner commutes, including the complete ordered frame, with
appending the same column after freezing the designated old winner. -/
theorem WindowRealization.freeze_horizontal {s : ChainState n (CoordSpace (d+1))}
    {t : ChainState (n+1) (CoordSpace ((d+1)+1))} (W : WindowRealization s c t)
    (ho : (s.append c).winner.snd = 0) : Nonempty (WindowRealization s.freeze c t.freeze) := by
  let A := (collapse t).comp W.e.toLinearEquiv.toLinearMap
  let B := collapseHorizontal s
  have hB : Function.Surjective B := by
    intro z
    obtain ⟨x,hx⟩ := collapse_surjective s z.fst
    exact ⟨toLp 2 (x,z.snd),(WithLp.equiv 2 _).injective (Prod.ext hx rfl)⟩
  have hn (y) : ‖A y‖ = ‖B y‖ := by
    change ‖collapse t (W.e y)‖ = ‖B y‖
    rw [collapse_norm,W.winner]
    have he : (ℝ ∙ (s.append c).winner)ᗮ.map W.e.toLinearEquiv.toLinearMap =
        (ℝ ∙ W.e (s.append c).winner)ᗮ := by
      rw [map_orthogonal_equiv,map_span,Set.image_singleton]; rfl
    have hp := starProjection_map_apply W.e (ℝ ∙ (s.append c).winner)ᗮ (W.e y)
    simp only [he,W.e.symm_apply_apply] at hp
    simp only [horizontal_line s c ho,horizontal_projection] at hp
    rw [hp,W.e.norm_map]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
    change _ = ‖collapse s y.fst‖^2 + ‖y.snd‖^2
    rw [collapse_norm]
    rfl
  have hk : LinearMap.ker B ≤ LinearMap.ker A := fun y hy ↦
    norm_eq_zero.mp ((hn y).trans ((LinearMap.mem_ker.mp hy) ▸ norm_zero))
  let F := B.liftOfSurjective hB ⟨A,hk⟩
  have hF (y) : F (B y) = A y := LinearMap.equivOfSurjective_apply hB hk
  let I : WindowSpace (CoordSpace d) →ₗᵢ[ℝ] CoordSpace (d+1) :=
    { F with norm_map' := fun z ↦ by obtain ⟨y,rfl⟩ := hB z; rw [hF,hn] }
  let E := LinearIsometryEquiv.ofSurjective I (by
    intro z
    obtain ⟨y,hy⟩ := collapse_surjective t z
    obtain ⟨w,rfl⟩ := W.e.surjective y
    exact ⟨B w,(hF w).trans hy⟩)
  have factor (y) : E (B y) = A y := hF y
  refine ⟨⟨E,?_,?_⟩⟩
  · rw [← collapse_append s c,← Submodule.map_comp,← collapse_M t,← W.lattice,← Submodule.map_comp]
    exact congrArg (fun f ↦ (s.append c).M.map f) (LinearMap.ext factor)
  · intro i
    rw [← collapse_axis s i,factor]
    change collapse t (W.e (s.frame.append.axis i)) = _
    rw [W.axis]
    rfl

theorem WindowRealization.horizontal_norm {s : ChainState n (CoordSpace (d+1))}
    {t : ChainState (n+1) (CoordSpace (d+1+1))} (W : WindowRealization s c t)
    (ho : (s.append c).winner.snd = 0) : ‖t.winner‖ = ‖s.winner‖ := by
  rw [W.winner,W.e.norm_map]
  let w := (s.append c).winner
  have he : horizontalInclusion w.fst = w := (WithLp.equiv 2 _).injective (Prod.ext rfl ho.symm)
  have hm := (mem_append_at_height _ _ w 0 (by simpa using ho)).mp (s.append c).shortest.1
  have old := s.shortest.2.2 w.fst ((Submodule.Quotient.mk_eq_zero _).mp (by simpa using hm))
    (fun h ↦ (s.append c).shortest.2.1 (he.symm.trans ((congrArg _ h).trans (map_zero _))))
  have hmem : horizontalInclusion s.winner ∈ (s.append c).M :=
    (le_sup_left : s.M.map _ ≤ appendWindow s.M (columnLift s.g c)) ⟨_,s.shortest.1,rfl⟩
  have hnew := (s.append c).shortest.2.2 _ hmem (fun h ↦ s.shortest.2.1 (congrArg WithLp.fst h))
  exact le_antisymm (hnew.trans_eq (WithLp.norm_toLp_fst 2 _ _ _))
    (old.trans_eq ((WithLp.norm_toLp_fst 2 _ _ _).symm.trans (congrArg norm he)))

end SigabaNeo.Wall1.ControlledPlane

#print axioms SigabaNeo.Wall1.ControlledPlane.WindowRealization.winner
#print axioms SigabaNeo.Wall1.ControlledPlane.WindowRealization.freeze_horizontal
#print axioms SigabaNeo.Wall1.ControlledPlane.WindowRealization.horizontal_norm
