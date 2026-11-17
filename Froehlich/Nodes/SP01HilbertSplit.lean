import Froehlich.Nodes.SP01BlockInverse

/-! The bounded energy decomposition expressed in the native Hilbert
product, so its adjoints and form representatives use the genuine graph norm. -/
noncomputable section
namespace Froehlich

def vacuumHilbertSplit (P : GW.Space) :
    EnergySpace P →L[ℂ] WithLp 2 (ℂ × HighEnergySpace P 1) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (HighEnergySpace P 1)).symm.toContinuousLinearMap.comp
    (vacuumEnergySplit P)

def vacuumHilbertJoin (P : GW.Space) :
    WithLp 2 (ℂ × HighEnergySpace P 1) →L[ℂ] EnergySpace P :=
  (vacuumEnergyJoin P).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (HighEnergySpace P 1)).toContinuousLinearMap

theorem vacuumHilbertJoin_split (P : GW.Space) (u : EnergySpace P) :
    vacuumHilbertJoin P (vacuumHilbertSplit P u) = u := by
  change vacuumEnergyJoin P
    ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (HighEnergySpace P 1))
      ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (HighEnergySpace P 1)).symm (vacuumEnergySplit P u))) = u
  rw [ContinuousLinearEquiv.apply_symm_apply,vacuumEnergyJoin_split]

theorem vacuumHilbertSplit_join (P : GW.Space) (u : WithLp 2 (ℂ × HighEnergySpace P 1)) :
    vacuumHilbertSplit P (vacuumHilbertJoin P u) = u := by
  change (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (HighEnergySpace P 1)).symm
    (vacuumEnergySplit P (vacuumEnergyJoin P
      ((WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (HighEnergySpace P 1)) u))) = u
  rw [vacuumEnergySplit_join,ContinuousLinearEquiv.symm_apply_apply]

theorem vacuumHilbertJoin_split_adjoint (P : GW.Space) (u : EnergySpace P) :
    (vacuumHilbertSplit P).adjoint ((vacuumHilbertJoin P).adjoint u) = u := by
  have h : (vacuumHilbertJoin P).comp (vacuumHilbertSplit P) = ContinuousLinearMap.id ℂ (EnergySpace P) :=
    ContinuousLinearMap.ext (vacuumHilbertJoin_split P)
  have ha := congrArg ContinuousLinearMap.adjoint h
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at ha
  exact congrArg (fun T : EnergySpace P →L[ℂ] EnergySpace P => T u) ha

theorem vacuumHilbertSplit_join_adjoint (P : GW.Space)
    (u : WithLp 2 (ℂ × HighEnergySpace P 1)) :
    (vacuumHilbertJoin P).adjoint ((vacuumHilbertSplit P).adjoint u) = u := by
  have h : (vacuumHilbertSplit P).comp (vacuumHilbertJoin P) =
      ContinuousLinearMap.id ℂ (WithLp 2 (ℂ × HighEnergySpace P 1)) :=
    ContinuousLinearMap.ext (vacuumHilbertSplit_join P)
  have ha := congrArg ContinuousLinearMap.adjoint h
  simp only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] at ha
  exact congrArg (fun T : WithLp 2 (ℂ × HighEnergySpace P 1) →L[ℂ]
    WithLp 2 (ℂ × HighEnergySpace P 1) => T u) ha

theorem vacuumHilbertBlockInverse_left (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) :
    (hilbertProductOperator (vacuumBlockInverse g P hg lam)).comp
      (hilbertProductOperator (vacuumBlockOperator g P lam)) =
      ContinuousLinearMap.id ℂ (WithLp 2 (ℂ × HighEnergySpace P 1)) := by
  rw [← hilbertProductOperator_comp,vacuumBlockInverse_left g P hg lam hF,hilbertProductOperator_id]

theorem vacuumHilbertBlockInverse_right (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) :
    (hilbertProductOperator (vacuumBlockOperator g P lam)).comp
      (hilbertProductOperator (vacuumBlockInverse g P hg lam)) =
      ContinuousLinearMap.id ℂ (WithLp 2 (ℂ × HighEnergySpace P 1)) := by
  rw [← hilbertProductOperator_comp,vacuumBlockInverse_right g P hg lam hF,hilbertProductOperator_id]

end Froehlich
