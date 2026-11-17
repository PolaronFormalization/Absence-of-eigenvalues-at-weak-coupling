import Froehlich.Nodes.SP01BlockForm
import Froehlich.Nodes.SP01HilbertSplit
import Froehlich.Nodes.FA01

/-! Full-domain physical resolvent from the literal vacuum Schur block
inverse, transported through the actual complete energy decomposition. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def vacuumEnergyOperator (g : ℝ) (P : GW.Space) (lam : ℝ) : EnergySpace P →L[ℂ] EnergySpace P :=
  (vacuumHilbertSplit P).adjoint.comp
    ((hilbertProductOperator (vacuumBlockOperator g P lam)).comp (vacuumHilbertSplit P))

def vacuumEnergyInverse (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) : EnergySpace P →L[ℂ] EnergySpace P :=
  (vacuumHilbertJoin P).comp ((hilbertProductOperator (vacuumBlockInverse g P hg lam)).comp
    (vacuumHilbertJoin P).adjoint)

theorem vacuumEnergyOperator_spec (g : ℝ) (P : GW.Space) (lam : ℝ) (w u : EnergySpace P) :
    ⟪w,vacuumEnergyOperator g P lam u⟫_ℂ = (fiberFormData g P none).form w u -
      (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ := by
  have hf := vacuumBlockForm_identity g P lam (vacuumEnergySplit P w) (vacuumEnergySplit P u)
  rw [vacuumEnergyJoin_split,vacuumEnergyJoin_split] at hf
  rw [vacuumEnergyOperator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    (vacuumHilbertSplit P).adjoint_inner_right,WithLp.prod_inner_apply]
  change ⟪(vacuumEnergySplit P w).1,(vacuumBlockOperator g P lam (vacuumEnergySplit P u)).1⟫_ℂ +
    ⟪(vacuumEnergySplit P w).2,(vacuumBlockOperator g P lam (vacuumEnergySplit P u)).2⟫_ℂ = _
  exact hf.symm

theorem vacuumEnergyInverse_left (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) :
    vacuumEnergyInverse g P hg lam * vacuumEnergyOperator g P lam = 1 := by
  ext u
  change vacuumHilbertJoin P (hilbertProductOperator (vacuumBlockInverse g P hg lam)
    ((vacuumHilbertJoin P).adjoint ((vacuumHilbertSplit P).adjoint
      (hilbertProductOperator (vacuumBlockOperator g P lam) (vacuumHilbertSplit P u))))) = u
  rw [vacuumHilbertSplit_join_adjoint]
  have hi := congrArg (fun T : WithLp 2 (ℂ × HighEnergySpace P 1) →L[ℂ]
      WithLp 2 (ℂ × HighEnergySpace P 1) => T (vacuumHilbertSplit P u))
    (vacuumHilbertBlockInverse_left g P hg lam hF)
  change hilbertProductOperator (vacuumBlockInverse g P hg lam)
    (hilbertProductOperator (vacuumBlockOperator g P lam) (vacuumHilbertSplit P u)) =
      vacuumHilbertSplit P u at hi
  rw [hi,vacuumHilbertJoin_split]

theorem vacuumEnergyInverse_right (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) :
    vacuumEnergyOperator g P lam * vacuumEnergyInverse g P hg lam = 1 := by
  ext u
  change (vacuumHilbertSplit P).adjoint (hilbertProductOperator (vacuumBlockOperator g P lam)
    (vacuumHilbertSplit P (vacuumHilbertJoin P
      (hilbertProductOperator (vacuumBlockInverse g P hg lam) ((vacuumHilbertJoin P).adjoint u))))) = u
  rw [vacuumHilbertSplit_join]
  have hi := congrArg (fun T : WithLp 2 (ℂ × HighEnergySpace P 1) →L[ℂ]
      WithLp 2 (ℂ × HighEnergySpace P 1) => T ((vacuumHilbertJoin P).adjoint u))
    (vacuumHilbertBlockInverse_right g P hg lam hF)
  change hilbertProductOperator (vacuumBlockOperator g P lam)
    (hilbertProductOperator (vacuumBlockInverse g P hg lam) ((vacuumHilbertJoin P).adjoint u)) =
      (vacuumHilbertJoin P).adjoint u at hi
  rw [hi,vacuumHilbertJoin_split_adjoint]

theorem vacuumSchurFunction_ne_zero_mem_resolvent (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (lam : Set.Iio (nonvacuumThreshold g)) (hF : vacuumSchurFunction g P hg lam ≠ 0) :
    (lam : ℝ) ∈ realResolventSet (fiberHamiltonian g P) := by
  refine ⟨physicalEnergyInverse (fiberFormData g P none) (vacuumEnergyInverse g P hg lam),?_⟩
  exact physicalEnergyInverse_isResolvent (fiberFormData g P none) lam
    (vacuumEnergyOperator g P lam) (vacuumEnergyInverse g P hg lam)
    (vacuumEnergyOperator_spec g P lam) (vacuumEnergyInverse_left g P hg lam hF)
    (vacuumEnergyInverse_right g P hg lam hF)

end Froehlich
