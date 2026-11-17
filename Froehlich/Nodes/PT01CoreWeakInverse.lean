import Froehlich.Nodes.CV01InversePairs
import Froehlich.Nodes.CV01PhysicalInverse

/-! A solution of the actual fixed-energy cutoff weak equation is the
literal physical resolvent applied to its physical source. -/
noncomputable section
namespace Froehlich
variable (m : ℕ) (e : ℝ) (p0 q : GW.Space) (hm : m ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Lambda : GW.Operators.PositiveCutoff)
include hg hs

theorem cutoffCommonFormOperator_injective :
    Function.Injective (cutoffCommonFormOperator m e p0 q hm he g Lambda) := by
  have hleft : Function.LeftInverse (cutoffCommonEnergyInverse m e p0 q hm he g hg hs Lambda)
      (cutoffCommonFormOperator m e p0 q hm he g Lambda) := by
    intro u
    exact congrArg (fun T : HighEnergySpace (-p0) m →L[ℂ] HighEnergySpace (-p0) m => T u)
      (cutoffCommonFormOperator_inverse_pair m e p0 q hm he g hg hs Lambda).1
  exact hleft.injective

theorem cutoff_fixedWeakSolution_physical (U : HighEnergySpace (-p0) m) (F : HighSectorSpace m)
    (hEq : cutoffCommonFormOperator m e p0 q hm he g Lambda U=(highEnergyEmbedding (-p0) m).adjoint F) :
    highEnergyEmbedding (-p0) m U=cutoffAuxiliaryResolvent m e q he Lambda g hg hs F := by
  have hleft := congrArg (fun T : HighEnergySpace (-p0) m →L[ℂ] HighEnergySpace (-p0) m => T U)
    (cutoffCommonFormOperator_inverse_pair m e p0 q hm he g hg hs Lambda).1
  change cutoffCommonEnergyInverse m e p0 q hm he g hg hs Lambda
    (cutoffCommonFormOperator m e p0 q hm he g Lambda U)=U at hleft
  rw [hEq] at hleft
  rw [←hleft]
  exact congrArg (fun T : HighSectorSpace m →L[ℂ] HighSectorSpace m => T F)
    (cutoffCommonEnergyInverse_physical m e p0 q hm he g hg hs Lambda)

end Froehlich
