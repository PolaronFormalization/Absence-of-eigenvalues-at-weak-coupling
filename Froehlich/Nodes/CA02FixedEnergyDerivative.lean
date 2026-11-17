import Froehlich.Nodes.CA02FixedEnergyRemainder
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false

/-! Genuine norm derivatives in the fixed weighted target, transported only
through its existing onto coordinate isometry. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
open scoped BoundedEndReal

local instance ca02FixedEnergyDerivativeHighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ca02FixedEnergyDerivativeEndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02FixedEnergyDerivativeEndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance ca02FixedEnergyDerivativeEndRealBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance ca02FixedEnergyDerivativeEndRealContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasDerivAt_of_eventually_quadratic_remainder (F : ℝ → V) (D : V) (x C : ℝ)
    (h : ∀ᶠ t in 𝓝 x, ‖F t-F x-(t-x) • D‖ ≤ C*‖t-x‖^2) : HasDerivAt F D x := by
  apply HasDerivAt.of_isLittleO
  have hb : (fun t => F t-F x-(t-x) • D) =O[𝓝 x] (fun t => ‖t-x‖^2) :=
    Asymptotics.IsBigO.of_bound C (h.mono (fun t ht => by
      simpa only [norm_pow,norm_norm] using ht))
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < (2 : ℕ)))

theorem auxiliaryFixedEnergyJetChartCoordinates_hasDerivAt_update
    (is : List (Fin 3)) (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0)
    (p : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => auxiliaryFixedEnergyJetChartCoordinates n e p0 he is (Function.update p i t))
      (auxiliaryFixedEnergyJetChartCoordinates n e p0 he (i::is) p) (p i) := by
  apply hasDerivAt_of_eventually_quadratic_remainder _ _ _
    (scalarDerivativeCoefficientBound (is.length+2)*
      (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖+euclideanChartInverseNorm)/2)
  have hnear : ∀ᶠ t : ℝ in 𝓝 (p i), ‖t-p i‖ < 1 := by
    exact (continuousAt_id.sub continuousAt_const).norm.tendsto.eventually_lt_const (by simp)
  filter_upwards [hnear] with t ht
  simpa only [Function.update_eq_self] using!
    auxiliaryFixedEnergyJetChartCoordinates_coordinate_remainder is n e p0 he p i t
      (by simpa only [Real.norm_eq_abs] using ht.le)

local instance ca02FixedEnergyDerivativeEnergyNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (AuxiliaryEnergySpace n e p0 he) :=
  Submodule.normedAddCommGroup (AuxiliaryEnergySpace n e p0 he)
local instance ca02FixedEnergyDerivativeEnergyMapNormedGroup (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedAddCommGroup (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ca02FixedEnergyDerivativeEnergyMapRealNormedSpace (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    NormedSpace ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance ca02FixedEnergyDerivativeEnergyMapRealBoundedSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  NormedSpace.toIsBoundedSMul
local instance ca02FixedEnergyDerivativeEnergyMapRealContinuousSMul (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) :
    ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
  IsBoundedSMul.continuousSMul

def auxiliaryFixedEnergyWeightJetChart (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0)
    (is : List (Fin 3)) (p : Fin 3 → ℝ) : HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he :=
  auxiliaryFixedEnergyWeightJet is n e p0 ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he

theorem auxiliaryFixedEnergyWeightJetChart_hasDerivAt_update
    (is : List (Fin 3)) (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0)
    (p : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => auxiliaryFixedEnergyWeightJetChart n e p0 he is (Function.update p i t))
      (auxiliaryFixedEnergyWeightJetChart n e p0 he (i::is) p) (p i) := by
  let L : (HighSectorSpace n →L[ℂ] HighSectorSpace n) →L[ℝ]
      (HighSectorSpace n →L[ℂ] AuxiliaryEnergySpace n e p0 he) :=
    ((ContinuousLinearMap.compL ℂ (HighSectorSpace n) (HighSectorSpace n)
      (AuxiliaryEnergySpace n e p0 he))
      (auxiliaryFreeInverseEnergy n e p0 he).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ
  have hidentity (js : List (Fin 3)) (q : Fin 3 → ℝ) :
      L (auxiliaryFixedEnergyJetChartCoordinates n e p0 he js q) =
        auxiliaryFixedEnergyWeightJetChart n e p0 he js q := by
    apply ContinuousLinearMap.ext
    intro f
    change (auxiliaryEnergyCoordinates n e p0 he).symm
      ((auxiliaryEnergyCoordinates n e p0 he) (auxiliaryFixedEnergyWeightJetChart n e p0 he js q f)) = _
    exact (auxiliaryEnergyCoordinates n e p0 he).symm_apply_apply _
  have hd := L.hasFDerivAt.comp_hasDerivAt (p i)
    (auxiliaryFixedEnergyJetChartCoordinates_hasDerivAt_update is n e p0 he p i)
  have hdc := hd.congr_deriv (hidentity (i::is) p)
  apply hdc.congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => (hidentity is (Function.update p i t)).symm)

end Froehlich
