import Froehlich.Nodes.CA02PhysicalJets
import Froehlich.Nodes.CA02ScalarRemainder
import Froehlich.Nodes.CA01Inverse

set_option autoImplicit false

/-! Genuine operator-norm coordinate derivatives of the physical source G
and its literal higher derivative symbols. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich
open scoped BoundedEndReal

local instance ca02PhysicalDerivativeHighNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)

local instance ca02PhysicalDerivativeEndNormedGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance ca02PhysicalDerivativeEndRealNormedSpace (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace

local instance ca02PhysicalDerivativeEndRealBoundedSMul (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul

local instance ca02PhysicalDerivativeEndRealContinuousSMul (n : ℕ) : ContinuousSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  IsBoundedSMul.continuousSMul

theorem highOperatorRemainder_ae (n : ℕ)
    (A B D : HighSectorSpace n →L[ℂ] HighSectorSpace n) (c : ℝ)
    (a b d : ∀ m, GW.Fock.Coordinates m → ℝ)
    (hA : ∀ (f : HighSectorSpace n) (m : ℕ), (fun K => (a m K : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K)
      =ᵐ[GW.Fock.sectorMeasure m] physicalSector m ((A f : GW.Fock.Carrier) m))
    (hB : ∀ (f : HighSectorSpace n) (m : ℕ), (fun K => (b m K : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K)
      =ᵐ[GW.Fock.sectorMeasure m] physicalSector m ((B f : GW.Fock.Carrier) m))
    (hD : ∀ (f : HighSectorSpace n) (m : ℕ), (fun K => (d m K : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K)
      =ᵐ[GW.Fock.sectorMeasure m] physicalSector m ((D f : GW.Fock.Carrier) m))
    (f : HighSectorSpace n) (m : ℕ) :
    (fun K => ((a m K-b m K-c*d m K : ℝ) : ℂ) • physicalSector m ((f : GW.Fock.Carrier) m) K)
      =ᵐ[GW.Fock.sectorMeasure m] physicalSector m (((A-B-c • D) f : GW.Fock.Carrier) m) := by
  let u := physicalSector m ((A f : GW.Fock.Carrier) m)
  let v := physicalSector m ((B f : GW.Fock.Carrier) m)
  let w := physicalSector m ((D f : GW.Fock.Carrier) m)
  have hlin : physicalSector m (((A-B-c • D) f : GW.Fock.Carrier) m) = u-v-c • w := by
    change physicalSector m (((A f : GW.Fock.Carrier) m)-((B f : GW.Fock.Carrier) m)-
      c • ((D f : GW.Fock.Carrier) m)) = _
    rw [map_sub,map_sub,LinearMapClass.map_smul_of_tower]
  rw [hlin]
  filter_upwards [hA f m,hB f m,hD f m,Lp.coeFn_sub (u-v) (c • w),
    Lp.coeFn_sub u v,Lp.coeFn_smul c w] with K hAK hBK hDK hsub hsub' hsmul
  change _ = (u-v-c • w) K
  rw [hsub]
  change _ = (u-v) K-(c • w) K
  rw [hsub',hsmul]
  change _ = u K-v K-c • w K
  rw [← hAK,← hBK,← hDK]
  simp only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.real_smul,smul_eq_mul]
  ring

theorem auxiliaryPhysicalWeightJetChart_coordinate_remainder
    (is : List (Fin 3)) (n : ℕ) (e : ℝ) (he : e ≤ 0)
    (p : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    ‖auxiliaryPhysicalWeightJetChart n e he is (Function.update p i t) -
      auxiliaryPhysicalWeightJetChart n e he is p -
      (t-p i) • auxiliaryPhysicalWeightJetChart n e he (i::is) p‖ ≤
      (scalarDerivativeCoefficientBound (is.length+2)/2)*‖t-p i‖^2 := by
  let C := (scalarDerivativeCoefficientBound (is.length+2)/2)*‖t-p i‖^2
  have hC : 0 ≤ C := mul_nonneg (div_nonneg
    (scalarDerivativeCoefficientBound_nonnegative (is.length+2)) (by norm_num)) (sq_nonneg _)
  apply operator_norm_le_of_ae_multiplier_coordinates
    (HighSectorSpace n).subtypeₗᵢ (HighSectorSpace n).subtypeₗᵢ _
    (fun m K => ((auxiliaryInverseWeightJetChart is n e (Function.update p i t) m K-
      auxiliaryInverseWeightJetChart is n e p m K-
      (t-p i)*auxiliaryInverseWeightJetChart (i::is) n e p m K : ℝ) : ℂ)) C hC
  · intro m K
    have h := auxiliaryInverseWeightJetChart_coordinate_remainder is n m e he p K i t
    simpa only [Complex.norm_real,Real.norm_eq_abs,C,div_mul_eq_mul_div] using h
  · intro f m
    exact highOperatorRemainder_ae n _ _ _ (t-p i) _ _ _
      (fun (f : HighSectorSpace n) m => auxiliaryPhysicalWeightJetChart_ae is n m e he (Function.update p i t) f)
      (fun (f : HighSectorSpace n) m => auxiliaryPhysicalWeightJetChart_ae is n m e he p f)
      (fun (f : HighSectorSpace n) m => auxiliaryPhysicalWeightJetChart_ae (i::is) n m e he p f) f m

theorem auxiliaryPhysicalWeightJetChart_hasDerivAt_update
    (is : List (Fin 3)) (n : ℕ) (e : ℝ) (he : e ≤ 0) (p : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => auxiliaryPhysicalWeightJetChart n e he is (Function.update p i t))
      (auxiliaryPhysicalWeightJetChart n e he (i::is) p) (p i) := by
  apply hasDerivAt_of_uniform_quadratic_remainder _ _ _
    (scalarDerivativeCoefficientBound (is.length+2)/2)
  intro t
  simpa only [Function.update_eq_self] using!
    auxiliaryPhysicalWeightJetChart_coordinate_remainder is n e he p i t

end Froehlich
