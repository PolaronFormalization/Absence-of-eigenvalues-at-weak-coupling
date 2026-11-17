import Froehlich.Nodes.CA02FixedEnergyCoordinates
import Froehlich.Nodes.CA02PhysicalDerivative
import Froehlich.Nodes.CA02WeightedScalarRemainder

set_option autoImplicit false

/-! Actual quadratic operator remainders in the existing fixed-energy
isometric coordinates, with a locally uniform bound over all sectors. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def auxiliaryFixedEnergyJetChartCoordinates (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0)
    (is : List (Fin 3)) (p : Fin 3 → ℝ) : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  auxiliaryFixedEnergyJetCoordinates is n e p0 ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he

theorem auxiliaryFixedEnergyJetChartCoordinates_ae (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) (p : Fin 3 → ℝ) (f : HighSectorSpace n) :
    (fun K => ((auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJetChart is n e p m K : ℝ) : ℂ) •
      physicalSector m ((f : GW.Fock.Carrier) m) K) =ᵐ[GW.Fock.sectorMeasure m]
      physicalSector m ((auxiliaryFixedEnergyJetChartCoordinates n e p0 he is p f : GW.Fock.Carrier) m) :=
  auxiliaryFixedEnergyJetCoordinates_ae is n m e p0 ((EuclideanSpace.equiv (Fin 3) ℝ).symm p) he f

theorem auxiliaryFixedEnergyJetChartCoordinates_coordinate_remainder
    (is : List (Fin 3)) (n : ℕ) (e : ℝ) (p0 : GW.Space) (he : e ≤ 0)
    (p : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) (ht : |t-p i| ≤ 1) :
    ‖auxiliaryFixedEnergyJetChartCoordinates n e p0 he is (Function.update p i t)-
      auxiliaryFixedEnergyJetChartCoordinates n e p0 he is p-
      (t-p i) • auxiliaryFixedEnergyJetChartCoordinates n e p0 he (i::is) p‖ ≤
      (scalarDerivativeCoefficientBound (is.length+2)*
        (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖+euclideanChartInverseNorm)/2)*‖t-p i‖^2 := by
  let C := (scalarDerivativeCoefficientBound (is.length+2)*
    (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖+euclideanChartInverseNorm)/2)*‖t-p i‖^2
  have hE : 0 ≤ euclideanChartInverseNorm := norm_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (div_nonneg (mul_nonneg
      (scalarDerivativeCoefficientBound_nonnegative (is.length+2)) (by positivity)) (by norm_num))
      (sq_nonneg _)
  let a : List (Fin 3) → (Fin 3 → ℝ) → ∀ m, GW.Fock.Coordinates m → ℝ :=
    fun js q m K => auxiliaryWeight n e p0 m K * auxiliaryInverseWeightJetChart js n e q m K
  apply operator_norm_le_of_ae_multiplier_coordinates
    (HighSectorSpace n).subtypeₗᵢ (HighSectorSpace n).subtypeₗᵢ _
    (fun m K => ((a is (Function.update p i t) m K-a is p m K-(t-p i)*a (i::is) p m K : ℝ) : ℂ)) C hC
  · intro m K
    have heq : a is (Function.update p i t) m K-a is p m K-(t-p i)*a (i::is) p m K =
        auxiliaryWeight n e p0 m K *
          (auxiliaryInverseWeightJetChart is n e (Function.update p i t) m K-
           auxiliaryInverseWeightJetChart is n e p m K-
           (t-p i)*auxiliaryInverseWeightJetChart (i::is) n e p m K) := by
      dsimp only [a]
      ring
    rw [heq,Complex.norm_real,Real.norm_eq_abs]
    simpa only [C,Real.norm_eq_abs] using
      auxiliaryInverseWeightJetChart_fixed_weight_remainder is n m e he p0 p K i t ht
  · intro f m
    exact highOperatorRemainder_ae n _ _ _ (t-p i) _ _ _
      (fun (f : HighSectorSpace n) m => auxiliaryFixedEnergyJetChartCoordinates_ae is n m e p0 he (Function.update p i t) f)
      (fun (f : HighSectorSpace n) m => auxiliaryFixedEnergyJetChartCoordinates_ae is n m e p0 he p f)
      (fun (f : HighSectorSpace n) m => auxiliaryFixedEnergyJetChartCoordinates_ae (i::is) n m e p0 he p f) f m

end Froehlich
