import Froehlich.Nodes.RS02SourceJetsBounds
import Froehlich.Nodes.CA02WeightedScalarRemainder

set_option autoImplicit false

/-! Pointwise source remainders dominated by the actual AN02 L2 source at
the base point. The squared majorant is explicitly integrable. -/
noncomputable section
open MeasureTheory
namespace Froehlich

def auxiliarySourceJetChartFunction (is : List (Fin 3)) (g e : ℝ)
    (q : Fin 3 → ℝ) (k : GW.Space) : ℂ :=
  auxiliarySourceJetFunction is g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) k

def sourceJetRemainderCoefficient (r : ℕ) : ℝ :=
  scalarDerivativeCoefficientBound (r+2)*(1+euclideanChartInverseNorm)/2

theorem auxiliarySourceJetChartFunction_coordinate_remainder (is : List (Fin 3))
    (g e : ℝ) (he : e ≤ 0) (q : Fin 3 → ℝ) (i : Fin 3) (t : ℝ)
    (ht : |t-q i| ≤ 1) (k : GW.Space) :
    ‖auxiliarySourceJetChartFunction is g e (Function.update q i t) k-
      auxiliarySourceJetChartFunction is g e q k-
      (t-q i) • auxiliarySourceJetChartFunction (i::is) g e q k‖ ≤
      (sourceJetRemainderCoefficient is.length*|t-q i|^2)*
        ‖auxiliarySourceJetChartFunction [] g e q k‖ := by
  let p := (EuclideanSpace.equiv (Fin 3) ℝ).symm q
  let K : GW.Fock.Coordinates 1 := fun _ => k
  let W := auxiliaryWeight 1 e p 1 K
  let R := auxiliaryInverseWeightJetChart is 1 e (Function.update q i t) 1 K-
    auxiliaryInverseWeightJetChart is 1 e q 1 K-
    (t-q i)*auxiliaryInverseWeightJetChart (i::is) 1 e q 1 K
  have hW : 0 < W := zero_lt_one.trans_le (auxiliaryWeight_ge_one 1 1 e p he K)
  have hTaylor := auxiliaryInverseWeightJetChart_fixed_weight_remainder is 1 1 e he p q K i t ht
  have hTaylor' : |W*R| ≤ sourceJetRemainderCoefficient is.length*|t-q i|^2 := by
    simpa only [p,W,R,sourceJetRemainderCoefficient,sub_self,norm_zero,add_zero] using! hTaylor
  have hR : |R| ≤ (sourceJetRemainderCoefficient is.length*|t-q i|^2)*W⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hW).mpr
    have hT : W*|R| ≤ sourceJetRemainderCoefficient is.length*|t-q i|^2 := by
      simpa only [abs_mul,abs_of_pos hW] using hTaylor'
    simpa only [mul_comm W] using hT
  have heq : auxiliarySourceJetChartFunction is g e (Function.update q i t) k-
      auxiliarySourceJetChartFunction is g e q k-
      (t-q i) • auxiliarySourceJetChartFunction (i::is) g e q k =
      (R : ℂ)*(fiberFormFactor g k : ℂ) := by
    simp only [auxiliarySourceJetChartFunction,auxiliarySourceJetFunction,R,
      auxiliaryInverseWeightJetChart,K,Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_mul]
    ring
  have hbase : ‖auxiliarySourceJetChartFunction [] g e q k‖ = W⁻¹*‖(fiberFormFactor g k : ℂ)‖ := by
    change ‖(auxiliaryInverseWeightJet [] 1 e p 1 K : ℂ)*(fiberFormFactor g k : ℂ)‖ = _
    rw [auxiliaryInverseWeightJet_nil 1 1 e p he K,norm_mul,
      Complex.norm_real W⁻¹,Real.norm_eq_abs W⁻¹,abs_of_pos (inv_pos.mpr hW)]
  rw [heq,norm_mul,Complex.norm_real R,Real.norm_eq_abs R,hbase]
  calc
    _ ≤ ((sourceJetRemainderCoefficient is.length*|t-q i|^2)*W⁻¹)*‖(fiberFormFactor g k : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ = _ := by ring

theorem auxiliarySourceJet_squared_remainder_majorant_integrable (r : ℕ)
    (g e : ℝ) (he : e ≤ 0) (q : Fin 3 → ℝ) :
    Integrable (fun k : GW.Space => (sourceJetRemainderCoefficient r)^2*
      ‖auxiliarySourceJetChartFunction [] g e q k‖^2) volume :=
  (auxiliarySourceJet_squared_majorant_integrable g e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he).const_mul _

end Froehlich
