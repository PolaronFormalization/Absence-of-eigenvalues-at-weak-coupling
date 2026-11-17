import Froehlich.Nodes.CA02
import Froehlich.Nodes.RS02NormalizedSource
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

set_option autoImplicit false

/-! Literal one-particle L2 source jets. The uncut form factor is multiplied
pointwise by the true reciprocal-weight jets before an L2 class is formed. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem auxiliaryWeight_one_particle (e : ℝ) (p k : GW.Space) :
    auxiliaryWeight 1 e p 1 (fun _ => k) = Real.sqrt (‖k+p‖^2+1-e) := by
  rw [auxiliaryWeight_of_ge 1 1 e p le_rfl]
  congr 1
  simp only [freeSymbol,totalMomentum,Fin.sum_univ_one,Nat.cast_one,sub_neg_eq_add]
  ring

theorem auxiliaryWeight_one_particle_ge_energy (e : ℝ) (he : e ≤ 0) (p k : GW.Space) :
    oneParticleEnergyWeight (-p) k ≤ auxiliaryWeight 1 e p 1 (fun _ => k) := by
  rw [auxiliaryWeight_one_particle,oneParticleEnergyWeight]
  apply Real.sqrt_le_sqrt
  simp only [sub_neg_eq_add]
  linarith

def auxiliarySourceJetFunction (is : List (Fin 3)) (g e : ℝ) (p k : GW.Space) : ℂ :=
  (auxiliaryInverseWeightJet is 1 e p 1 (fun _ => k) : ℂ)*(fiberFormFactor g k : ℂ)

theorem auxiliarySourceJetFunction_measurable (is : List (Fin 3)) (g e : ℝ) (p : GW.Space) :
    Measurable (auxiliarySourceJetFunction is g e p) := by
  have hK : Measurable (fun k : GW.Space => (fun _ : Fin 1 => k)) :=
    measurable_pi_lambda (fun _ => measurable_id)
  exact (Complex.continuous_ofReal.measurable.comp
    ((auxiliaryInverseWeightJet_measurable is 1 1 e p).comp hK)).mul
      (Complex.continuous_ofReal.measurable.comp (fiberFormFactor_measurable g))

theorem auxiliarySourceJetFunction_bound (is : List (Fin 3)) (g e : ℝ)
    (p k : GW.Space) (he : e ≤ 0) :
    ‖auxiliarySourceJetFunction is g e p k‖ ≤ scalarDerivativeCoefficientBound is.length*
      ‖(fiberFormFactor g k : ℂ)/(oneParticleEnergyWeight (-p) k : ℂ)‖ := by
  let W := auxiliaryWeight 1 e p 1 (fun _ => k)
  let V := oneParticleEnergyWeight (-p) k
  have hW : 0 < W := zero_lt_one.trans_le (auxiliaryWeight_ge_one 1 1 e p he _)
  have hV : 0 < V := zero_lt_one.trans_le (oneParticleEnergyWeight_ge_one (-p) k)
  have hInv : W⁻¹ ≤ V⁻¹ := (inv_le_inv₀ hW hV).mpr (auxiliaryWeight_one_particle_ge_energy e he p k)
  have hc := scalarDerivativeCoefficientBound_nonnegative is.length
  have hj := auxiliaryInverseWeightJet_relative_bound is 1 1 e p he (fun _ => k)
  change ‖(auxiliaryInverseWeightJet is 1 e p 1 (fun _ => k) : ℂ)*(fiberFormFactor g k : ℂ)‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (scalarDerivativeCoefficientBound is.length*W⁻¹)*‖(fiberFormFactor g k : ℂ)‖ :=
      mul_le_mul_of_nonneg_right hj (norm_nonneg _)
    _ ≤ (scalarDerivativeCoefficientBound is.length*V⁻¹)*‖(fiberFormFactor g k : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hInv hc) (norm_nonneg _)
    _ = _ := by
      rw [norm_div]
      change (scalarDerivativeCoefficientBound is.length*V⁻¹)*‖(fiberFormFactor g k : ℂ)‖ =
        scalarDerivativeCoefficientBound is.length*(‖(fiberFormFactor g k : ℂ)‖/‖(V : ℂ)‖)
      rw [Complex.norm_real V,Real.norm_eq_abs V,abs_of_pos hV,div_eq_mul_inv]
      ring

theorem auxiliarySourceJetFunction_memLp (is : List (Fin 3)) (g e : ℝ)
    (p : GW.Space) (he : e ≤ 0) : MemLp (auxiliarySourceJetFunction is g e p) 2 volume :=
  (fiberSource_quotient_memLp g (-p)).of_le_mul
    (auxiliarySourceJetFunction_measurable is g e p).aestronglyMeasurable
    (Eventually.of_forall (fun k => auxiliarySourceJetFunction_bound is g e p k he))

def auxiliarySourceJetL2 (is : List (Fin 3)) (g e : ℝ) (p : GW.Space) (he : e ≤ 0) : GW.OnePhonon :=
  (auxiliarySourceJetFunction_memLp is g e p he).toLp (auxiliarySourceJetFunction is g e p)

theorem auxiliarySourceJetL2_ae (is : List (Fin 3)) (g e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    (auxiliarySourceJetL2 is g e p he : GW.Space → ℂ) =ᵐ[volume] auxiliarySourceJetFunction is g e p :=
  (auxiliarySourceJetFunction_memLp is g e p he).coeFn_toLp

theorem auxiliarySourceJetL2_norm_le_reference (is : List (Fin 3)) (g e : ℝ)
    (p : GW.Space) (he : e ≤ 0) :
    ‖auxiliarySourceJetL2 is g e p he‖ ≤ scalarDerivativeCoefficientBound is.length*
      ‖weightedSourceCoordinate (oneParticleEnergyWeight (-p)) (fun k => (fiberFormFactor g k : ℂ))
        (fiberSource_quotient_memLp g (-p))‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [auxiliarySourceJetL2_ae is g e p he,
    weightedSourceCoordinate_ae (oneParticleEnergyWeight (-p)) (fun k => (fiberFormFactor g k : ℂ))
      (fiberSource_quotient_memLp g (-p))] with k hk href
  rw [hk,href]
  exact auxiliarySourceJetFunction_bound is g e p k he

end Froehlich
