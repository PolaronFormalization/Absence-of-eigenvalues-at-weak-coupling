import Froehlich.Nodes.RS02SourceJetsL2

set_option autoImplicit false

/-! The integrable AN02 source majorant and constants chosen before every
coupling and reference parameter. Signed and zero couplings are retained. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem auxiliarySourceJetFunction_nil (g e : ℝ) (p k : GW.Space) (he : e ≤ 0) :
    auxiliarySourceJetFunction [] g e p k =
      (fiberFormFactor g k : ℂ)/(auxiliaryWeight 1 e p 1 (fun _ => k) : ℂ) := by
  rw [auxiliarySourceJetFunction,auxiliaryInverseWeightJet_nil 1 1 e p he]
  rw [Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

theorem auxiliarySourceJet_squared_majorant_integrable (g e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    Integrable (fun k : GW.Space => ‖auxiliarySourceJetFunction [] g e p k‖^2) volume :=
  (memLp_two_iff_integrable_sq_norm
    (auxiliarySourceJetFunction_measurable [] g e p).aestronglyMeasurable).mp
      (auxiliarySourceJetFunction_memLp [] g e p he)

theorem auxiliarySourceJets_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (is : List (Fin 3)) (g e : ℝ) (p : GW.Space) (he : e ≤ 0),
      ‖auxiliarySourceJetL2 is g e p he‖ ≤ scalarDerivativeCoefficientBound is.length*C*|g| := by
  obtain ⟨Cv,hCv,hv⟩ := fiberSourceLoads_uniform_bound
  refine ⟨Real.sqrt Cv,Real.sqrt_pos.mpr hCv,?_⟩
  intro is g e p he
  let z := weightedSourceCoordinate (oneParticleEnergyWeight (-p))
    (fun k => (fiberFormFactor g k : ℂ)) (fiberSource_quotient_memLp g (-p))
  have hzsq : ‖z‖^2 ≤ Cv*g^2 := by
    have h := (hv g (-p)).1
    rw [isolatedFiberSourceLoad,weightedSourceLoad_norm] at h
    exact h
  have hz : ‖z‖ ≤ Real.sqrt Cv*|g| := by
    apply (sq_le_sq₀ (norm_nonneg z) (mul_nonneg (Real.sqrt_nonneg Cv) (abs_nonneg g))).mp
    rw [mul_pow,Real.sq_sqrt hCv.le,sq_abs]
    exact hzsq
  have hj := auxiliarySourceJetL2_norm_le_reference is g e p he
  exact hj.trans (by
    change scalarDerivativeCoefficientBound is.length*‖z‖ ≤ _
    calc
      _ ≤ scalarDerivativeCoefficientBound is.length*(Real.sqrt Cv*|g|) :=
        mul_le_mul_of_nonneg_left hz (scalarDerivativeCoefficientBound_nonnegative is.length)
      _ = _ := by ring)

end Froehlich
