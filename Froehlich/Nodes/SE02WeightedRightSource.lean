import Froehlich.Nodes.SE01Lambda
import Froehlich.Nodes.PT03KernelConvergence
import Froehlich.Nodes.PT03BoundsCutoffCoefficient
import Froehlich.Nodes.LD01

/-! Literal SE02 sources only in the weighted Q1 dual. The error majorant
is the accepted AN02 density; there is no unweighted singular L² vector. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def se02RightCoefficient (k : GW.Space) : ℂ :=
  (1-(groundSourceLambda e he g hg hs k : ℂ))*(fiberFormFactor g k : ℂ)

def se02CutoffRightCoefficient (Λ : GW.Operators.PositiveCutoff) (k : GW.Space) : ℂ :=
  (1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0)*(cutoffFormFactor g Λ.val k : ℂ)

theorem se02_right_factor_measurable :
    Measurable (fun k : GW.Space => 1-(groundSourceLambda e he g hg hs k : ℂ)) :=
  measurable_const.sub (Complex.continuous_ofReal.comp (groundSourceLambda_continuous e he g hg hs)).measurable

theorem se02_cutoff_factor_measurable (Λ : GW.Operators.PositiveCutoff) :
    Measurable (fun k : GW.Space => 1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0) := by
  have hm : Measurable (fun k : GW.Space => ((0 : GW.Space),(k,(0 : GW.Space)))) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have hJ : Measurable (fun t : GW.Space × (GW.Space × GW.Space) =>
      cutoffThresholdKernelJ e he g hg hs Λ t.1 t.2.1 t.2.2) :=
    (cutoffThresholdKernelJ_continuous e he g hg hs Λ).measurable
  have hc := hJ.comp hm
  have hsection : Measurable (fun k : GW.Space => cutoffThresholdKernelJ e he g hg hs Λ 0 k 0) := by
    simpa only [Function.comp_def] using! hc
  exact measurable_const.sub hsection

theorem se02RightCoefficient_measurable : Measurable (se02RightCoefficient e he g hg hs) :=
  (se02_right_factor_measurable e he g hg hs).mul
    (Complex.continuous_ofReal.measurable.comp (fiberFormFactor_measurable g))

theorem se02CutoffRightCoefficient_measurable (Λ : GW.Operators.PositiveCutoff) :
    Measurable (se02CutoffRightCoefficient e he g hg hs Λ) := by
  have hv : Measurable (cutoffFormFactor g Λ.val) := by
    unfold cutoffFormFactor
    exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
      (fiberFormFactor_measurable g) measurable_const
  exact (se02_cutoff_factor_measurable e he g hg hs Λ).mul
    (Complex.continuous_ofReal.measurable.comp hv)

private theorem se02_weighted_error (C : ℝ) (hC : 0 ≤ C) (g : ℝ) (k : GW.Space)
    (a b vc : ℂ) (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C)
    (hv : ‖vc‖ ≤ ‖(fiberFormFactor g k : ℂ)‖) :
    ‖(a*vc-b*(fiberFormFactor g k : ℂ))/(oneParticleEnergyWeight 0 k : ℂ)‖^2 ≤
      (4*C^2*g^2)*shiftedSourceDensity 0 k := by
  have h1 : ‖a*vc‖ ≤ C*‖(fiberFormFactor g k : ℂ)‖ := by
    rw [norm_mul]
    exact mul_le_mul ha hv (norm_nonneg _) hC
  have h2 : ‖b*(fiberFormFactor g k : ℂ)‖ ≤ C*‖(fiberFormFactor g k : ℂ)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have he : ‖a*vc-b*(fiberFormFactor g k : ℂ)‖ ≤ (2*C)*‖(fiberFormFactor g k : ℂ)‖ :=
    (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hq : ‖(a*vc-b*(fiberFormFactor g k : ℂ))/(oneParticleEnergyWeight 0 k : ℂ)‖ ≤
      (2*C)*‖(fiberFormFactor g k : ℂ)/(oneParticleEnergyWeight 0 k : ℂ)‖ := by
    rw [norm_div,norm_div]
    exact (div_le_div_of_nonneg_right he (norm_nonneg _)).trans_eq (by ring)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hC) (norm_nonneg _))).mpr hq
  rw [mul_pow,fiberSource_quotient_norm_sq,neg_zero] at hsq
  exact hsq.trans_eq (by ring)

theorem se02_right_uniform_majorant : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant * |g| ≤ 1/2),
      (∀ k : GW.Space, ‖1-(groundSourceLambda e he g hg hs k : ℂ)‖ ≤ C) ∧
      ∀ (Λ : GW.Operators.PositiveCutoff) (k : GW.Space),
        ‖1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0‖ ≤ C ∧
        ‖(se02CutoffRightCoefficient e he g hg hs Λ k-se02RightCoefficient e he g hg hs k)/
          (oneParticleEnergyWeight 0 k : ℂ)‖^2 ≤ (4*C^2*g^2)*shiftedSourceDensity 0 k := by
  obtain ⟨B,hB,hBound⟩ := thresholdKernels_uniform_bound
  refine ⟨1+B,by linarith,?_⟩
  intro e he g hg hs
  have hb (k : GW.Space) : ‖1-(groundSourceLambda e he g hg hs k : ℂ)‖ ≤ 1+B := by
    rw [groundSourceLambda_ofReal]
    exact (norm_sub_le _ _).trans (by
      simpa only [norm_one] using add_le_add (le_refl ‖(1 : ℂ)‖) (hBound g e he hg hs 0 k 0 (by simp)).1)
  refine ⟨hb,?_⟩
  intro Λ k
  have ha : ‖1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0‖ ≤ 1+B :=
    (norm_sub_le _ _).trans (by
      simpa only [norm_one] using add_le_add (le_refl ‖(1 : ℂ)‖)
        (((hBound g e he hg hs 0 k 0 (by simp)).2.2 Λ).1))
  exact ⟨ha,se02_weighted_error (1+B) (by linarith) g k
    (1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0) (1-(groundSourceLambda e he g hg hs k : ℂ))
    (cutoffFormFactor g Λ.val k : ℂ) ha (hb k) (pt03_cutoffCoefficient_norm_le g Λ k)⟩

theorem se02_right_quotient_memLp :
    MemLp (fun k => se02RightCoefficient e he g hg hs k/(oneParticleEnergyWeight 0 k : ℂ)) 2 volume := by
  obtain ⟨C,hC,hBound⟩ := se02_right_uniform_majorant
  exact weightedSource_factor_memLp (oneParticleEnergyWeight 0) (fun k => (fiberFormFactor g k : ℂ))
    (fun k => 1-(groundSourceLambda e he g hg hs k : ℂ)) (fiberSource_quotient_memLp g 0)
    (se02_right_factor_measurable e he g hg hs) (hBound e he g hg hs).1

theorem se02_cutoff_right_quotient_memLp (Λ : GW.Operators.PositiveCutoff) :
    MemLp (fun k => se02CutoffRightCoefficient e he g hg hs Λ k/(oneParticleEnergyWeight 0 k : ℂ)) 2 volume := by
  obtain ⟨C,hC,hBound⟩ := se02_right_uniform_majorant
  exact weightedSource_factor_memLp (oneParticleEnergyWeight 0) (fun k => (cutoffFormFactor g Λ.val k : ℂ))
    (fun k => 1-cutoffThresholdKernelJ e he g hg hs Λ 0 k 0) (cutoffFiberSource_quotient_memLp g Λ.val 0)
    (se02_cutoff_factor_measurable e he g hg hs Λ) (fun k => ((hBound e he g hg hs).2 Λ k).1)

def se02RightLoad : ConjugateLoad (OneParticleEnergySpace 0) :=
  weightedSourceLoad (oneParticleEnergyWeight 0) (se02RightCoefficient e he g hg hs)
    (se02_right_quotient_memLp e he g hg hs)

def se02CutoffWeightedRightLoad (Λ : GW.Operators.PositiveCutoff) : ConjugateLoad (OneParticleEnergySpace 0) :=
  weightedSourceLoad (oneParticleEnergyWeight 0) (se02CutoffRightCoefficient e he g hg hs Λ)
    (se02_cutoff_right_quotient_memLp e he g hg hs Λ)

theorem se02_error_majorant_integrable (C g : ℝ) :
    Integrable (fun k : GW.Space => (4*C^2*g^2)*shiftedSourceDensity 0 k) volume := by
  obtain ⟨Cv,hCv,hD⟩ := shiftedSourceDensity_uniform
  exact (hD 0).1.const_mul (4*C^2*g^2)

theorem se02_cutoff_right_quotient_tendsto (k : GW.Space) :
    Tendsto (fun Λ : GW.Operators.PositiveCutoff => se02CutoffRightCoefficient e he g hg hs Λ k/
      (oneParticleEnergyWeight 0 k : ℂ)) atTop
      (𝓝 (se02RightCoefficient e he g hg hs k/(oneParticleEnergyWeight 0 k : ℂ))) := by
  have hJ := cutoffThresholdKernelJ_tendsto e he g hg hs 0 k 0
  rw [←groundSourceLambda_ofReal e he g hg hs k] at hJ
  have hOne : Tendsto (fun _ : GW.Operators.PositiveCutoff => (1 : ℂ)) atTop (𝓝 (1 : ℂ)) := tendsto_const_nhds
  have hnum := (hOne.sub hJ).mul (pt03_cutoffCoefficient_tendsto g k)
  have hquot := hnum.mul_const ((oneParticleEnergyWeight 0 k : ℂ)⁻¹)
  simpa only [se02CutoffRightCoefficient,se02RightCoefficient,div_eq_mul_inv] using hquot

/-- Norm convergence along the explicit cofinal positive natural cutoffs.
This is sufficient for the singular dual identity; no full-filter assertion
is silently inferred from a single cofinal sequence. -/
theorem se02_weighted_right_load_tendsto_sequence :
    Tendsto (fun n : ℕ => se02CutoffWeightedRightLoad e he g hg hs (GW.Operators.positiveNatCutoff n))
      atTop (𝓝 (se02RightLoad e he g hg hs)) := by
  obtain ⟨C,hC,hBound⟩ := se02_right_uniform_majorant
  refine weightedSourceLoad_tendsto_dominated (oneParticleEnergyWeight 0)
    (fun n => se02CutoffRightCoefficient e he g hg hs (GW.Operators.positiveNatCutoff n))
    (se02RightCoefficient e he g hg hs)
    (fun n => se02_cutoff_right_quotient_memLp e he g hg hs (GW.Operators.positiveNatCutoff n))
    (se02_right_quotient_memLp e he g hg hs) ?_
    (fun k => (4*C^2*g^2)*shiftedSourceDensity 0 k) (se02_error_majorant_integrable C g) ?_
  · exact Eventually.of_forall (fun k => (se02_cutoff_right_quotient_tendsto e he g hg hs k).comp
      GW.Operators.positiveNatCutoff_tendsto)
  · intro n
    exact Eventually.of_forall (fun k => ((hBound e he g hg hs).2 (GW.Operators.positiveNatCutoff n) k).2)

end Froehlich
