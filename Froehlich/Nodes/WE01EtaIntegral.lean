import Froehlich.Nodes.WE01Source

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

def weightedEtaIntegral (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (P : GW.Space) (eta : GW.Space → ℝ) (q : GW.Space) : ℝ :=
  ∫ r, remainderKernel e he g hg hs P q r*muDensity P r*eta r

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space)

theorem weightedEtaIntegral_zero (eta : GW.Space → ℝ) :
    weightedEtaIntegral e he g hg hs P eta 0 = 0 := by
  simp only [weightedEtaIntegral,remainderKernel_left_zero,zero_mul,integral_zero]

theorem weightedEtaIntegral_congr_ae (eta zeta : GW.Space → ℝ)
    (hz : eta =ᵐ[volume] zeta) (q : GW.Space) :
    weightedEtaIntegral e he g hg hs P eta q = weightedEtaIntegral e he g hg hs P zeta q := by
  apply integral_congr_ae
  filter_upwards [hz] with r hr
  rw [hr]

/-- No unweighted mu integrability is used: exactly omega squared times mu
controls every input bounded by M omega. -/
theorem weightedEtaIntegral_uniform : ∃ CW : ℝ, 0 < CW ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space), ‖P‖ ≤ 1/4 →
      ∀ (M : ℝ), 0 ≤ M → ∀ (eta : GW.Space → ℝ), AEStronglyMeasurable eta volume →
      (∀ᵐ r ∂volume, |eta r| ≤ M*omega r) → ∀ q : GW.Space,
      Integrable (fun r => remainderKernel e he g hg hs P q r*muDensity P r*eta r) volume ∧
      ‖weightedEtaIntegral e he g hg hs P eta q‖ ≤ CW*M*omega q := by
  obtain ⟨C,hC,hF⟩ := remainderKernel_uniform_bound
  obtain ⟨CI,hCI,hI⟩ := weightedKernelDensity_integral_uniform
  refine Exists.intro (C*CI) ?_
  refine And.intro (mul_pos hC hCI) ?_
  intro e he g hg hs P hP M hM eta hEta hBound q
  have hqr : Measurable (fun r : GW.Space => (q,r)) :=
    measurable_const.prodMk measurable_id
  have hcomp : Measurable ((Function.uncurry (remainderKernel e he g hg hs P)) ∘
      (fun r : GW.Space => (q,r))) :=
    (remainderKernel_measurable e he g hg hs P).comp hqr
  have hmF : Measurable (fun r : GW.Space => remainderKernel e he g hg hs P q r) := by
    simpa only [Function.comp_def,Function.uncurry] using! hcomp
  have hmeas : AEStronglyMeasurable
      (fun r => remainderKernel e he g hg hs P q r*muDensity P r*eta r) volume := by
    simpa only [Pi.mul_def] using!
      (hmF.mul (muDensity_measurable P)).aestronglyMeasurable.mul hEta
  have hnon : 0 ≤ C*M*omega q := mul_nonneg (mul_nonneg hC.le hM) (omega_nonneg q)
  have hdom : ∀ᵐ r ∂volume,
      ‖remainderKernel e he g hg hs P q r*muDensity P r*eta r‖ ≤
        (C*M*omega q)*weightedKernelDensity P r := by
    filter_upwards [hBound] with r hr
    simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (muDensity_nonneg P r)]
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_right (hF e he g hg hs P q r hP) (muDensity_nonneg P r)) hr
      (abs_nonneg (eta r))
      (mul_nonneg (mul_nonneg (mul_nonneg hC.le (omega_nonneg q)) (omega_nonneg r)) (muDensity_nonneg P r))
    simpa only [weightedKernelDensity,pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  have hi := (weightedKernelDensity_integrable P hP).const_mul (C*M*omega q)
  have hIntegrable : Integrable
      (fun r => remainderKernel e he g hg hs P q r*muDensity P r*eta r) volume :=
    hi.mono' hmeas hdom
  refine And.intro hIntegrable ?_
  have hN := norm_integral_le_of_norm_le hi hdom
  have hN' : ‖weightedEtaIntegral e he g hg hs P eta q‖ ≤
      (C*M*omega q)*(∫ r,weightedKernelDensity P r) := by
    simpa only [weightedEtaIntegral,integral_const_mul] using hN
  exact hN'.trans (by
    have h := mul_le_mul_of_nonneg_left (hI P hP) hnon
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h)

/-- The weighted input formula is an identity of raw integral representatives,
including q=0; the input is still the existing ordinary L-infinity class. -/
theorem weightedEtaIntegral_omega_mul (f : Lp ℝ ⊤ (volume : Measure GW.Space)) (q : GW.Space) :
    weightedEtaIntegral e he g hg hs P (fun r => omega r*f r) q =
      omega q*normalizedWeightedIntegral e he g hg hs P f q := by
  by_cases hq : q = 0
  · subst q
    rw [weightedEtaIntegral_zero]
    simp [omega]
  · have ho : omega q ≠ 0 := ne_of_gt (lt_min (norm_pos_iff.mpr hq) zero_lt_one)
    unfold weightedEtaIntegral normalizedWeightedIntegral
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun r => by
      simp only [normalizedWeightedKernel,ite_eq_right hq,div_eq_mul_inv]
      field_simp [ho]
      <;> ring)

end Froehlich
