import Froehlich.Nodes.WE04SpecificDomination

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- Uniform comparison only on the fixed quadratic-vanishing input. -/
theorem weightedEtaIntegral_difference_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space), ‖P‖ ≤ 1/4 →
      ∀ (M : ℝ), 0 ≤ M → ∀ eta : GW.Space → ℝ,
      AEStronglyMeasurable eta volume → (∀ᵐ r ∂volume, |eta r| ≤ M*(omega r)^2) → ∀ q : GW.Space,
      |weightedEtaIntegral e he g hg hs P eta q-weightedEtaIntegral e he g hg hs 0 eta q| ≤
        C*M*‖P‖*omega q := by
  obtain ⟨CK,hCK,hK⟩ := weightedEtaIntegral_difference_domination
  obtain ⟨CI,hCI,hMom⟩ := omega_moments_uniform
  obtain ⟨CD,hCD,hMoving,hUnused⟩ := moving_singularity_estimates
  obtain ⟨CE,hCE,hRows⟩ := weightedEtaIntegral_uniform
  refine ⟨CK*(CI+CD),by positivity,?_⟩
  intro e he g hg hs P hP M hM eta hEta hQuad q
  have hLinear : ∀ᵐ r ∂volume, |eta r| ≤ M*omega r := by
    filter_upwards [hQuad] with r hr
    have hw : (omega r)^2 ≤ omega r := by nlinarith [omega_nonneg r,omega_le_one r]
    exact hr.trans (mul_le_mul_of_nonneg_left hw hM)
  have hiP := (hRows e he g hg hs P hP M hM eta hEta hLinear q).1
  have hi0 := (hRows e he g hg hs 0 (by simp) M hM eta hEta hLinear q).1
  let D : GW.Space → ℝ := fun r => ‖P‖*((omega r)^3*muDensity P r)+weightedMuDifference P r
  have hiD : Integrable D volume :=
    (((hMom P hP).2.1).const_mul ‖P‖).add (hMoving P hP).2.1
  have hID : (∫ r,D r) ≤ (CI+CD)*‖P‖ := by
    have heq : (∫ r,D r) = ‖P‖*(∫ r,(omega r)^3*muDensity P r)+(∫ r,weightedMuDifference P r) := by
      have hAdd := integral_add (((hMom P hP).2.1).const_mul ‖P‖) (hMoving P hP).2.1
      simpa only [D,Pi.add_def,integral_const_mul] using! hAdd
    rw [heq]
    have h := add_le_add (mul_le_mul_of_nonneg_left (hMom P hP).2.2 (norm_nonneg P))
      (hMoving P hP).2.2
    exact h.trans_eq (by ring)
  have hEq : weightedEtaIntegral e he g hg hs P eta q-weightedEtaIntegral e he g hg hs 0 eta q =
      ∫ r,(remainderKernel e he g hg hs P q r*muDensity P r-
        remainderKernel e he g hg hs 0 q r*muDensity 0 r)*eta r := by
    unfold weightedEtaIntegral
    rw [←integral_sub hiP hi0]
    exact integral_congr_ae (Eventually.of_forall (fun r => by ring))
  have hN := norm_integral_le_of_norm_le (hiD.const_mul (CK*M*omega q))
    (hK e he g hg hs P hP M hM eta hQuad q)
  have hN' : |weightedEtaIntegral e he g hg hs P eta q-weightedEtaIntegral e he g hg hs 0 eta q| ≤
      (CK*M*omega q)*(∫ r,D r) := by
    rw [hEq]
    simpa only [Real.norm_eq_abs,integral_const_mul,D] using hN
  exact hN'.trans (by
    have h := mul_le_mul_of_nonneg_left hID
      (mul_nonneg (mul_nonneg hCK.le hM) (omega_nonneg q))
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h)

end Froehlich
