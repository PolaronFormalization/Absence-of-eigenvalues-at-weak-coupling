import Froehlich.Nodes.WE03

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- The source comparison is on a fixed better-vanishing input, not an
operator-norm estimate on the whole L-infinity space. -/
theorem weightedEtaIntegral_difference_domination : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space), ‖P‖ ≤ 1/4 →
      ∀ (M : ℝ), 0 ≤ M → ∀ eta : GW.Space → ℝ,
      (∀ᵐ r ∂volume, |eta r| ≤ M*(omega r)^2) → ∀ q : GW.Space,
      ∀ᵐ r ∂volume,
      ‖(remainderKernel e he g hg hs P q r*muDensity P r-
          remainderKernel e he g hg hs 0 q r*muDensity 0 r)*eta r‖ ≤
        C*M*omega q*(‖P‖*((omega r)^3*muDensity P r)+weightedMuDifference P r) := by
  obtain ⟨A,hA,hDiff⟩ := kernelMomentumDifferences_uniform
  obtain ⟨B,hB,hBase⟩ := remainderKernel_uniform_bound
  let C := A+B
  have hC : 0 < C := add_pos hA hB
  refine ⟨C,hC,?_⟩
  intro e he g hg hs P hP M hM eta hEta q
  filter_upwards [hEta] with r hr
  have hD : |remainderKernel e he g hg hs P q r-remainderKernel e he g hg hs 0 q r| ≤
      C*‖P‖*omega q*omega r :=
    ((hDiff e he g hg hs P hP).2 q r).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) (norm_nonneg P)) (omega_nonneg q)) (omega_nonneg r))
  have hF : |remainderKernel e he g hg hs 0 q r| ≤ C*omega q*omega r :=
    (hBase e he g hg hs 0 q r (by simp)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hA.le) (omega_nonneg q)) (omega_nonneg r))
  have hSplit : (remainderKernel e he g hg hs P q r*muDensity P r-
      remainderKernel e he g hg hs 0 q r*muDensity 0 r)*eta r =
      (remainderKernel e he g hg hs P q r-remainderKernel e he g hg hs 0 q r)*muDensity P r*eta r+
      remainderKernel e he g hg hs 0 q r*(muDensity P r-muDensity 0 r)*eta r := by ring
  rw [hSplit,Real.norm_eq_abs]
  have h1 : |(remainderKernel e he g hg hs P q r-remainderKernel e he g hg hs 0 q r)*muDensity P r*eta r| ≤
      C*M*omega q*‖P‖*((omega r)^3*muDensity P r) := by
    rw [abs_mul,abs_mul,abs_of_nonneg (muDensity_nonneg P r)]
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hD (muDensity_nonneg P r)) hr
      (abs_nonneg (eta r))
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le (norm_nonneg P)) (omega_nonneg q)) (omega_nonneg r)) (muDensity_nonneg P r))
    simpa only [pow_succ,pow_two,pow_one,pow_zero,one_mul,mul_assoc,mul_comm,mul_left_comm] using h
  have h2 : |remainderKernel e he g hg hs 0 q r*(muDensity P r-muDensity 0 r)*eta r| ≤
      C*M*omega q*weightedMuDifference P r := by
    rw [abs_mul,abs_mul]
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hF (abs_nonneg (muDensity P r-muDensity 0 r))) hr
      (abs_nonneg (eta r))
      (mul_nonneg (mul_nonneg (mul_nonneg hC.le (omega_nonneg q)) (omega_nonneg r)) (abs_nonneg (muDensity P r-muDensity 0 r)))
    simpa only [weightedMuDifference,pow_succ,pow_two,pow_one,pow_zero,one_mul,mul_assoc,mul_comm,mul_left_comm] using h
  exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end Froehlich
