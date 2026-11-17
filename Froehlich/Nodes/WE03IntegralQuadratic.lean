import Froehlich.Nodes.WE03SecondDifference
import Froehlich.Nodes.WE03EvenSolution

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem weightedEquationEta_integral_zero_quadratic : ∃ CJ : ℝ, 0 < CJ ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2),
      ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2 → ∀ q : GW.Space,
      |weightedEtaIntegral e he g hg hs 0 (weightedEquationEta e he g hg hs hLower 0 (by simp)) q| ≤ CJ*(omega q)^2 := by
  obtain ⟨CF,hCF,hF⟩ := remainderKernel_zero_symmetricDifference_uniform
  obtain ⟨CZ,hCZ,hZ⟩ := weightedEquationSolution_norm_uniform
  obtain ⟨CI,hCI,hI⟩ := weightedKernelDensity_integral_uniform
  obtain ⟨CE,hCE,hEtaI⟩ := weightedEtaIntegral_uniform
  let A := CF*CZ*CI
  let B := CE*CZ
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro e he g hg hs hLower CD hCD hquad hSmall q
  let eta := weightedEquationEta e he g hg hs hLower 0 (by simp)
  let J := weightedEtaIntegral e he g hg hs 0 eta
  have hz := hZ e he g hg hs hLower 0 (by simp) hSmall
  have hEta : ∀ᵐ r ∂volume, |eta r| ≤ CZ*omega r := by
    filter_upwards [weightedEquationEta_bound e he g hg hs hLower 0 (by simp)] with r hr
    exact hr.trans (mul_le_mul_of_nonneg_right hz (omega_nonneg r))
  have hm : AEStronglyMeasurable eta volume :=
    weightedEquationEta_aestronglyMeasurable e he g hg hs hLower 0 (by simp)
  have hi (x : GW.Space) := hEtaI e he g hg hs 0 (by simp) CZ hCZ.le eta hm hEta x
  have hEven : J (-q) = J q :=
    weightedEquationEta_integral_zero_even e he g hg hs hLower CD hCD hquad hSmall q
  have hsum : 2*J q = ∫ r,(remainderKernel e he g hg hs 0 q r+
      remainderKernel e he g hg hs 0 (-q) r)*muDensity 0 r*eta r := by
    calc
      _ = J q+J (-q) := by rw [hEven]; ring
      _ = ∫ r,(remainderKernel e he g hg hs 0 q r*muDensity 0 r*eta r+
          remainderKernel e he g hg hs 0 (-q) r*muDensity 0 r*eta r) :=
        (integral_add (hi q).1 (hi (-q)).1).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun r => by ring))
  have hdom : ∀ᵐ r ∂volume, ‖(remainderKernel e he g hg hs 0 q r+
      remainderKernel e he g hg hs 0 (-q) r)*muDensity 0 r*eta r‖ ≤
      (CF*CZ*‖q‖^2)*weightedKernelDensity 0 r := by
    filter_upwards [hEta] with r hr
    simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (muDensity_nonneg 0 r)]
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_right (hF e he g hg hs q r) (muDensity_nonneg 0 r)) hr
      (abs_nonneg (eta r))
      (mul_nonneg (mul_nonneg (mul_nonneg hCF.le (sq_nonneg _)) (omega_nonneg r)) (muDensity_nonneg 0 r))
    simpa only [weightedKernelDensity,pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  have hNi := norm_integral_le_of_norm_le
    ((weightedKernelDensity_integrable 0 (by simp)).const_mul (CF*CZ*‖q‖^2)) hdom
  have hN : |2*J q| ≤ A*‖q‖^2 := by
    rw [←hsum] at hNi
    have hIntegral : (CF*CZ*‖q‖^2)*(∫ r,weightedKernelDensity 0 r) ≤ A*‖q‖^2 := by
      have h : (CF*CZ*‖q‖^2)*(∫ r,weightedKernelDensity 0 r) ≤
          (CF*CZ*‖q‖^2)*CI :=
        mul_le_mul_of_nonneg_left (hI 0 (by simp))
          (mul_nonneg (mul_nonneg hCF.le hCZ.le) (sq_nonneg ‖q‖))
      simpa only [A,mul_assoc,mul_comm,mul_left_comm] using h
    have hNorm : |2*J q| ≤ (CF*CZ*‖q‖^2)*(∫ r,weightedKernelDensity 0 r) := by
      simpa only [Real.norm_eq_abs,integral_const_mul] using hNi
    exact hNorm.trans hIntegral
  have hSmallQ : |J q| ≤ A*‖q‖^2 := by
    rw [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hN
    linarith [abs_nonneg (J q)]
  have hLargeQ : |J q| ≤ B := by
    have h := (hi q).2
    have h' : |J q| ≤ B*omega q := h
    exact h'.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (omega_le_one q) hB.le)
  by_cases hq : ‖q‖ ≤ 1
  · rw [omega,min_eq_left hq]
    exact hSmallQ.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) (sq_nonneg _))
  · rw [omega,min_eq_right (le_of_lt (lt_of_not_ge hq)),one_pow,mul_one]
    exact hLargeQ.trans (le_add_of_nonneg_left hA.le)

end Froehlich
