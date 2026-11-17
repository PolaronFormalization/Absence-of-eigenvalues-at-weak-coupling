import Froehlich.Nodes.WE04

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- The specific scalar numerator has the source's Lipschitz and cubic-weight bounds. -/
theorem we06_psi_eta_product_difference_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2),
      ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2 →
      ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2 →
      ∀ᵐ q ∂volume,
        |kernelPsi e he g hg hs P q*weightedEquationEta e he g hg hs hLower P hP q-
          kernelPsi e he g hg hs 0 q*weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤
            C*‖P‖*(omega q)^2 ∧
        |kernelPsi e he g hg hs 0 q*weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ C*(omega q)^3 := by
  obtain ⟨A,hA,hPsiDiff⟩ := kernelMomentumDifferences_uniform
  obtain ⟨B,hB,hPsi0⟩ := kernelPsi_zero_quadratic_uniform
  obtain ⟨Z,hZ,hNorm⟩ := weightedEquationSolution_norm_uniform
  obtain ⟨D,hD,hDiff⟩ := weightedEquationEta_comparison_uniform
  obtain ⟨E,hE,hQuad⟩ := weightedEquationEta_zero_quadratic_uniform
  let C := A*Z+B*D+B*E+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro e he g hg hs hLower CD hCD hquad hSmall0 P hP hSmallP
  have hPnorm := hNorm e he g hg hs hLower P hP hSmallP
  have hEta0 := (hQuad e he g hg hs hLower CD hCD hquad hSmall0).2
  have hEtaDiff := hDiff e he g hg hs hLower CD hCD hquad hSmall0 P hP hSmallP
  filter_upwards [weightedEquationEta_bound e he g hg hs hLower P hP,hEta0,hEtaDiff]
    with q hEtaP hEta0 hEtaDiff
  let p := kernelPsi e he g hg hs P q
  let p0 := kernelPsi e he g hg hs 0 q
  let v := weightedEquationEta e he g hg hs hLower P hP q
  let v0 := weightedEquationEta e he g hg hs hLower 0 (by simp) q
  have hw : 0 ≤ omega q := omega_nonneg q
  have hw1 : omega q ≤ 1 := omega_le_one q
  have hw2 : (omega q)^2 ≤ omega q := by nlinarith
  have hp0 : |p0| ≤ B*omega q := (hPsi0 e he g hg hs q).trans
    (mul_le_mul_of_nonneg_left hw2 hB.le)
  have hv : |v| ≤ Z*omega q := hEtaP.trans (mul_le_mul_of_nonneg_right hPnorm hw)
  have h1 : |(p-p0)*v| ≤ (A*Z)*‖P‖*(omega q)^2 := by
    rw [abs_mul]
    have h := mul_le_mul ((hPsiDiff e he g hg hs P hP).1 q) hv (abs_nonneg v)
      (mul_nonneg (mul_nonneg hA.le (norm_nonneg P)) hw)
    simpa only [p,p0,v,pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  have h2 : |p0*(v-v0)| ≤ (B*D)*‖P‖*(omega q)^2 := by
    rw [abs_mul]
    have h := mul_le_mul hp0 hEtaDiff.1 (abs_nonneg (v-v0)) (mul_nonneg hB.le hw)
    simpa only [p0,v,v0,pow_two,mul_assoc,mul_comm,mul_left_comm] using h
  have hNumerator : |p*v-p0*v0| ≤ (A*Z+B*D)*‖P‖*(omega q)^2 := by
    have heq : p*v-p0*v0 = (p-p0)*v+p0*(v-v0) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hBase : |p0*v0| ≤ (B*E)*(omega q)^4 := by
    rw [abs_mul]
    have h := mul_le_mul (hPsi0 e he g hg hs q) hEta0 (abs_nonneg v0)
      (mul_nonneg hB.le (sq_nonneg _))
    simpa only [p0,v0,pow_two,pow_succ,pow_one,pow_zero,one_mul,mul_one,mul_assoc,mul_comm,mul_left_comm] using h
  have hw4 : (omega q)^4 ≤ (omega q)^3 := by
    simpa only [pow_succ,mul_one] using mul_le_mul_of_nonneg_left hw1 (pow_nonneg hw 3)
  have hAC : A*Z+B*D ≤ C := by dsimp [C]; nlinarith [mul_pos hB hE]
  have hBC : B*E ≤ C := by dsimp [C]; nlinarith [mul_pos hA hZ,mul_pos hB hD]
  exact ⟨hNumerator.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAC (norm_nonneg P)) (sq_nonneg _)),
    (hBase.trans (mul_le_mul_of_nonneg_left hw4 (mul_pos hB hE).le)).trans
      (mul_le_mul_of_nonneg_right hBC (pow_nonneg hw 3))⟩

end Froehlich
