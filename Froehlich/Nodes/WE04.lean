import Froehlich.Nodes.WE04Comparison

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem weightedEquationEta_comparison_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q)
      (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2),
      ‖weightedEquationPerturbation e he g hg hs hLower 0 (by simp)‖ ≤ 1/2 →
      ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖weightedEquationPerturbation e he g hg hs hLower P hP‖ ≤ 1/2 →
      ∀ᵐ q ∂volume,
      |weightedEquationEta e he g hg hs hLower P hP q-
        weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ C*‖P‖*omega q ∧
      |weightedEquationEta e he g hg hs hLower P hP q| ≤ C*omega q*(omega q+‖P‖) := by
  obtain ⟨CN,hCN,hN⟩ := weightedEquationSolution_comparison_uniform
  obtain ⟨CE,hCE,hE⟩ := weightedEquationEta_zero_quadratic_uniform
  let C := CN+CE
  have hC : 0 < C := add_pos hCN hCE
  have hNC : CN ≤ C := le_add_of_nonneg_right hCE.le
  have hEC : CE ≤ C := le_add_of_nonneg_left hCN.le
  refine ⟨C,hC,?_⟩
  intro e he g hg hs hLower CD hCD hquad hSmall0 P hP hSmallP
  let zP := weightedEquationSolution e he g hg hs hLower P hP
  let z0 := weightedEquationSolution e he g hg hs hLower 0 (by simp)
  have hNorm : ‖zP-z0‖ ≤ CN*‖P‖ := hN e he g hg hs hLower CD hCD hquad hSmall0 P hP hSmallP
  have hQuad := (hE e he g hg hs hLower CD hCD hquad hSmall0).2
  filter_upwards [linftyReal_ae_norm_le (zP-z0),Lp.coeFn_sub zP z0,hQuad] with q hnorm hsub hquadq
  have hDiff : |weightedEquationEta e he g hg hs hLower P hP q-
      weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ C*‖P‖*omega q := by
    have hScalar : |zP q-z0 q| ≤ CN*‖P‖ := by
      rw [hsub,Pi.sub_apply,Real.norm_eq_abs] at hnorm
      exact hnorm.trans hNorm
    calc
      _ = omega q*|zP q-z0 q| := by
        rw [weightedEquationEta,weightedEquationEta,←mul_sub,abs_mul,abs_of_nonneg (omega_nonneg q)]
      _ ≤ omega q*(CN*‖P‖) := mul_le_mul_of_nonneg_left hScalar (omega_nonneg q)
      _ ≤ C*‖P‖*omega q := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNC (norm_nonneg P)) (omega_nonneg q)
        simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  refine ⟨hDiff,?_⟩
  have hQ : |weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ C*(omega q)^2 :=
    hquadq.trans (mul_le_mul_of_nonneg_right hEC (sq_nonneg _))
  have htri := abs_add_le (weightedEquationEta e he g hg hs hLower P hP q-
    weightedEquationEta e he g hg hs hLower 0 (by simp) q)
    (weightedEquationEta e he g hg hs hLower 0 (by simp) q)
  simp only [sub_add_cancel] at htri
  exact htri.trans ((add_le_add hDiff hQ).trans_eq (by ring))

/-- The source WE04 inequalities for the actual weighted solutions. -/
def WE04FixedReference (C e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q) : Prop :=
  ∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4), ∀ᵐ q ∂volume,
    |weightedEquationEta e he g hg hs hLower P hP q-
      weightedEquationEta e he g hg hs hLower 0 (by simp) q| ≤ C*‖P‖*omega q ∧
    |weightedEquationEta e he g hg hs hLower P hP q| ≤ C*omega q*(omega q+‖P‖)

theorem finalWE04 : ∃ C CD s : ℝ, 0 < C ∧ 0 < CD ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hCD : 0 ≤ CD,
      ∃ hquad : ∀ q : GW.Space,
        |auxiliarySelfEnergy (groundEnergy (fiberHamiltonian g 0)) q he g hg hs-groundEnergy (fiberHamiltonian g 0)| ≤ CD*g^2*‖q‖^2,
      ∃ hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
      WE04FixedReference C (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower := by
  obtain ⟨C,hC,hCompare⟩ := weightedEquationEta_comparison_uniform
  obtain ⟨CZ,CD,s,hCZ,hCD,hs,hGround⟩ := weightedEquation_ground_smallness
  refine ⟨C,CD,s,hC,hCD,hs,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hCD0,hquad,hLower,hControl⟩ := hGround g hgs
  refine ⟨he,hg,haux,hCD0,hquad,hLower,?_⟩
  intro P hP
  exact hCompare _ he g hg haux hLower CD hCD0 hquad (hControl 0 (by simp)).1 P hP (hControl P hP).1

end Froehlich
