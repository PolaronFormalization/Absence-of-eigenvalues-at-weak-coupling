import Froehlich.Nodes.WE01EtaIntegral
import Froehlich.Nodes.WE01InverseMultiplier

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

/-- The source's literal division-outside-the-integral representative. -/
def weightedKernelFormula (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (P : GW.Space) (f : Lp ℝ ⊤ (volume : Measure GW.Space)) (q : GW.Space) : ℝ :=
  if q = 0 then 0 else (omega q)⁻¹*
    ∫ r, remainderKernel e he g hg hs P q r*muDensity P r*omega r*f r

theorem normalizedWeightedIntegral_eq_formula
    (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space)
    (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    normalizedWeightedIntegral e he g hg hs P f = weightedKernelFormula e he g hg hs P f := by
  funext q
  by_cases hq : q = 0
  · subst q
    simp [normalizedWeightedIntegral,normalizedWeightedKernel,weightedKernelFormula]
  · unfold normalizedWeightedIntegral weightedKernelFormula
    rw [ite_eq_right hq,←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun r => by
      simp only [normalizedWeightedKernel,ite_eq_right hq,div_eq_mul_inv]
      ring)

/-- Raw zero prescriptions are separated from the AE representatives of
operators and source vectors in the existing L-infinity quotient. -/
def WE01OperatorReference (CW e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q) : Prop :=
  (∀ (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
    ‖weightedKernelOperator e he g hg hs P hP‖ ≤ CW ∧
    (∀ f : Lp ℝ ⊤ (volume : Measure GW.Space),
      weightedKernelOperator e he g hg hs P hP f =ᵐ[volume]
        weightedKernelFormula e he g hg hs P f) ∧
    (∀ f : Lp ℝ ⊤ (volume : Measure GW.Space), weightedKernelFormula e he g hg hs P f 0 = 0) ∧
    ‖weightedKernelSource e he g hg hs P hP‖ ≤ CW ∧
    (weightedKernelSource e he g hg hs P hP =ᵐ[volume] normalizedKernelPsi e he g hg hs P) ∧
    normalizedKernelPsi e he g hg hs P 0 = 0) ∧
  ‖thresholdInverseLinftyMultiplier e he g hg hs hLower‖ ≤ (4/3 : ℝ) ∧
  ∀ f : Lp ℝ ⊤ (volume : Measure GW.Space),
    thresholdInverseLinftyMultiplier e he g hg hs hLower f =ᵐ[volume]
      (fun q => (thresholdDiagonalMultiplier e he g hg hs q)⁻¹*f q)

private theorem we01_operator_uniform : ∃ CW : ℝ, 0 < CW ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q),
      WE01OperatorReference CW e he g hg hs hLower := by
  obtain ⟨A,hA,hOp⟩ := weightedKernelOperator_norm_uniform
  obtain ⟨B,hB,hSource⟩ := weightedKernelSource_norm_uniform
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro e he g hg hs hLower
  constructor
  · intro P hP
    refine ⟨(hOp e he g hg hs P hP).trans (le_add_of_nonneg_right hB.le),?_,?_,
      (hSource e he g hg hs P hP).trans (le_add_of_nonneg_left hA.le),
      weightedKernelSource_ae e he g hg hs P hP,normalizedKernelPsi_zero e he g hg hs P⟩
    · intro f
      rw [←normalizedWeightedIntegral_eq_formula e he g hg hs P f]
      exact weightedKernelOperator_ae e he g hg hs P hP f
    · intro f
      simp [weightedKernelFormula]
  · exact ⟨thresholdInverseLinftyMultiplier_norm_le e he g hg hs hLower,
      thresholdInverseLinftyMultiplier_ae e he g hg hs hLower⟩

/-- Full WE01 coverage, including the source's unnormalized eta notation. -/
def WE01FixedReference (CW e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q) : Prop :=
  WE01OperatorReference CW e he g hg hs hLower ∧
  (∀ (P : GW.Space), ‖P‖ ≤ 1/4 → ∀ (M : ℝ), 0 ≤ M → ∀ eta : GW.Space → ℝ,
    AEStronglyMeasurable eta volume → (∀ᵐ r ∂volume, |eta r| ≤ M*omega r) → ∀ q,
    Integrable (fun r => remainderKernel e he g hg hs P q r*muDensity P r*eta r) volume ∧
      ‖weightedEtaIntegral e he g hg hs P eta q‖ ≤ CW*M*omega q) ∧
  (∀ (P : GW.Space) (eta : GW.Space → ℝ), weightedEtaIntegral e he g hg hs P eta 0 = 0) ∧
  ∀ (P : GW.Space) (f : Lp ℝ ⊤ (volume : Measure GW.Space)) (q : GW.Space),
    weightedEtaIntegral e he g hg hs P (fun r => omega r*f r) q =
      omega q*weightedKernelFormula e he g hg hs P f q

theorem finalWE01_uniform : ∃ CW : ℝ, 0 < CW ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (hLower : ∀ q : GW.Space, 3/4 ≤ thresholdDiagonalMultiplier e he g hg hs q),
      WE01FixedReference CW e he g hg hs hLower := by
  obtain ⟨A,hA,hOp⟩ := we01_operator_uniform
  obtain ⟨B,hB,hEta⟩ := weightedEtaIntegral_uniform
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro e he g hg hs hLower
  have hOld := hOp e he g hg hs hLower
  refine ⟨?_,?_,?_,?_⟩
  · constructor
    · intro P hP
      rcases hOld.1 P hP with ⟨hn,ha,hz,hchi,hca,hcz⟩
      exact ⟨hn.trans (le_add_of_nonneg_right hB.le),ha,hz,
        hchi.trans (le_add_of_nonneg_right hB.le),hca,hcz⟩
    · exact hOld.2
  · intro P hP M hM eta hm hb q
    rcases hEta e he g hg hs P hP M hM eta hm hb q with ⟨hi,hn⟩
    exact ⟨hi,hn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) hM) (omega_nonneg q))⟩
  · exact weightedEtaIntegral_zero e he g hg hs
  · intro P f q
    rw [←normalizedWeightedIntegral_eq_formula e he g hg hs P f]
    exact weightedEtaIntegral_omega_mul e he g hg hs P f q

/-- WE01 at the actual zero-momentum ground energy. The multiplier lower
bound is an internally constructed output, not a desired operator premise. -/
theorem finalWE01 : ∃ CW s : ℝ, 0 < CW ∧ 0 < s ∧
    ∀ g : ℝ, |g| < s →
      ∃ he : groundEnergy (fiberHamiltonian g 0) ∈ Set.Icc (-1/4 : ℝ) 0,
      ∃ hg : |g| ≤ 1, ∃ hs : auxiliaryResolventConstant*|g| ≤ 1/2,
      ∃ hLower : ∀ q : GW.Space, 3/4 ≤
        thresholdDiagonalMultiplier (groundEnergy (fiberHamiltonian g 0)) he g hg hs q,
      WE01FixedReference CW (groundEnergy (fiberHamiltonian g 0)) he g hg hs hLower := by
  obtain ⟨CW,hCW,hW⟩ := finalWE01_uniform
  obtain ⟨s,hs,hGround⟩ := thresholdInverseLinftyMultiplier_ground
  refine ⟨CW,s,hCW,hs,?_⟩
  intro g hgs
  obtain ⟨he,hg,haux,hLower,hNorm⟩ := hGround g hgs
  exact ⟨he,hg,haux,hLower,hW _ he g hg haux hLower⟩

end Froehlich
