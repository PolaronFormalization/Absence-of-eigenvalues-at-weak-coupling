import Froehlich.Nodes.OP01KernelSymmetries
import Froehlich.Nodes.OP01DiagonalSymmetry

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ C*g^2*‖q‖^2)
    (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

/-- The literal OP01 operator on the existing physical one-particle space. -/
def thresholdBoundedOperator : GW.OnePhonon →L[ℂ] GW.OnePhonon :=
  thresholdDiagonalOperator e he g hg hs C hC hquad+
    ((g^2 : ℝ) : ℂ) • thresholdIntegralOperator e he g hg hs P hP

theorem thresholdBoundedOperator_ae (f : GW.OnePhonon) :
    thresholdBoundedOperator e he g hg hs C hC hquad P hP f =ᵐ[volume]
      (fun q => (thresholdDiagonalMultiplier e he g hg hs q : ℂ)*f q+
        ((g^2 : ℝ) : ℂ)*(∫ r, boundedThresholdKernel e he g hg hs P q r*f r)) := by
  let D := thresholdDiagonalOperator e he g hg hs C hC hquad
  let K := thresholdIntegralOperator e he g hg hs P hP
  filter_upwards [Lp.coeFn_add (D f) (((g^2 : ℝ) : ℂ) • K f),
    Lp.coeFn_smul ((g^2 : ℝ) : ℂ) (K f),
    thresholdDiagonalOperator_ae e he g hg hs C hC hquad f,
    thresholdIntegralOperator_ae e he g hg hs P hP f] with q hadd hsmul hd hk
  change (D f+((g^2 : ℝ) : ℂ) • K f) q = _
  rw [hadd,Pi.add_apply,hsmul,Pi.smul_apply,hd,hk] <;> rfl

theorem thresholdBoundedOperator_selfadjoint :
    (thresholdBoundedOperator e he g hg hs C hC hquad P hP).adjoint =
      thresholdBoundedOperator e he g hg hs C hC hquad P hP := by
  simp only [thresholdBoundedOperator,map_add,map_smulₛₗ,Complex.conj_ofReal,
    thresholdDiagonalOperator_selfadjoint,thresholdIntegralOperator_selfadjoint]

theorem thresholdBoundedOperator_conjugation (f : GW.OnePhonon) :
    thresholdBoundedOperator e he g hg hs C hC hquad P hP (conjugateOnePhonon f) =
      conjugateOnePhonon (thresholdBoundedOperator e he g hg hs C hC hquad P hP f) := by
  let J : GW.OnePhonon →L[ℝ] GW.OnePhonon := Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume
  let D := thresholdDiagonalOperator e he g hg hs C hC hquad
  let K := thresholdIntegralOperator e he g hg hs P hP
  have hd : D (J f) = J (D f) := thresholdDiagonalOperator_conjugation e he g hg hs C hC hquad f
  have hk : K (J f) = J (K f) := thresholdIntegralOperator_conjugation e he g hg hs P hP f
  have hreal (a : ℝ) (u : GW.OnePhonon) :
      conjugateOnePhonon ((a : ℂ) • u) = (a : ℂ) • conjugateOnePhonon u := by
    apply Lp.ext
    filter_upwards [conjugateOnePhonon_ae ((a : ℂ) • u),Lp.coeFn_smul (a : ℂ) u,
      conjugateOnePhonon_ae u,Lp.coeFn_smul (a : ℂ) (conjugateOnePhonon u)] with q hc hs hu ht
    rw [hc,hs,Pi.smul_apply,ht,Pi.smul_apply,hu]
    change (starRingEnd ℂ) ((a : ℂ)*u q) = (a : ℂ)*(starRingEnd ℂ) (u q)
    rw [map_mul,Complex.conj_ofReal]
  have hsmul (u : GW.OnePhonon) : J (((g^2 : ℝ) : ℂ) • u) = ((g^2 : ℝ) : ℂ) • J u :=
    hreal (g^2) u
  change D (J f)+((g^2 : ℝ) : ℂ) • K (J f) = J (D f+((g^2 : ℝ) : ℂ) • K f)
  rw [hd,hk,map_add,hsmul]

theorem thresholdBoundedOperator_distance_uniform : ∃ CK : ℝ, 0 < CK ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
      (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
      (P : GW.Space) (hP : ‖P‖ ≤ 1/4),
      ‖thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1‖ ≤ (CD+CK)*g^2 := by
  obtain ⟨CK,hCK,hK⟩ := thresholdIntegralOperator_norm_uniform
  refine ⟨CK,hCK,?_⟩
  intro e he g hg hs CD hCD hquad P hP
  let D := thresholdDiagonalOperator e he g hg hs CD hCD hquad
  let K := thresholdIntegralOperator e he g hg hs P hP
  have hD : ‖D-1‖ ≤ CD*g^2 := thresholdDiagonalOperator_sub_id_norm e he g hg hs CD hCD hquad
  have hEq : thresholdBoundedOperator e he g hg hs CD hCD hquad P hP-1 =
      (D-1)+((g^2 : ℝ) : ℂ) • K := by
    change (D+((g^2 : ℝ) : ℂ) • K)-1 = _
    abel
  rw [hEq]
  calc
    _ ≤ ‖D-1‖+‖((g^2 : ℝ) : ℂ) • K‖ := norm_add_le _ _
    _ = ‖D-1‖+g^2*‖K‖ := by
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg g)]
    _ ≤ CD*g^2+g^2*CK := add_le_add hD
      (mul_le_mul_of_nonneg_left (hK e he g hg hs P hP) (sq_nonneg g))
    _ = _ := by ring

end Froehlich
