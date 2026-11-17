import Froehlich.Nodes.WE01IntegralRows

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem linftyReal_norm_le_of_ae_bound (f : Lp ℝ ⊤ (volume : Measure GW.Space))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ q ∂volume, ‖f q‖ ≤ B) : ‖f‖ ≤ B := by
  have h : eLpNorm f ⊤ volume ≤ ENNReal.ofReal B := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
    exact eLpNormEssSup_le_of_ae_bound hb
  simpa only [Lp.norm_def,ENNReal.toReal_ofReal hB] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ q r, ‖normalizedWeightedKernel e he g hg hs P q r‖ ≤ C*weightedKernelDensity P r)

include hP hC hK in
theorem normalizedWeightedIntegral_memLp (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    MemLp (normalizedWeightedIntegral e he g hg hs P f) ⊤ volume := by
  apply memLp_top_of_bound (normalizedWeightedIntegral_aestronglyMeasurable e he g hg hs P f)
    ((C*(∫ r,weightedKernelDensity P r))*‖f‖)
  exact Eventually.of_forall (normalizedWeightedIntegral_norm_le e he g hg hs P hP C hC hK f)

def weightedLinftyValue (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    Lp ℝ ⊤ (volume : Measure GW.Space) :=
  (normalizedWeightedIntegral_memLp e he g hg hs P hP C hC hK f).toLp
    (normalizedWeightedIntegral e he g hg hs P f)

theorem weightedLinftyValue_ae (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedLinftyValue e he g hg hs P hP C hC hK f =ᵐ[volume]
      normalizedWeightedIntegral e he g hg hs P f := MemLp.coeFn_toLp _

include hP hC hK in
theorem normalizedWeightedIntegral_add (f z : Lp ℝ ⊤ (volume : Measure GW.Space)) (q : GW.Space) :
    normalizedWeightedIntegral e he g hg hs P (f+z) q =
      normalizedWeightedIntegral e he g hg hs P f q+normalizedWeightedIntegral e he g hg hs P z q := by
  unfold normalizedWeightedIntegral
  calc
    _ = ∫ r, (normalizedWeightedKernel e he g hg hs P q r*f r+
        normalizedWeightedKernel e he g hg hs P q r*z r) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f z] with r hr
      rw [hr,Pi.add_apply,mul_add]
    _ = _ := integral_add
      (normalizedWeightedIntegral_integrable e he g hg hs P hP C hC hK f q)
      (normalizedWeightedIntegral_integrable e he g hg hs P hP C hC hK z q)

theorem normalizedWeightedIntegral_smul (a : ℝ) (f : Lp ℝ ⊤ (volume : Measure GW.Space)) (q : GW.Space) :
    normalizedWeightedIntegral e he g hg hs P (a • f) q =
      a*normalizedWeightedIntegral e he g hg hs P f q := by
  unfold normalizedWeightedIntegral
  calc
    _ = ∫ r, a*(normalizedWeightedKernel e he g hg hs P q r*f r) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul a f] with r hr
      rw [hr,Pi.smul_apply,smul_eq_mul]
      ring
    _ = _ := integral_const_mul _ _

private def weightedLinftyLinearMap :
    Lp ℝ ⊤ (volume : Measure GW.Space) →ₗ[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) where
  toFun := weightedLinftyValue e he g hg hs P hP C hC hK
  map_add' f z := by
    apply Lp.ext
    filter_upwards [weightedLinftyValue_ae e he g hg hs P hP C hC hK (f+z),
      weightedLinftyValue_ae e he g hg hs P hP C hC hK f,
      weightedLinftyValue_ae e he g hg hs P hP C hC hK z,
      Lp.coeFn_add (weightedLinftyValue e he g hg hs P hP C hC hK f)
        (weightedLinftyValue e he g hg hs P hP C hC hK z)] with q hsum hf hz hout
    rw [hsum,hout,Pi.add_apply,hf,hz]
    exact normalizedWeightedIntegral_add e he g hg hs P hP C hC hK f z q
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [weightedLinftyValue_ae e he g hg hs P hP C hC hK (a • f),
      weightedLinftyValue_ae e he g hg hs P hP C hC hK f,
      Lp.coeFn_smul a (weightedLinftyValue e he g hg hs P hP C hC hK f)] with q hin hf hout
    simp only [RingHom.id_apply]
    rw [hin,hout,Pi.smul_apply,hf,smul_eq_mul]
    exact normalizedWeightedIntegral_smul e he g hg hs P a f q

private theorem weightedLinftyValue_bound (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    ‖weightedLinftyValue e he g hg hs P hP C hC hK f‖ ≤
      (C*(∫ r,weightedKernelDensity P r))*‖f‖ := by
  apply linftyReal_norm_le_of_ae_bound _ _
    (mul_nonneg (mul_nonneg hC (integral_nonneg (weightedKernelDensity_nonnegative P))) (norm_nonneg f))
  filter_upwards [weightedLinftyValue_ae e he g hg hs P hP C hC hK f] with q hq
  rw [hq]
  exact normalizedWeightedIntegral_norm_le e he g hg hs P hP C hC hK f q

/-- A genuine bounded real-linear map on the existing ordinary L-infinity quotient. -/
def weightedLinftyOperator :
    Lp ℝ ⊤ (volume : Measure GW.Space) →L[ℝ] Lp ℝ ⊤ (volume : Measure GW.Space) :=
  (weightedLinftyLinearMap e he g hg hs P hP C hC hK).mkContinuous
    (C*(∫ r,weightedKernelDensity P r)) (weightedLinftyValue_bound e he g hg hs P hP C hC hK)

theorem weightedLinftyOperator_ae (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    weightedLinftyOperator e he g hg hs P hP C hC hK f =ᵐ[volume]
      normalizedWeightedIntegral e he g hg hs P f := weightedLinftyValue_ae e he g hg hs P hP C hC hK f

theorem weightedLinftyOperator_norm_le :
    ‖weightedLinftyOperator e he g hg hs P hP C hC hK‖ ≤ C*(∫ r,weightedKernelDensity P r) :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg hC (integral_nonneg (weightedKernelDensity_nonnegative P))) _

theorem normalizedWeightedIntegral_zero (f : Lp ℝ ⊤ (volume : Measure GW.Space)) :
    normalizedWeightedIntegral e he g hg hs P f 0 = 0 := by
  simp [normalizedWeightedIntegral,normalizedWeightedKernel]

end Froehlich
