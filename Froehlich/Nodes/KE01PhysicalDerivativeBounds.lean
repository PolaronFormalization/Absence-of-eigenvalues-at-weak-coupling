import Froehlich.Nodes.KE01CDerivativeBounds
import Froehlich.Nodes.KE01CanonicalNormChart
import Froehlich.Nodes.KE01CanonicalNormLocalChain

set_option autoImplicit false
noncomputable section
namespace Froehlich

theorem thresholdKernelC_product_iterated_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (k : ℕ) (hk : k ≤ 3)
      (t : GW.Space × (GW.Space × GW.Space)), ‖t.1‖ ≤ 1/4 →
      ‖iteratedFDeriv ℝ k (fun u : GW.Space × (GW.Space × GW.Space) =>
        thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2) t‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := thresholdKernelC_iterated_uniform
  let L := kernelJointCoordinateInverse
  let A := (1+‖L‖)^3
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C*A,by positivity,?_⟩
  intro e he g hg hs k hk t ht
  have hcoverage : kernelJointCoordinates (L t) = t := kernelJointCoordinates_rightInverse t
  have hP : kernelCoordinateBlock 0 (L t) = t.1 := congrArg Prod.fst hcoverage
  have hx : ‖kernelCoordinateBlock 0 (L t)‖ ≤ 1/4 := by rw [hP]; exact ht
  have hAt : ContDiffAt ℝ k (thresholdKernelCCoordinates e he g hg hs) (L t) :=
    (thresholdKernelCCoordinates_contDiffAt_closedBall e he g hg hs (L t) hx).of_le (by exact_mod_cast hk)
  have hN := iteratedFDeriv_comp_linear_norm_le_at L (thresholdKernelCCoordinates e he g hg hs) k t hAt
  have hpow : ‖L‖^k ≤ A := by
    dsimp [A]
    interval_cases k <;> norm_num <;>
      nlinarith [norm_nonneg L,sq_nonneg ‖L‖,pow_nonneg (norm_nonneg L) 3]
  have hN' : ‖iteratedFDeriv ℝ k ((thresholdKernelCCoordinates e he g hg hs) ∘ L) t‖ ≤ C*A :=
    hN.trans (mul_le_mul (hB e he g hg hs k hk (L t) hx) hpow
      (pow_nonneg (norm_nonneg L) k) hC.le)
  have hfun : (thresholdKernelCCoordinates e he g hg hs) ∘ L =
      (fun u : GW.Space × (GW.Space × GW.Space) => thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2) := by
    funext u
    have h := congrArg (fun z : GW.Space × (GW.Space × GW.Space) =>
      thresholdKernelC e he g hg hs z.1 z.2.1 z.2.2) (kernelJointCoordinates_rightInverse u)
    simpa only [Function.comp_def,thresholdKernelCCoordinates,kernelJointCoordinates_apply,L] using! h
  simpa only [hfun] using! hN'

/-- Explicit coverage of every actual momentum triple by the canonical
nine-coordinate derivative endpoint. -/
theorem thresholdKernelC_physical_multiPartial_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (alpha : Fin 9 → ℕ)
      (ha : (∑ i,alpha i) ≤ 3) (P q r : GW.Space), ‖P‖ ≤ 1/4 →
      ‖coordinateMultiPartial alpha (thresholdKernelCCoordinates e he g hg hs)
        (kernelCoordinatesFor P q r)‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := thresholdKernelC_multiPartial_uniform
  refine ⟨C,hC,?_⟩
  intro e he g hg hs alpha ha P q r hP
  apply hB e he g hg hs alpha ha
  have h := congrArg Prod.fst (kernelJointCoordinates_coordinatesFor P q r)
  change kernelCoordinateBlock 0 (kernelCoordinatesFor P q r) = P at h
  rw [h]
  exact hP

end Froehlich
