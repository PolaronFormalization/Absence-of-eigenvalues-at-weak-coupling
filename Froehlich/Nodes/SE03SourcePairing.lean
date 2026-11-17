import Froehlich.Nodes.OP02SourcePairings
import Froehlich.Nodes.RS03StaticBounded
import Froehlich.Nodes.SE02

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

/-- The source functional sees exactly the one-particle projection of the true source. -/
theorem se03_ground_source_linear_pairing :
    translatedLinearSource g 0 (groundSourceOneEnergy e he g hg hs) =
      -(auxiliarySelfEnergy e 0 he g hg hs : ℂ) := by
  have hconj := (translatedLinearSource_star_integral g 0 (groundSourceOneEnergy e he g hg hs)).2
  have hload : (starRingEnd ℂ) (translatedLinearSource g 0 (groundSourceOneEnergy e he g hg hs)) =
      highFiberSourceLoad g (-(0 : GW.Space)) 1 (auxiliaryGroundSourceEnergy e 0 he g hg hs) := by
    rw [hconj]
    change _ = fiberSourceLoad g (-(0 : GW.Space))
      (auxiliaryGroundSourceEnergy e 0 he g hg hs : EnergySpace (-(0 : GW.Space)))
    rw [←groundSourceZeroEnergy_val e he g hg hs,neg_zero,fiberSourceLoad_integral]
    apply integral_congr_ae
    have hf := groundSourceOneEnergy_physical e he g hg hs
    have hz := groundSourceZeroEnergy_physical e he g hg hs
    filter_upwards [Filter.Eventually.of_forall (fun k => congrArg (fun f : GW.OnePhonon => f k) hf)] with k hk
    rw [add_zero,hk,hz]
  have hvalue : highFiberSourceLoad g (-(0 : GW.Space)) 1
      (auxiliaryGroundSourceEnergy e 0 he g hg hs) = -(auxiliarySelfEnergy e 0 he g hg hs : ℂ) := by
    rw [auxiliaryGroundSourceEnergy_bounded_pairing]
    have h := congrArg (fun z : ℂ => -z) (auxiliarySelfEnergy_bounded_complex e 0 he g hg hs)
    simpa only [neg_neg] using h.symm
  have h0 : (starRingEnd ℂ) (translatedLinearSource g 0 (groundSourceOneEnergy e he g hg hs)) =
      -(auxiliarySelfEnergy e 0 he g hg hs : ℂ) := hload.trans hvalue
  have h := congrArg (starRingEnd ℂ) h0
  rw [Complex.conj_conj,map_neg,Complex.conj_ofReal] at h
  exact h

/-- At the actual vacuum root the linear source pairing is minus the root energy. -/
theorem se03_ground_source_linear_pairing_of_anchor
    (hanchor : auxiliarySelfEnergy e 0 he g hg hs = e) :
    translatedLinearSource g 0 (groundSourceOneEnergy e he g hg hs) = -(e : ℂ) := by
  rw [se03_ground_source_linear_pairing,hanchor]

end Froehlich
