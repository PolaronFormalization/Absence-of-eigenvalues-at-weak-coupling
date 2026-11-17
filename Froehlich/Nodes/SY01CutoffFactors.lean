import Froehlich.Nodes.SY01Annihilation
import Froehlich.Nodes.GW05

/-! Reality and evenness of the actual signed closed-cutoff L² classes. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich

theorem cutoffFormFactor_even (g Λ : ℝ) (k : GW.Space) :
    cutoffFormFactor g Λ (-k) = cutoffFormFactor g Λ k := by
  simp only [cutoffFormFactor, fiberFormFactor, norm_neg]

theorem cutoffFormFactorL2_conjugation (g Λ : ℝ) (hΛ : 0 < Λ) :
    conjugateOnePhonon (cutoffFormFactorL2 g Λ hΛ) = cutoffFormFactorL2 g Λ hΛ := by
  apply Lp.ext
  filter_upwards [conjugateOnePhonon_ae (cutoffFormFactorL2 g Λ hΛ),
    cutoffFormFactorL2_ae g Λ hΛ] with k hc hf
  rw [hc, hf, Complex.conj_ofReal]

theorem cutoffFormFactorL2_reflection (g Λ : ℝ) (hΛ : 0 < Λ) :
    reflectOnePhonon (cutoffFormFactorL2 g Λ hΛ) = cutoffFormFactorL2 g Λ hΛ := by
  apply Lp.ext
  have hn := space_negation_preserving.quasiMeasurePreserving.ae (cutoffFormFactorL2_ae g Λ hΛ)
  filter_upwards [reflectOnePhonon_ae (cutoffFormFactorL2 g Λ hΛ),
    cutoffFormFactorL2_ae g Λ hΛ, hn] with k hr hf hn
  rw [hr, hn, cutoffFormFactor_even, hf]

end Froehlich
