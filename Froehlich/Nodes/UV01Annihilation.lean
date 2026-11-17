import Froehlich.Nodes.UV01UniformSources
import Froehlich.Nodes.FC02
import Froehlich.Nodes.EN02Number
import Mathlib.Topology.MetricSpace.Bounded

/-! The UV source convergence in the number graph implies genuine L²
annihilation-field convergence. No evaluation at a fixed momentum occurs. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace Froehlich
variable (n : ℕ) (e : ℝ) (p0 : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem cutoffCommonSourceSolution_uniform_on_bounded (K : Set GW.Space) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space => cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ)
      (fun p : GW.Space => singularCommonSourceSolution n e p0 p hn he g hg hsmall)
      atTop K := by
  obtain ⟨R,hR,hsub⟩ := hK.subset_closedBall_lt 0 p0
  apply (cutoffCommonSourceSolution_uniform_on_ball n e p0 hn he g hg hsmall R hR.le).mono
  intro p hp
  have hd : ‖p-p0‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hsub hp
  change ‖p0-p‖ ≤ R
  simpa only [norm_sub_rev] using hd

def commonEnergyAnnihilation (p0 : GW.Space) (n : ℕ) :
    HighEnergySpace (-p0) n →L[ℂ] Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  annihilationField.comp ((energyNumberCoordinates (-p0)).comp (HighEnergySpace (-p0) n).subtypeL)

theorem commonEnergyAnnihilation_physical (u : HighEnergySpace (-p0) n) :
    numberFormEmbedding (energyNumberCoordinates (-p0) (u : EnergySpace (-p0))) =
      energyEmbedding (-p0) (u : EnergySpace (-p0)) :=
  energyNumberCoordinates_intertwines (-p0) u

theorem cutoffCommonAnnihilation_uniform_on_bounded (K : Set GW.Space) (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn
      (fun Λ : GW.Operators.PositiveCutoff => fun p : GW.Space =>
        commonEnergyAnnihilation p0 n (cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ))
      (fun p : GW.Space => commonEnergyAnnihilation p0 n (singularCommonSourceSolution n e p0 p hn he g hg hsmall))
      atTop K := by
  exact (commonEnergyAnnihilation p0 n).uniformContinuous.comp_tendstoUniformlyOn
    (cutoffCommonSourceSolution_uniform_on_bounded n e p0 hn he g hg hsmall K hK)

end Froehlich
