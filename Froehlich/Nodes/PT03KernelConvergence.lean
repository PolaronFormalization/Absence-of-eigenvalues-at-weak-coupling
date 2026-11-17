import Froehlich.Nodes.PT03KernelDefinitions
import Froehlich.Nodes.PT02SourceConvergence
import Froehlich.Nodes.CV01PhysicalInverse

set_option autoImplicit false

/-! Pointwise convergence of the literal scalar kernels at fixed parameters.
No varying-parameter substitution into a field AE identity is used. -/
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace Froehlich

private theorem pt03_extended_tendsto (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) :
    Tendsto (fun Lambda : GW.Operators.PositiveCutoff => cutoffAuxiliaryExtendedResolvent n e p he Lambda g hg hs)
      atTop (𝓝 (auxiliaryExtendedResolvent n e p he g hg hs)) := by
  let I : HighSectorSpace n →L[ℂ] GW.Fock.Carrier := (HighSectorSpace n).subtypeL
  let Q : GW.Fock.Carrier →L[ℂ] HighSectorSpace n := highSectorProject n
  let B : (HighSectorSpace n →L[ℂ] HighSectorSpace n) → (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
    fun T => I.comp (T.comp Q)
  have hpre : Continuous (fun T : HighSectorSpace n →L[ℂ] HighSectorSpace n => T.comp Q) :=
    continuous_id.clm_comp_const Q
  have hB : Continuous B := hpre.const_clm_comp I
  have hR : Tendsto (fun Lambda : GW.Operators.PositiveCutoff => cutoffAuxiliaryResolvent n e p he Lambda g hg hs)
      atTop (𝓝 (auxiliaryResolvent n e p he g hg hs)) :=
    (cutoffAuxiliaryResolvent_uniform_on_bounded n e 0 hn he g hg hs {p}
      Bornology.isBounded_singleton).tendsto_at (Set.mem_singleton p)
  have h := (hB.tendsto (auxiliaryResolvent n e p he g hg hs)).comp hR
  exact h

private theorem pt03_apply_tendsto
    (T : GW.Operators.PositiveCutoff → GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)
    (S : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)
    (v : GW.Operators.PositiveCutoff → GW.Fock.Carrier) (w : GW.Fock.Carrier)
    (hT : Tendsto T atTop (𝓝 S)) (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun Lambda => T Lambda (v Lambda)) atTop (𝓝 (S w)) :=
  (((ContinuousLinearMap.id ℂ (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)).continuous₂).tendsto (S,w)).comp
    (hT.prodMk_nhds hv)

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem cutoffThresholdKernelJ_tendsto (P q r : GW.Space) :
    Tendsto (fun Lambda : GW.Operators.PositiveCutoff => cutoffThresholdKernelJ e he g hg hs Lambda P q r)
      atTop (𝓝 (thresholdKernelJ e he g hg hs P q r)) := by
  have hq : Tendsto (fun Lambda => cutoffThresholdSourceVector e he g hg hs Lambda q) atTop
      (𝓝 (auxiliaryGroundSourceVector e q he g hg hs)) := cutoffGroundSourceVector_tendsto e q he g hg hs
  have hr : Tendsto (fun Lambda => cutoffThresholdSourceVector e he g hg hs Lambda r) atTop
      (𝓝 (auxiliaryGroundSourceVector e r he g hg hs)) := cutoffGroundSourceVector_tendsto e r he g hg hs
  have hZ := pt03_extended_tendsto 0 e (P+q+r) (by norm_num) he g hg hs
  have hX := pt03_extended_tendsto 2 e (-P) (by norm_num) he g hg hs
  have hOq : Tendsto (fun Lambda => GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Lambda q)
      atTop (𝓝 (GW.Fock.vacuum-auxiliaryGroundSourceVector e q he g hg hs)) := tendsto_const_nhds.sub hq
  have hOr : Tendsto (fun Lambda => GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Lambda r)
      atTop (𝓝 (GW.Fock.vacuum-auxiliaryGroundSourceVector e r he g hg hs)) := tendsto_const_nhds.sub hr
  have hleft := hOq.inner (𝕜 := ℂ) (pt03_apply_tendsto _ _ _ _ hZ hOr)
  have hright := hq.inner (𝕜 := ℂ) (pt03_apply_tendsto _ _ _ _ hX hr)
  exact hleft.add hright

theorem cutoffThresholdKernelC_tendsto (P q r : GW.Space) :
    Tendsto (fun Lambda : GW.Operators.PositiveCutoff => cutoffThresholdKernelC e he g hg hs Lambda P q r)
      atTop (𝓝 (thresholdKernelC e he g hg hs P q r)) := by
  exact tendsto_const_nhds.sub (cutoffThresholdKernelJ_tendsto e he g hg hs P q r)

end Froehlich
