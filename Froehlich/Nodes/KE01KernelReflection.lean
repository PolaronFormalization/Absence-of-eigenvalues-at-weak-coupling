import Froehlich.Nodes.KE01ResolventReflection
import Froehlich.Nodes.KE01KernelDefinitions

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem ke01_fockReflection_vacuum : fockReflection GW.Fock.vacuum = GW.Fock.vacuum := by
  apply lp.ext
  funext n
  cases n with
  | zero =>
    apply (physicalSector 0).injective
    apply Lp.ext
    filter_upwards [fockReflection_physical GW.Fock.vacuum 0] with k hk
    rw [hk]
    exact congrArg (physicalSector 0 (GW.Fock.vacuum 0)) (Subsingleton.elim _ _)
  | succ n =>
    change sectorReflection (n+1) (GW.Fock.vacuum (n+1)) = GW.Fock.vacuum (n+1)
    rw [GW.Fock.vacuum_succ,map_zero]

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem thresholdKernelJ_reflection (P q r : GW.Space) :
    thresholdKernelJ e he g hg hs (-P) (-q) (-r) = thresholdKernelJ e he g hg hs P q r := by
  have hh (t : GW.Space) := auxiliaryGroundSourceVector_reflection e t he g hg hs
  have hv (t : GW.Space) : fockReflection
      (GW.Fock.vacuum-auxiliaryGroundSourceVector e t he g hg hs) =
      GW.Fock.vacuum-auxiliaryGroundSourceVector e (-t) he g hg hs := by
    rw [map_sub,ke01_fockReflection_vacuum,hh t]
  have hsum : (-P)+(-q)+(-r) = -(P+q+r) := by abel
  have hz := fockReflectionEquiv.inner_map_map
    (GW.Fock.vacuum-auxiliaryGroundSourceVector e q he g hg hs)
    (auxiliaryZ e (P+q+r) he g hg hs (GW.Fock.vacuum-auxiliaryGroundSourceVector e r he g hg hs))
  change ⟪fockReflection _,fockReflection _⟫_ℂ = _ at hz
  change ⟪fockReflection _,fockReflection (auxiliaryExtendedResolvent 0 e (P+q+r) he g hg hs _)⟫_ℂ = _ at hz
  rw [hv q,auxiliaryExtendedResolvent_reflection 0 e (P+q+r) (by norm_num) he g hg hs,hv r] at hz
  have hx := fockReflectionEquiv.inner_map_map
    (auxiliaryGroundSourceVector e q he g hg hs)
    (auxiliaryX e he g hg hs P (auxiliaryGroundSourceVector e r he g hg hs))
  change ⟪fockReflection _,fockReflection (auxiliaryExtendedResolvent 2 e (-P) he g hg hs _)⟫_ℂ = _ at hx
  rw [hh q,auxiliaryExtendedResolvent_reflection 2 e (-P) (by norm_num) he g hg hs,hh r] at hx
  unfold thresholdKernelJ
  rw [hsum]
  exact congrArg₂ (fun a b : ℂ => a+b) hz hx

theorem thresholdKernelC_reflection (P q r : GW.Space) :
    thresholdKernelC e he g hg hs (-P) (-q) (-r) = thresholdKernelC e he g hg hs P q r := by
  unfold thresholdKernelC
  rw [norm_neg,thresholdKernelJ_reflection]

theorem kernelConstant_even (P : GW.Space) :
    kernelConstant e he g hg hs (-P) = kernelConstant e he g hg hs P := by
  unfold kernelConstant
  simpa only [neg_zero] using congrArg Complex.re (thresholdKernelC_reflection e he g hg hs P 0 0)

theorem kernelPsi_reflection (P q : GW.Space) :
    kernelPsi e he g hg hs (-P) (-q) = kernelPsi e he g hg hs P q := by
  unfold kernelPsi
  rw [kernelConstant_even]
  have h := congrArg Complex.re (thresholdKernelC_reflection e he g hg hs P q 0)
  simpa only [neg_zero] using congrArg (fun x : ℝ => x-kernelConstant e he g hg hs P) h

end Froehlich
