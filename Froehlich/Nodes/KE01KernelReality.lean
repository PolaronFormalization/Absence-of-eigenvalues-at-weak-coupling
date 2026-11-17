import Froehlich.Nodes.KE01PhysicalConjugation
import Froehlich.Nodes.SY01FieldConjugation

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem ke01_fockConjugation_vacuum : fockConjugation GW.Fock.vacuum = GW.Fock.vacuum := by
  apply lp.ext
  funext n
  cases n with
  | zero =>
    apply (physicalSector 0).injective
    apply Lp.ext
    have hv : physicalSector 0 (GW.Fock.vacuum 0) =ᵐ[GW.Fock.sectorMeasure 0]
        (fun _ => (1 : ℂ)) := by
      rw [GW.Fock.vacuum_zero]
      change GW.Fock.vacuumAdapterIsometry (1 : ℂ) =ᵐ[GW.Fock.sectorMeasure 0] (fun _ => (1 : ℂ))
      exact GW.Fock.vacuumAdapter_ae (1 : ℂ)
    filter_upwards [fockConjugation_physical GW.Fock.vacuum 0,hv] with k hk hv
    rw [hk,hv,map_one]
  | succ n =>
    change sectorConjugation (n+1) (GW.Fock.vacuum (n+1)) = GW.Fock.vacuum (n+1)
    rw [GW.Fock.vacuum_succ,sectorConjugation_zero]

private theorem ke01_real_pairing (u v : GW.Fock.Carrier)
    (hu : fockConjugation u = u) (hv : fockConjugation v = v) :
    (starRingEnd ℂ) ⟪u,v⟫_ℂ = ⟪u,v⟫_ℂ := by
  rw [←fockConjugation_inner,hu,hv]

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem thresholdKernelJ_conj (P q r : GW.Space) :
    (starRingEnd ℂ) (thresholdKernelJ e he g hg hs P q r) =
      thresholdKernelJ e he g hg hs P q r := by
  have hh (t : GW.Space) := auxiliaryGroundSourceVector_conjugation e t he g hg hs
  have hv (t : GW.Space) : fockConjugation
      (GW.Fock.vacuum-auxiliaryGroundSourceVector e t he g hg hs) =
      GW.Fock.vacuum-auxiliaryGroundSourceVector e t he g hg hs := by
    change fockConjugationIsometry (GW.Fock.vacuum-auxiliaryGroundSourceVector e t he g hg hs) = _
    rw [map_sub]
    exact congrArg₂ (fun u v : GW.Fock.Carrier => u-v) ke01_fockConjugation_vacuum (hh t)
  have hZ : fockConjugation (auxiliaryZ e (P+q+r) he g hg hs
      (GW.Fock.vacuum-auxiliaryGroundSourceVector e r he g hg hs)) =
      auxiliaryZ e (P+q+r) he g hg hs
      (GW.Fock.vacuum-auxiliaryGroundSourceVector e r he g hg hs) := by
    change fockConjugation (auxiliaryExtendedResolvent 0 e (P+q+r) he g hg hs _) = _
    rw [auxiliaryExtendedResolvent_conjugation 0 e (P+q+r) (by norm_num) he g hg hs,hv r]
    rfl
  have hX : fockConjugation (auxiliaryX e he g hg hs P
      (auxiliaryGroundSourceVector e r he g hg hs)) =
      auxiliaryX e he g hg hs P (auxiliaryGroundSourceVector e r he g hg hs) := by
    change fockConjugation (auxiliaryExtendedResolvent 2 e (-P) he g hg hs _) = _
    rw [auxiliaryExtendedResolvent_conjugation 2 e (-P) (by norm_num) he g hg hs,hh r]
    rfl
  unfold thresholdKernelJ
  rw [map_add,ke01_real_pairing _ _ (hv q) hZ,ke01_real_pairing _ _ (hh q) hX]

theorem thresholdKernelC_conj (P q r : GW.Space) :
    (starRingEnd ℂ) (thresholdKernelC e he g hg hs P q r) =
      thresholdKernelC e he g hg hs P q r := by
  unfold thresholdKernelC
  rw [map_sub,Complex.conj_ofReal,thresholdKernelJ_conj]

theorem thresholdKernelJ_ofReal_re (P q r : GW.Space) :
    ((thresholdKernelJ e he g hg hs P q r).re : ℂ) = thresholdKernelJ e he g hg hs P q r := by
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (thresholdKernelJ_conj e he g hg hs P q r)
    simp only [Complex.conj_im] at h
    simp only [Complex.ofReal_im]
    linarith

theorem thresholdKernelC_ofReal_re (P q r : GW.Space) :
    ((thresholdKernelC e he g hg hs P q r).re : ℂ) = thresholdKernelC e he g hg hs P q r := by
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (thresholdKernelC_conj e he g hg hs P q r)
    simp only [Complex.conj_im] at h
    simp only [Complex.ofReal_im]
    linarith

end Froehlich
