import Froehlich.Nodes.KE01InputNativeBounds
import Froehlich.Nodes.KE01AffineCoordinates

set_option autoImplicit false
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance ke01AffineFockReal : NormedSpace ℝ GW.Fock.Carrier := NormedSpace.restrictScalars ℝ ℂ _
local instance ke01AffineFockEndGroup : NormedAddCommGroup (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ke01AffineFockEndReal : NormedSpace ℝ (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  (BoundedEndReal.realNormedAlgebra (E := GW.Fock.Carrier)).toNormedSpace

private theorem ke01_affine_power_bound {d : ℕ}
    (L : (Fin d → ℝ) →L[ℝ] (Fin 3 → ℝ)) (k : ℕ) (hk : k ≤ 3) :
    ‖L‖^k ≤ (1+‖L‖)^3 := by
  interval_cases k <;> norm_num <;>
    nlinarith [norm_nonneg L,sq_nonneg ‖L‖,pow_nonneg (norm_nonneg L) 3]

theorem ke01_groundSource_affine_common {d : ℕ}
    (L : (Fin d → ℝ) →L[ℝ] (Fin 3 → ℝ)) : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (k : ℕ) (hk : k ≤ 3) (x : Fin d → ℝ),
      ‖iteratedFDeriv ℝ k
        (fun y => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm (L y)) he g hg hs) x‖ ≤ C*|g| := by
  obtain ⟨C,hC,hB⟩ := ke01_groundSource_native_common
  refine ⟨C*(1+‖L‖)^3,by positivity,?_⟩
  intro g e he hg hs k hk x
  let F := fun t : Fin 3 → ℝ => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs
  have hF : ContDiff ℝ 3 F := by
    simpa only [F,Function.comp_def] using!
      (auxiliaryGroundSourceVector_contDiff g e he hg hs).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hN := ke01_iteratedFDeriv_linear_pullback_bound F hF L k hk (C*|g|)
    (fun q => hB g e he hg hs k hk q) x
  have hMul := mul_le_mul_of_nonneg_left (ke01_affine_power_bound L k hk)
    (mul_nonneg hC.le (abs_nonneg g))
  exact hN.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hMul)

theorem ke01_extendedResolvent_affine_common {d : ℕ}
    (L : (Fin d → ℝ) →L[ℝ] (Fin 3 → ℝ)) : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
      (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (k : ℕ) (hk : k ≤ 3) (x : Fin d → ℝ),
      ‖iteratedFDeriv ℝ k
        (fun y => auxiliaryExtendedResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm (L y)) he g hg hs) x‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := ke01_extendedResolvent_native_common
  refine ⟨C*(1+‖L‖)^3,by positivity,?_⟩
  intro n e hn he g hg hs k hk x
  let F := fun t : Fin 3 → ℝ => auxiliaryExtendedResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs
  have hF : ContDiff ℝ 3 F := by
    simpa only [F,Function.comp_def] using!
      (auxiliaryExtendedResolvent_contDiff n e hn he g hg hs).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hN := ke01_iteratedFDeriv_linear_pullback_bound F hF L k hk C
    (fun q => hB n e hn he g hg hs k hk q) x
  exact hN.trans (mul_le_mul_of_nonneg_left (ke01_affine_power_bound L k hk) hC.le)

end Froehlich
