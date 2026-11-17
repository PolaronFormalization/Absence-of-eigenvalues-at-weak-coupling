import Froehlich.Nodes.PT03ScalarSource
import Froehlich.Nodes.PT03ScalarStepOne
import Froehlich.Nodes.PT02ProjectionConvention

set_option autoImplicit false

/-! PT03 Step 2's scalar field pairing for each fixed q. No varying
parameter is inserted into an almost-everywhere assertion. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem cutoffXSource_pairing_field (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (Λ : GW.Operators.PositiveCutoff) (P q : GW.Space) :
    ∀ᵐ k ∂volume,
      ⟪annihilationField (projectedCutoffAuxiliaryXNumber e he g hg hs Λ P
        (cutoffGroundSourceNumber e q he g hg hs Λ)) k,
        oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property)⟫_ℂ =
      (cutoffFormFactor g Λ.val k : ℂ) *
        (⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryZ e (q+k) he Λ g hg hs
            (cutoffThresholdSourceVector e he g hg hs Λ (k-P))⟫_ℂ -
        ⟪cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryX e he Λ g hg hs P
            (cutoffThresholdSourceVector e he g hg hs Λ (k-P))⟫_ℂ) := by
  let b := GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q
  let hq := cutoffThresholdSourceVector e he g hg hs Λ q
  let v := oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property)
  have hN : numberFormEmbedding (cutoffGroundSourceNumber e q he g hg hs Λ) = hq :=
    energyNumberCoordinates_intertwines (-q) _
  have hpt := projectedCutoffAuxiliaryX_pullthrough e he g hg hs Λ P
    (cutoffGroundSourceNumber e q he g hg hs Λ)
  rw [hN] at hpt
  filter_upwards [hpt,cutoffGroundSource_pullthrough e q he g hg hs Λ] with k hp hk
  change annihilationField (cutoffGroundSourceNumber e q he g hg hs Λ) k =
    (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryZ e (q+k) he Λ g hg hs b at hk
  let hr := cutoffThresholdSourceVector e he g hg hs Λ (k-P)
  have hY : ⟪cutoffAuxiliaryY e (k-P) he Λ g hg hs
      (annihilationField (cutoffGroundSourceNumber e q he g hg hs Λ) k -
        (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryX e he Λ g hg hs P hq),v⟫_ℂ =
      ⟪annihilationField (cutoffGroundSourceNumber e q he g hg hs Λ) k -
        (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryX e he Λ g hg hs P hq,hr⟫_ℂ := by
    have h := (pt03_cutoffExtendedResolvent_pairing 1 e (k-P) he Λ g hg hs
      (annihilationField (cutoffGroundSourceNumber e q he g hg hs Λ) k -
        (cutoffFormFactor g Λ.val k : ℂ) • cutoffAuxiliaryX e he Λ g hg hs P hq) v).symm
    change _ = ⟪_,cutoffAuxiliaryY e (k-P) he Λ g hg hs v⟫_ℂ at h
    rw [cutoffThresholdSourceVector_eq_Y] at h
    exact h
  have hZ : ⟪cutoffAuxiliaryZ e (q+k) he Λ g hg hs b,hr⟫_ℂ =
      ⟪b,cutoffAuxiliaryZ e (q+k) he Λ g hg hs hr⟫_ℂ :=
    (pt03_cutoffExtendedResolvent_pairing 0 e (q+k) he Λ g hg hs b hr).symm
  have hX : ⟪cutoffAuxiliaryX e he Λ g hg hs P hq,hr⟫_ℂ =
      ⟪hq,cutoffAuxiliaryX e he Λ g hg hs P hr⟫_ℂ :=
    (pt03_cutoffExtendedResolvent_pairing 2 e (-P) he Λ g hg hs hq hr).symm
  change ⟪_,v⟫_ℂ = _
  rw [hp,hY,hk,inner_sub_left,inner_smul_left,inner_smul_left,Complex.conj_ofReal,hZ,hX]
  ring

end Froehlich
