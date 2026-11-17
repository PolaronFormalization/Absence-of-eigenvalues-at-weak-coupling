import Froehlich.Nodes.PT03ScalarStepTwoIntegral

set_option autoImplicit false

/-! The finite-cutoff correction is an ordinary integral of the scalar
diagonal and iterated kernel terms. Absolute splitting is a subsequent step. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem cutoffCorrection_integrated_row (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (Λ : GW.Operators.PositiveCutoff) (P : GW.Space) (f h : GW.OnePhonon) :
    let v := cutoffFormFactorL2 g Λ.val Λ.property
    let row := fun k =>
      (starRingEnd ℂ) (f k) * h k *
        ⟪oneParticleInclusion v,cutoffAuxiliaryY e (k-P) he Λ g hg hs (oneParticleInclusion v)⟫_ℂ +
      (starRingEnd ℂ) (f k) * (cutoffFormFactor g Λ.val k : ℂ) *
        (∫ l, h l * (cutoffFormFactor g Λ.val l : ℂ) * cutoffThresholdKernelJ e he g hg hs Λ P (k-P) (l-P))
    Integrable row volume ∧
      ⟪(oneToHighMap v f : GW.Fock.Carrier),
        cutoffAuxiliaryX e he Λ g hg hs P (oneToHighMap v h : GW.Fock.Carrier)⟫_ℂ = ∫ k, row k := by
  intro v row
  let z := cutoffAuxiliaryXNumber e he g hg hs Λ P (oneToHighMap v h)
  have hphys : numberFormEmbedding z =
      cutoffAuxiliaryX e he Λ g hg hs P (oneToHighMap v h : GW.Fock.Carrier) :=
    cutoffAuxiliaryXNumber_physical e he g hg hs Λ P (oneToHighMap v h)
  have ht := oneToHighMap_pairing_integral v f z
  rw [hphys] at ht
  have hr : (fun k => (starRingEnd ℂ) (f k) *
      ⟪oneParticleInclusion v,annihilationField z k⟫_ℂ) =ᵐ[volume] row := by
    dsimp only [v,z]
    filter_upwards [cutoffOneToHighSolution_field e he g hg hs Λ P h] with k hk
    have hY := pt03_cutoffExtendedResolvent_pairing 1 e (k-P) he Λ g hg hs
      (oneParticleInclusion v)
      (oneParticleInclusion h-cutoffAuxiliaryX e he Λ g hg hs P (oneToHighMap v h : GW.Fock.Carrier))
    change ⟪oneParticleInclusion v,cutoffAuxiliaryY e (k-P) he Λ g hg hs _⟫_ℂ =
      ⟪cutoffAuxiliaryY e (k-P) he Λ g hg hs (oneParticleInclusion v),_⟫_ℂ at hY
    rw [cutoffThresholdSourceVector_eq_Y] at hY
    have hq := (cutoffGroundSource_kernel_pairing e he g hg hs Λ P (k-P) h).2
    rw [hk,inner_add_right,inner_smul_right,inner_smul_right,hY,hq,
      ←cutoffThresholdSourceVector_eq_Y e he g hg hs Λ (k-P)]
    dsimp only [row]
    ring
  exact ⟨ht.1.congr hr,ht.2.trans (integral_congr_ae hr)⟩

end Froehlich
