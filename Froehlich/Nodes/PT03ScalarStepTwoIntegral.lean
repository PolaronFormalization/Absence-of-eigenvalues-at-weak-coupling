import Froehlich.Nodes.PT03ScalarStepTwoField

set_option autoImplicit false

/-! The remaining PT03 scalar pairing, as an absolutely integrable
ordinary integral for every fixed q. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem oneToHighMap_reverse_pairing_integral (v f : GW.OnePhonon) (z : NumberFormSpace) :
    Integrable (fun k => f k * ⟪annihilationField z k,oneParticleInclusion v⟫_ℂ) volume ∧
    ⟪numberFormEmbedding z,(oneToHighMap v f : GW.Fock.Carrier)⟫_ℂ =
      ∫ k, f k * ⟪annihilationField z k,oneParticleInclusion v⟫_ℂ := by
  have h := oneToHighMap_pairing_integral v f z
  have he (k : GW.Space) :
      (starRingEnd ℂ) ((starRingEnd ℂ) (f k) * ⟪oneParticleInclusion v,annihilationField z k⟫_ℂ) =
        f k * ⟪annihilationField z k,oneParticleInclusion v⟫_ℂ := by
    simp only [map_mul,Complex.conj_conj,inner_conj_symm]
  constructor
  · have hc : Integrable (fun k => (starRingEnd ℂ)
        ((starRingEnd ℂ) (f k) * ⟪oneParticleInclusion v,annihilationField z k⟫_ℂ)) volume :=
      h.1.mono (Complex.conjCLE.continuous.comp_aestronglyMeasurable h.1.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun k => le_of_eq (Complex.norm_conj _)))
    exact hc.congr (Filter.Eventually.of_forall he)
  · have hi := congrArg (starRingEnd ℂ) h.2
    rw [←integral_conj] at hi
    have hi' := hi.trans (integral_congr_ae (Filter.Eventually.of_forall he))
    simpa only [inner_conj_symm] using hi'

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Λ : GW.Operators.PositiveCutoff)

theorem cutoffGroundSource_high_pairing (P q : GW.Space) (f : GW.OnePhonon) :
    Integrable (fun k => f k * (cutoffFormFactor g Λ.val k : ℂ) *
      (⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
        cutoffAuxiliaryZ e (q+k) he Λ g hg hs (cutoffThresholdSourceVector e he g hg hs Λ (k-P))⟫_ℂ -
      ⟪cutoffThresholdSourceVector e he g hg hs Λ q,
        cutoffAuxiliaryX e he Λ g hg hs P (cutoffThresholdSourceVector e he g hg hs Λ (k-P))⟫_ℂ)) volume ∧
    ⟪cutoffThresholdSourceVector e he g hg hs Λ q,
      cutoffAuxiliaryX e he Λ g hg hs P
        (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) f : GW.Fock.Carrier)⟫_ℂ =
      ∫ k, f k * (cutoffFormFactor g Λ.val k : ℂ) *
        (⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryZ e (q+k) he Λ g hg hs (cutoffThresholdSourceVector e he g hg hs Λ (k-P))⟫_ℂ -
        ⟪cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryX e he Λ g hg hs P (cutoffThresholdSourceVector e he g hg hs Λ (k-P))⟫_ℂ) := by
  let z := projectedCutoffAuxiliaryXNumber e he g hg hs Λ P (cutoffGroundSourceNumber e q he g hg hs Λ)
  have hN : numberFormEmbedding (cutoffGroundSourceNumber e q he g hg hs Λ) =
      cutoffThresholdSourceVector e he g hg hs Λ q := energyNumberCoordinates_intertwines (-q) _
  have hphys : numberFormEmbedding z =
      cutoffAuxiliaryX e he Λ g hg hs P (cutoffThresholdSourceVector e he g hg hs Λ q) := by
    rw [show numberFormEmbedding z = cutoffAuxiliaryX e he Λ g hg hs P
      (numberFormEmbedding (cutoffGroundSourceNumber e q he g hg hs Λ)) from
        projectedCutoffAuxiliaryXNumber_physical e he g hg hs Λ P _,hN]
  have h := oneToHighMap_reverse_pairing_integral (cutoffFormFactorL2 g Λ.val Λ.property) f z
  rw [hphys] at h
  have hf : (fun k : GW.Space => f k) =ᵐ[volume] (fun k => f k) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hr := hf.mul (cutoffXSource_pairing_field e he g hg hs Λ P q)
  simp only [Pi.mul_def,←mul_assoc] at hr
  have hsym := pt03_cutoffExtendedResolvent_pairing 2 e (-P) he Λ g hg hs
    (cutoffThresholdSourceVector e he g hg hs Λ q)
    (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) f : GW.Fock.Carrier)
  exact ⟨h.1.congr hr,hsym.trans (h.2.trans (integral_congr_ae hr))⟩

theorem cutoffGroundSource_kernel_pairing (P q : GW.Space) (f : GW.OnePhonon) :
    Integrable (fun k => f k * (cutoffFormFactor g Λ.val k : ℂ) *
      cutoffThresholdKernelJ e he g hg hs Λ P q (k-P)) volume ∧
    ⟪cutoffThresholdSourceVector e he g hg hs Λ q,
      oneParticleInclusion f - cutoffAuxiliaryX e he Λ g hg hs P
        (oneToHighMap (cutoffFormFactorL2 g Λ.val Λ.property) f : GW.Fock.Carrier)⟫_ℂ =
      ∫ k, f k * (cutoffFormFactor g Λ.val k : ℂ) * cutoffThresholdKernelJ e he g hg hs Λ P q (k-P) := by
  have hS := cutoffGroundSource_oneParticle_pairing e q he g hg hs Λ f
  have hH := cutoffGroundSource_high_pairing e he g hg hs Λ P q f
  have hrow : (fun k =>
      f k * (cutoffFormFactor g Λ.val k : ℂ) *
        ⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryZ e (q+k) he Λ g hg hs GW.Fock.vacuum⟫_ℂ -
      f k * (cutoffFormFactor g Λ.val k : ℂ) *
        (⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryZ e (q+k) he Λ g hg hs (cutoffThresholdSourceVector e he g hg hs Λ (k-P))⟫_ℂ -
        ⟪cutoffThresholdSourceVector e he g hg hs Λ q,
          cutoffAuxiliaryX e he Λ g hg hs P (cutoffThresholdSourceVector e he g hg hs Λ (k-P))⟫_ℂ)) =ᵐ[volume]
      (fun k => f k * (cutoffFormFactor g Λ.val k : ℂ) * cutoffThresholdKernelJ e he g hg hs Λ P q (k-P)) := by
    exact Filter.Eventually.of_forall fun k => by
      dsimp only [cutoffThresholdKernelJ]
      rw [show P+q+(k-P)=q+k by abel,map_sub,inner_sub_right]
      ring
  constructor
  · exact (hS.1.sub hH.1).congr hrow
  · rw [inner_sub_right,hS.2,hH.2,←integral_sub hS.1 hH.1]
    exact integral_congr_ae hrow

end Froehlich
