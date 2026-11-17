import Froehlich.Nodes.PT01CoreScalarTests

/-! At the limit, the physical source F is genuinely in the number-form
domain. FC03 therefore identifies the limiting creation pairing with AF. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem localCreation_source_test (K : Set GW.Space) (hK : MeasurableSet K)
    (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) (w F : NumberFormSpace) :
    Integrable (fun k => (starRingEnd ℂ) (chi k)*⟪numberFormEmbedding w,annihilationField F k⟫_ℂ)
      ((volume : Measure GW.Space).restrict K) ∧
    (∫ k in K, (starRingEnd ℂ) (chi k)*⟪numberFormEmbedding w,annihilationField F k⟫_ℂ)=
      ⟪creationRestriction (localScalarTestExtension K hK chi) w,numberFormEmbedding F⟫_ℂ := by
  let chiG := localScalarTestExtension K hK chi
  obtain ⟨hi,heq⟩ := smearedCreation_test_integral chiG w F
  have hAE : (fun k => (starRingEnd ℂ) (chiG k)*⟪numberFormEmbedding w,annihilationField F k⟫_ℂ)
      =ᵐ[(volume : Measure GW.Space).restrict K]
      (fun k => (starRingEnd ℂ) (chi k)*⟪numberFormEmbedding w,annihilationField F k⟫_ℂ) := by
    filter_upwards [localScalarTestExtension_restrict_ae K hK chi] with k hk
    rw [hk]
  refine ⟨hi.restrict.congr hAE,?_⟩
  calc
    _ = ∫ k in K, (starRingEnd ℂ) (chiG k)*⟪numberFormEmbedding w,annihilationField F k⟫_ℂ :=
      integral_congr_ae hAE.symm
    _ = ∫ k, (starRingEnd ℂ) (chiG k)*⟪numberFormEmbedding w,annihilationField F k⟫_ℂ :=
      localScalarTestExtension_integral_restrict K hK chi _
    _ = _ := heq

end Froehlich
