import Froehlich.Nodes.PT01CoreScalarTests

/-! The complex local scalar test identity in the source, with the literal
zero extension used by the smeared creation operator. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem projectedCutoffCore_local_test (g : ℝ) (P : GW.Space) (n : ℕ)
    (Lambda : GW.Operators.PositiveCutoff) (e : ℝ) (u w : boundedMomentumCore)
    (K : Set GW.Space) (hK : MeasurableSet K) (chi : Lp ℂ 2 ((volume : Measure GW.Space).restrict K)) :
    Integrable (fun k => (starRingEnd ℂ) (chi k)*
      ⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ) ((volume : Measure GW.Space).restrict K) ∧
    Integrable (fun k => ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
      ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ) ((volume : Measure GW.Space).restrict K) ∧
    (∫ k in K, (starRingEnd ℂ) (chi k)*⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ)=
      ⟪creationRestriction (localScalarTestExtension K hK chi) (coreNumberLift w),
        (coreProjectedCutoffShiftAction g P n Lambda e u : GW.Fock.Carrier)⟫_ℂ -
      ∫ k in K, ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
        ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ := by
  let chiG := localScalarTestExtension K hK chi
  have hchi : chiG =ᵐ[(volume : Measure GW.Space).restrict K] chi :=
    localScalarTestExtension_restrict_ae K hK chi
  obtain ⟨hg,hgEq⟩ := projectedCutoffCore_field_test g P n Lambda e u w chiG
  have he : (fun k => (starRingEnd ℂ) (chiG k)*
      ⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ) =ᵐ[(volume : Measure GW.Space).restrict K]
      (fun k => (starRingEnd ℂ) (chi k)*⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ) := by
    filter_upwards [hchi] with k hk
    rw [hk]
  have htailG : Integrable (fun k => ((starRingEnd ℂ) (chiG k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
      ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ) volume := by
    simpa only [RCLike.inner_apply'] using
      (L2.integrable_inner (𝕜 := ℂ) chiG (cutoffFormFactorL2 g Lambda.val Lambda.property)).mul_const
        ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ
  have htailAE : (fun k => ((starRingEnd ℂ) (chiG k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
      ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ) =ᵐ[(volume : Measure GW.Space).restrict K]
      (fun k => ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
        ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ) := by
    filter_upwards [hchi] with k hk
    rw [hk]
  have htailEq : (∫ k, ((starRingEnd ℂ) (chiG k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
      ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ)=
      ∫ k in K, ((starRingEnd ℂ) (chi k)*cutoffFormFactorL2 g Lambda.val Lambda.property k)*
        ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ := by
    calc
      _ = ∫ k, (starRingEnd ℂ) (chiG k)*(cutoffFormFactorL2 g Lambda.val Lambda.property k*
          ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ) := by simp only [mul_assoc]
      _ = ∫ k in K, (starRingEnd ℂ) (chiG k)*(cutoffFormFactorL2 g Lambda.val Lambda.property k*
          ⟪(w : GW.Fock.Carrier),(u : GW.Fock.Carrier)⟫_ℂ) :=
        (localScalarTestExtension_integral_restrict K hK chi _).symm
      _ = _ := by
        simp only [←mul_assoc]
        exact integral_congr_ae htailAE
  refine ⟨hg.restrict.congr he,htailG.restrict.congr htailAE,?_⟩
  calc
    _ = ∫ k in K, (starRingEnd ℂ) (chiG k)*
        ⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ := integral_congr_ae he.symm
    _ = ∫ k, (starRingEnd ℂ) (chiG k)*
        ⟪(w : GW.Fock.Carrier),projectedCutoffShiftField g P n Lambda e u k⟫_ℂ :=
      localScalarTestExtension_integral_restrict K hK chi _
    _ = _ := hgEq
    _ = _ := by rw [htailEq]

end Froehlich
