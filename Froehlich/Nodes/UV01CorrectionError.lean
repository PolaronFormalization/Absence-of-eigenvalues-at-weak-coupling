import Froehlich.Nodes.UV01CorrectionConvergence
import Froehlich.Nodes.UV01InverseBounds

/-! The source's literal three-factor telescoping, with a rate independent
of physical momentum in the corresponding original energy norms. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
local instance uvCorrectionErrorEndNormedGroup (P : GW.Space) :
    NormedAddCommGroup (OneParticleEnergySpace P →L[ℂ] OneParticleEnergySpace P) :=
  ContinuousLinearMap.toNormedAddCommGroup

private theorem tripleNorm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : G →L[ℂ] H) (Q : F →L[ℂ] G) (B : E →L[ℂ] F)
    (a q b : ℝ) (ha : ‖A‖ ≤ a) (hq : ‖Q‖ ≤ q) (hb : ‖B‖ ≤ b) :
    ‖A.comp (Q.comp B)‖ ≤ a*q*b := by
  have hqa : 0 ≤ q := Q.opNorm_nonneg.trans hq
  have haa : 0 ≤ a := A.opNorm_nonneg.trans ha
  calc
    _ ≤ ‖A‖*‖Q.comp B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖*(‖Q‖*‖B‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) A.opNorm_nonneg
    _ ≤ a*(q*b) := mul_le_mul ha (mul_le_mul hq hb B.opNorm_nonneg hqa)
      (mul_nonneg Q.opNorm_nonneg B.opNorm_nonneg) haa
    _ = _ := by ring

private theorem schurDifferenceNorm_le {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : E →L[ℂ] H) (Q T : H →L[ℂ] H) (K dA dQ : ℝ)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ K) (hBA : ‖B-A‖ ≤ dA)
    (hT : ‖T‖ ≤ 6) (hTQ : ‖T-Q‖ ≤ dQ) :
    ‖B.adjoint.comp (T.comp B)-A.adjoint.comp (Q.comp A)‖ ≤ (dA*6*K+K*6*dA)+K*dQ*K := by
  have hAd : ‖A.adjoint‖ ≤ K := (ContinuousLinearMap.adjoint.norm_map A).trans_le hA
  have hBd : ‖B.adjoint-A.adjoint‖ ≤ dA := by
    rw [←map_sub ContinuousLinearMap.adjoint B A,ContinuousLinearMap.adjoint.norm_map]
    exact hBA
  have hid : B.adjoint.comp (T.comp B)-A.adjoint.comp (Q.comp A) =
      (B.adjoint-A.adjoint).comp (T.comp B) + A.adjoint.comp (T.comp (B-A)) +
        A.adjoint.comp ((T-Q).comp A) := by
    simp only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]
    abel
  rw [hid]
  have h1 : ‖(B.adjoint-A.adjoint).comp (T.comp B)‖ ≤ dA*6*K :=
    tripleNorm_le _ _ _ dA 6 K hBd hT hB
  have h2 : ‖A.adjoint.comp (T.comp (B-A))‖ ≤ K*6*dA :=
    tripleNorm_le _ _ _ K 6 dA hAd hT hBA
  have h3 : ‖A.adjoint.comp ((T-Q).comp A)‖ ≤ K*dQ*K :=
    tripleNorm_le _ _ _ K dQ K hAd hTQ hA
  let X := (B.adjoint-A.adjoint).comp (T.comp B)
  let Y := A.adjoint.comp (T.comp (B-A))
  let Z := A.adjoint.comp ((T-Q).comp A)
  have hsum : ‖X+Y+Z‖ ≤ (‖X‖+‖Y‖)+‖Z‖ :=
    (norm_add_le (X+Y) Z).trans (add_le_add (norm_add_le X Y) (le_refl ‖Z‖))
  exact hsum.trans (add_le_add (add_le_add h1 h2) h3)

variable (e : ℝ) (P : GW.Space) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem cutoffEnergySchurCorrection_error (Λ : GW.Operators.PositiveCutoff) (hΛ : 1 ≤ Λ.val) :
    ‖cutoffEnergySchurCorrection e P he g hg hsmall Λ-singularEnergySchurCorrection e P he g hg hsmall‖ ≤
      (12*(Real.sqrt 2*phiMixedConstant*|g|)*(Real.sqrt 2*lyHighConstant*|g|) +
        36*(Real.sqrt 2*phiMixedConstant*|g|)^2*lyHighConstant*|g|)/Real.sqrt Λ.val := by
  let A := twoSectorCoupling g P
  let B := cutoffTwoSectorCoupling g P Λ
  let Q := singularTwoSectorReferenceInverse e P he g hg hsmall
  let T := cutoffTwoSectorReferenceInverse e P he g hg hsmall Λ
  let K := Real.sqrt 2*phiMixedConstant*|g|
  let dA := Real.sqrt 2*lyHighConstant*|g|/Real.sqrt Λ.val
  let dQ := 36*lyHighConstant*|g|/Real.sqrt Λ.val
  have hA : ‖A‖ ≤ K := twoSectorCoupling_norm_le g P hg
  have hB : ‖B‖ ≤ K := cutoffTwoSectorCoupling_norm_le g P Λ hg
  have hBA : ‖B-A‖ ≤ dA := cutoffTwoSectorCoupling_error g P Λ hΛ
  have hT : ‖T‖ ≤ 6 := by
    simpa only [T,cutoffTwoSectorReferenceInverse,neg_neg] using!
      cutoffAuxiliaryEnergyInverse_norm_le 2 e (-P) (by norm_num) he g hg hsmall Λ
  have hTQ : ‖T-Q‖ ≤ dQ := by
    simpa only [T,Q,dQ,cutoffTwoSectorReferenceInverse,singularTwoSectorReferenceInverse,neg_neg] using!
      cutoffAuxiliaryEnergyInverse_error 2 e (-P) (by norm_num) he g hg hsmall Λ hΛ
  have hnorm : ‖B.adjoint.comp (T.comp B)-A.adjoint.comp (Q.comp A)‖ ≤
      (dA*6*K+K*6*dA)+K*dQ*K := schurDifferenceNorm_le A B Q T K dA dQ hA hB hBA hT hTQ
  change ‖B.adjoint.comp (T.comp B)-A.adjoint.comp (Q.comp A)‖ ≤ _
  refine hnorm.trans_eq ?_
  dsimp only [dA,dQ,K]
  ring

theorem cutoffEnergySchurCorrection_tendsto :
    Tendsto (cutoffEnergySchurCorrection e P he g hg hsmall) atTop
      (𝓝 (singularEnergySchurCorrection e P he g hg hsmall)) := by
  apply cutoffNormRate_tendsto _ _
    (12*(Real.sqrt 2*phiMixedConstant*|g|)*(Real.sqrt 2*lyHighConstant*|g|) +
      36*(Real.sqrt 2*phiMixedConstant*|g|)^2*lyHighConstant*|g|)
  exact cutoffEnergySchurCorrection_error e P he g hg hsmall

end Froehlich
