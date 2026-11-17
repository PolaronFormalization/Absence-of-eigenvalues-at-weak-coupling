import Froehlich.Nodes.CV01FormRepresentatives

/-! The common-energy inverse operators are genuine two-sided inverses of
those same actual fixed-graph form representatives. -/
noncomputable section
namespace Froehlich
private theorem inverseCoordinateConjugation {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] E) (C : E →L[ℂ] H) (T Q : H →L[ℂ] H)
    (hCB : C.comp B=ContinuousLinearMap.id ℂ H) (hBC : B.comp C=ContinuousLinearMap.id ℂ E)
    (hQT : Q*T=1) (hTQ : T*Q=1) :
    (B.comp (Q.comp B.adjoint))*(C.adjoint.comp (T.comp C))=1 ∧
      (C.adjoint.comp (T.comp C))*(B.comp (Q.comp B.adjoint))=1 := by
  have ha : B.adjoint.comp C.adjoint=ContinuousLinearMap.id ℂ H := by
    have h := congrArg ContinuousLinearMap.adjoint hCB
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] using h
  have hb : C.adjoint.comp B.adjoint=ContinuousLinearMap.id ℂ E := by
    have h := congrArg ContinuousLinearMap.adjoint hBC
    simpa only [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_id] using h
  constructor
  · apply ContinuousLinearMap.ext
    intro u
    change B (Q (B.adjoint (C.adjoint (T (C u)))))=u
    have hai := congrArg (fun L : H →L[ℂ] H => L (T (C u))) ha
    change B.adjoint (C.adjoint (T (C u)))=T (C u) at hai
    rw [hai]
    have hq := congrArg (fun L : H →L[ℂ] H => L (C u)) hQT
    change Q (T (C u))=C u at hq
    rw [hq]
    exact congrArg (fun L : E →L[ℂ] E => L u) hBC
  · apply ContinuousLinearMap.ext
    intro u
    change C.adjoint (T (C (B (Q (B.adjoint u)))))=u
    have hci := congrArg (fun L : H →L[ℂ] H => L (Q (B.adjoint u))) hCB
    change C (B (Q (B.adjoint u)))=Q (B.adjoint u) at hci
    rw [hci]
    have ht := congrArg (fun L : H →L[ℂ] H => L (B.adjoint u)) hTQ
    change T (Q (B.adjoint u))=B.adjoint u at ht
    rw [ht]
    exact congrArg (fun L : E →L[ℂ] E => L u) hb

variable (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant*|g| ≤ 1/2)

theorem cutoffCommonFormOperator_inverse_pair (Λ : GW.Operators.PositiveCutoff) :
    cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ*cutoffCommonFormOperator n e p0 p hn he g Λ=1 ∧
      cutoffCommonFormOperator n e p0 p hn he g Λ*cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ=1 := by
  simpa only [cutoffCommonEnergyInverse,cutoffCommonFormOperator] using
    inverseCoordinateConjugation (highEnergyCoordinateChange (-p0) (-p) n)
      (highEnergyCoordinateChange (-p) (-p0) n) (cutoffCompressedEnergyOperator n e p hn he Λ g)
      (cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ)
      (ContinuousLinearMap.ext (highEnergyCoordinateChange_cancel (-p) (-p0) n))
      (ContinuousLinearMap.ext (highEnergyCoordinateChange_cancel (-p0) (-p) n))
      (cutoffCompressedEnergyInverse_left n e p hn he Λ g hg hsmall)
      (cutoffCompressedEnergyInverse_right n e p hn he Λ g hg hsmall)

theorem singularCommonFormOperator_inverse_pair :
    singularCommonEnergyInverse n e p0 p hn he g hg hsmall*singularCommonFormOperator n e p0 p hn he g=1 ∧
      singularCommonFormOperator n e p0 p hn he g*singularCommonEnergyInverse n e p0 p hn he g hg hsmall=1 := by
  simpa only [singularCommonEnergyInverse,singularCommonFormOperator] using
    inverseCoordinateConjugation (highEnergyCoordinateChange (-p0) (-p) n)
      (highEnergyCoordinateChange (-p) (-p0) n) (auxiliaryCompressedEnergyOperator n e p hn he g)
      (auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall)
      (ContinuousLinearMap.ext (highEnergyCoordinateChange_cancel (-p) (-p0) n))
      (ContinuousLinearMap.ext (highEnergyCoordinateChange_cancel (-p0) (-p) n))
      (auxiliaryCompressedEnergyInverse_left n e p hn he g hg hsmall)
      (auxiliaryCompressedEnergyInverse_right n e p hn he g hg hsmall)

end Froehlich
