import Froehlich.Nodes.SY01TotalForms

/-! The same actual form symmetries at every finite cutoff and at the
singular index, with arbitrary real spectral shift. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem indexedFiberForm_conjugation (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (w u : EnergySpace P) :
    (fiberFormData g P i).form (energyConjugation P w) (energyConjugation P u) =
      (starRingEnd ℂ) ((fiberFormData g P i).form w u) := by
  cases i with
  | none => exact fiberTotalForm_conjugation g P w u
  | some Λ =>
    rw [fiberFormData_cutoff_apply,fiberFormData_cutoff_apply,freeFiberForm_conjugation,
      cutoffInteraction_conjugation,map_add]

theorem indexedFiberForm_reflection (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (w u : EnergySpace P) :
    (fiberFormData g (-P) i).form (energyReflection P w) (energyReflection P u) =
      (fiberFormData g P i).form w u := by
  cases i with
  | none => exact fiberTotalForm_reflection g P w u
  | some Λ =>
    rw [fiberFormData_cutoff_apply,fiberFormData_cutoff_apply,freeFiberForm_reflection,
      cutoffInteraction_reflection]

theorem indexedShiftedFiberForm_conjugation (g lam : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (w u : EnergySpace P) :
    (fiberFormData g P i).form (energyConjugation P w) (energyConjugation P u) -
        (lam : ℂ)*⟪energyEmbedding P (energyConjugation P w),energyEmbedding P (energyConjugation P u)⟫_ℂ =
      (starRingEnd ℂ) ((fiberFormData g P i).form w u -
        (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ) := by
  rw [indexedFiberForm_conjugation,energyConjugation_intertwines,energyConjugation_intertwines,
    fockConjugation_inner,map_sub,map_mul,Complex.conj_ofReal]

theorem indexedShiftedFiberForm_reflection (g lam : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (w u : EnergySpace P) :
    (fiberFormData g (-P) i).form (energyReflection P w) (energyReflection P u) -
        (lam : ℂ)*⟪energyEmbedding (-P) (energyReflection P w),energyEmbedding (-P) (energyReflection P u)⟫_ℂ =
      (fiberFormData g P i).form w u - (lam : ℂ)*⟪energyEmbedding P w,energyEmbedding P u⟫_ℂ := by
  rw [indexedFiberForm_reflection,energyReflection_intertwines,energyReflection_intertwines]
  exact congrArg (fun z : ℂ => (fiberFormData g P i).form w u - (lam : ℂ)*z)
    (fockReflectionEquiv.inner_map_map _ _)

end Froehlich
