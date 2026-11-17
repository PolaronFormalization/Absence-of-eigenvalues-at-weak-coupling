import Froehlich.Nodes.RS02SandwichBilinear
import Froehlich.Nodes.RS02RealLinear
import Froehlich.Nodes.RS02RealTopology
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! The actual form sandwich as a bounded real-bilinear map. Complex
conjugation in its first slot is retained, not differentiated as holomorphic. -/
noncomputable section
namespace Froehlich
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ H] [NormedSpace ℝ V]
    [SMulCommClass ℂ ℝ H] [SMulCommClass ℂ ℝ V]
    [IsScalarTower ℝ ℂ H] [IsScalarTower ℝ ℂ V]
    [ContinuousSMul ℝ (H →L[ℂ] V)]
    [ContinuousSMul ℝ ((H →L[ℂ] V) →L[ℂ] (H →L[ℂ] H))]

def formSandwichReal (a : GW.Analysis.BoundedForm V) :
    (H →L[ℂ] V) →L[ℝ] ((H →L[ℂ] V) →L[ℝ] (H →L[ℂ] H)) := by
  let R : ((H →L[ℂ] V) →L[ℂ] (H →L[ℂ] H)) →L[ℝ]
      ((H →L[ℂ] V) →L[ℝ] (H →L[ℂ] H)) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ (H →L[ℂ] V) (H →L[ℂ] H) ℝ ℝ).toContinuousLinearMap
  exact R.comp (conjugateLinearRealTopology (formSandwichConjugate (H := H) (V := V) a))

@[simp] theorem formSandwichReal_apply (a : GW.Analysis.BoundedForm V) (A B : H →L[ℂ] V) :
    formSandwichReal a A B = formRepresentative (boundedFormPullback a A B) := rfl

theorem formSandwichReal_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : GW.Analysis.BoundedForm V) (k : ℕ) (f g : X → H →L[ℂ] V)
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (fun x => formSandwichReal a (f x) (g x)) := by
  have h : ContDiff ℝ k (fun x => ((formSandwichReal (H := H) (V := V) a) (f x)) (g x)) := by
    simpa only [Function.comp_apply] using!
      ((formSandwichReal (H := H) (V := V) a).contDiff.comp hf).clm_apply hg
  exact h

end Froehlich
