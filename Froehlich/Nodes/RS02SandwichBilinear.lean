import Froehlich.Nodes.RS02RieszTransport
import Mathlib.Topology.Instances.RealVectorSpace

/-! The fixed-energy form sandwich is an actual bounded semibilinear map
of its two bounded weight maps, before any parameter differentiation. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [NormedSpace ℂ V]

def boundedFormPullback (a : GW.Analysis.BoundedForm V) (A B : H →L[ℂ] V) :
    GW.Analysis.BoundedForm H :=
  ((ContinuousLinearMap.compL ℂ H V ℂ).flip B).comp (a.comp A)

@[simp] theorem boundedFormPullback_apply (a : GW.Analysis.BoundedForm V)
    (A B : H →L[ℂ] V) (w u : H) : boundedFormPullback a A B w u = a (A w) (B u) := rfl

private theorem boundedFormPullback_add_right (a : GW.Analysis.BoundedForm V)
    (A B C : H →L[ℂ] V) :
    boundedFormPullback a A (B+C) = boundedFormPullback a A B + boundedFormPullback a A C := by
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro u
  simp only [boundedFormPullback_apply,ContinuousLinearMap.add_apply,map_add]

private theorem boundedFormPullback_add_left (a : GW.Analysis.BoundedForm V)
    (A B C : H →L[ℂ] V) :
    boundedFormPullback a (A+B) C = boundedFormPullback a A C + boundedFormPullback a B C := by
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro u
  simp only [boundedFormPullback_apply,ContinuousLinearMap.add_apply,map_add]

private theorem boundedFormPullback_smul_right (a : GW.Analysis.BoundedForm V)
    (A B : H →L[ℂ] V) (c : ℂ) :
    boundedFormPullback a A (c • B) = c • boundedFormPullback a A B := by
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro u
  simp only [boundedFormPullback_apply,ContinuousLinearMap.smul_apply,map_smulₛₗ,RingHom.id_apply]

private theorem boundedFormPullback_smul_left (a : GW.Analysis.BoundedForm V)
    (A B : H →L[ℂ] V) (c : ℂ) :
    boundedFormPullback a (c • A) B = (starRingEnd ℂ) c • boundedFormPullback a A B := by
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro u
  simp only [boundedFormPullback_apply,ContinuousLinearMap.smul_apply,map_smulₛₗ]

theorem boundedFormPullback_riesz_norm_le (a : GW.Analysis.BoundedForm V)
    (A B : H →L[ℂ] V) :
    ‖formRepresentative (boundedFormPullback a A B)‖ ≤ ‖a‖*‖A‖*‖B‖ := by
  apply formRepresentative_norm_le _ (mul_nonneg (mul_nonneg a.opNorm_nonneg A.opNorm_nonneg) B.opNorm_nonneg)
  intro w u
  have hAB := mul_le_mul (A.le_opNorm w) (B.le_opNorm u) (norm_nonneg _)
    (mul_nonneg A.opNorm_nonneg (norm_nonneg w))
  calc
    ‖boundedFormPullback a A B w u‖ ≤ (‖a‖*‖A w‖)*‖B u‖ :=
      ((a (A w)).le_opNorm (B u)).trans
        (mul_le_mul_of_nonneg_right (a.le_opNorm (A w)) (norm_nonneg (B u)))
    _ = ‖a‖*(‖A w‖*‖B u‖) := by ring
    _ ≤ ‖a‖*((‖A‖*‖w‖)*(‖B‖*‖u‖)) := mul_le_mul_of_nonneg_left hAB a.opNorm_nonneg
    _ = _ := by ring

def formSandwichRight (a : GW.Analysis.BoundedForm V) (A : H →L[ℂ] V) :
    (H →L[ℂ] V) →L[ℂ] (H →L[ℂ] H) :=
  ({ toFun := fun B => formRepresentative (boundedFormPullback a A B)
     map_add' := fun B C => by rw [boundedFormPullback_add_right,formRepresentative_add]
     map_smul' := fun c B => by
       simp only [boundedFormPullback_smul_right,formRepresentative_smul,RingHom.id_apply] } :
      (H →L[ℂ] V) →ₗ[ℂ] (H →L[ℂ] H)).mkContinuous (‖a‖*‖A‖) (fun B =>
        boundedFormPullback_riesz_norm_le a A B)

@[simp] theorem formSandwichRight_apply (a : GW.Analysis.BoundedForm V) (A B : H →L[ℂ] V) :
    formSandwichRight a A B = formRepresentative (boundedFormPullback a A B) := rfl

theorem formSandwichRight_norm_le (a : GW.Analysis.BoundedForm V) (A : H →L[ℂ] V) :
    ‖formSandwichRight a A‖ ≤ ‖a‖*‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg a.opNorm_nonneg A.opNorm_nonneg)
  exact fun B => boundedFormPullback_riesz_norm_le a A B

def formSandwichConjugate (a : GW.Analysis.BoundedForm V) :
    (H →L[ℂ] V) →L⋆[ℂ] ((H →L[ℂ] V) →L[ℂ] (H →L[ℂ] H)) := by
  let F : (H →L[ℂ] V) →ₗ⋆[ℂ] ((H →L[ℂ] V) →L[ℂ] (H →L[ℂ] H)) :=
    { toFun := fun (A : H →L[ℂ] V) => formSandwichRight (H := H) (V := V) a A
      map_add' := fun A B => by
        apply ContinuousLinearMap.ext
        intro C
        simp only [formSandwichRight_apply,ContinuousLinearMap.add_apply,
          boundedFormPullback_add_left,formRepresentative_add]
      map_smul' := fun c A => by
        apply ContinuousLinearMap.ext
        intro B
        simp only [formSandwichRight_apply,ContinuousLinearMap.smul_apply,
          boundedFormPullback_smul_left,formRepresentative_smul] }
  have hF : ∀ (A : H →L[ℂ] V), ‖F A‖ ≤ ‖a‖*‖A‖ := by
    intro A
    exact formSandwichRight_norm_le (H := H) (V := V) a A
  exact ⟨F,AddMonoidHomClass.continuous_of_bound F ‖a‖ hF⟩

@[simp] theorem formSandwichConjugate_apply (a : GW.Analysis.BoundedForm V) (A B : H →L[ℂ] V) :
    formSandwichConjugate a A B = formRepresentative (boundedFormPullback a A B) := rfl

end Froehlich
