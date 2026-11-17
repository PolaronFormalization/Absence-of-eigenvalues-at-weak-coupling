import Froehlich.Nodes.BA01

/-! The actual bounded-form Riesz representative is a bounded complex-linear
map. This transports fixed-domain form derivatives to operator norm. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem formRepresentative_add (a b : GW.Analysis.BoundedForm V) :
    formRepresentative (a+b) = formRepresentative a + formRepresentative b := by
  apply Eq.symm
  apply formRepresentative_unique
  intro w u
  simp only [ContinuousLinearMap.add_apply,inner_add_right]
  rw [formRepresentative_spec,formRepresentative_spec]

theorem formRepresentative_smul (c : ℂ) (a : GW.Analysis.BoundedForm V) :
    formRepresentative (c • a) = c • formRepresentative a := by
  apply Eq.symm
  apply formRepresentative_unique
  intro w u
  simp only [ContinuousLinearMap.smul_apply,inner_smul_right,smul_eq_mul]
  rw [formRepresentative_spec]

theorem formRepresentative_norm_le_opNorm (a : GW.Analysis.BoundedForm V) :
    ‖formRepresentative a‖ ≤ ‖a‖ := by
  apply formRepresentative_norm_le a a.opNorm_nonneg
  intro w u
  calc
    ‖a w u‖ ≤ ‖a w‖*‖u‖ := (a w).le_opNorm u
    _ ≤ (‖a‖*‖w‖)*‖u‖ := mul_le_mul_of_nonneg_right (a.le_opNorm w) (norm_nonneg u)

def formRepresentativeLinear : GW.Analysis.BoundedForm V →L[ℂ] (V →L[ℂ] V) :=
  ({ toFun := fun a => formRepresentative (V := V) a
     map_add' := fun a b => formRepresentative_add (V := V) a b
     map_smul' := fun c a => by simpa only [RingHom.id_apply] using formRepresentative_smul (V := V) c a } :
      GW.Analysis.BoundedForm V →ₗ[ℂ] (V →L[ℂ] V)).mkContinuous 1 (fun (a : GW.Analysis.BoundedForm V) => by
        simpa only [one_mul] using! formRepresentative_norm_le_opNorm (V := V) a)

@[simp] theorem formRepresentativeLinear_apply (a : GW.Analysis.BoundedForm V) :
    formRepresentativeLinear a = formRepresentative a := rfl

end Froehlich
