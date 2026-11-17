import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Complex.Basic

/-! Real-linear restriction retaining the native topological module structures. -/
noncomputable section
namespace Froehlich
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℂ A] [Module ℂ B] [Module ℝ A] [Module ℝ B]
    [TopologicalSpace A] [TopologicalSpace B]
    [ContinuousSMul ℝ A] [ContinuousSMul ℝ B] [T2Space B]

def conjugateLinearRealTopology (f : A →L⋆[ℂ] B) : A →L[ℝ] B :=
  ({ toFun := f
     map_zero' := map_zero f
     map_add' := fun x y => map_add f x y } : A →+ B).toRealLinearMap f.continuous

@[simp] theorem conjugateLinearRealTopology_apply (f : A →L⋆[ℂ] B) (x : A) :
    conjugateLinearRealTopology f x = f x := rfl
end Froehlich
