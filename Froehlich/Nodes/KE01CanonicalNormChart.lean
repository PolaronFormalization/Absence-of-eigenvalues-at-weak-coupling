import Froehlich.Nodes.KE01AffineCoordinates
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- Flattening only reindexes the actual three coordinate blocks. -/
def kernelFlattenCoordinates (T : Fin 3 → Fin 3 → ℝ) : Fin 9 → ℝ :=
  fun j => T ((finProdFinEquiv (m := 3) (n := 3)).symm j).1 ((finProdFinEquiv (m := 3) (n := 3)).symm j).2

theorem kernelInputCoordinates_flatten (T : Fin 3 → Fin 3 → ℝ) (b : Fin 3) :
    kernelInputCoordinates b (kernelFlattenCoordinates T) = T b := by
  funext i
  have hj : (⟨3*b.val+i.val,by omega⟩ : Fin 9) = (finProdFinEquiv (m := 3) (n := 3)) (b,i) := by
    apply Fin.ext
    change 3*b.val+i.val = i.val+3*b.val
    omega
  change kernelFlattenCoordinates T (⟨3*b.val+i.val,by omega⟩ : Fin 9) = T b i
  rw [hj]
  simp only [kernelFlattenCoordinates,Equiv.symm_apply_apply]

theorem kernelCoordinateBlock_flatten (T : Fin 3 → Fin 3 → ℝ) (b : Fin 3) :
    kernelCoordinateBlock b (kernelFlattenCoordinates T) =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm (T b) := by
  rw [kernelCoordinateBlock_eq,kernelInputCoordinates_flatten]

def kernelCoordinatesFor (P q r : GW.Space) : Fin 9 → ℝ :=
  kernelFlattenCoordinates ![(EuclideanSpace.equiv (Fin 3) ℝ) P,
    (EuclideanSpace.equiv (Fin 3) ℝ) q,(EuclideanSpace.equiv (Fin 3) ℝ) r]

def kernelJointBlock (b : Fin 3) : (GW.Space × (GW.Space × GW.Space)) →L[ℝ] GW.Space :=
  ![ContinuousLinearMap.fst ℝ GW.Space (GW.Space × GW.Space),
    (ContinuousLinearMap.fst ℝ GW.Space GW.Space).comp
      (ContinuousLinearMap.snd ℝ GW.Space (GW.Space × GW.Space)),
    (ContinuousLinearMap.snd ℝ GW.Space GW.Space).comp
      (ContinuousLinearMap.snd ℝ GW.Space (GW.Space × GW.Space))] b

/-- The inverse chart is a genuine bounded real-linear map on the actual
momentum triple, so derivative norms can also be transported back. -/
def kernelJointCoordinateInverse : (GW.Space × (GW.Space × GW.Space)) →L[ℝ] (Fin 9 → ℝ) :=
  ContinuousLinearMap.pi (fun j =>
    (ContinuousLinearMap.proj ((finProdFinEquiv (m := 3) (n := 3)).symm j).2).comp
      (((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap).comp
        (kernelJointBlock ((finProdFinEquiv (m := 3) (n := 3)).symm j).1)))

theorem kernelJointCoordinateInverse_apply (t : GW.Space × (GW.Space × GW.Space)) :
    kernelJointCoordinateInverse t = kernelCoordinatesFor t.1 t.2.1 t.2.2 := by
  funext j
  change (EuclideanSpace.equiv (Fin 3) ℝ)
      (kernelJointBlock ((finProdFinEquiv (m := 3) (n := 3)).symm j).1 t) ((finProdFinEquiv (m := 3) (n := 3)).symm j).2 =
    ![(EuclideanSpace.equiv (Fin 3) ℝ) t.1,
      (EuclideanSpace.equiv (Fin 3) ℝ) t.2.1,
      (EuclideanSpace.equiv (Fin 3) ℝ) t.2.2]
        ((finProdFinEquiv (m := 3) (n := 3)).symm j).1 ((finProdFinEquiv (m := 3) (n := 3)).symm j).2
  generalize ((finProdFinEquiv (m := 3) (n := 3)).symm j).1 = b
  fin_cases b <;> rfl

theorem kernelJointCoordinates_coordinatesFor (P q r : GW.Space) :
    kernelJointCoordinates (kernelCoordinatesFor P q r) = (P,(q,r)) := by
  simp [kernelCoordinatesFor,kernelJointCoordinates_apply,kernelCoordinateBlock_flatten]

theorem kernelJointCoordinates_surjective : Function.Surjective kernelJointCoordinates := by
  rintro ⟨P,q,r⟩
  exact ⟨kernelCoordinatesFor P q r,kernelJointCoordinates_coordinatesFor P q r⟩

theorem kernelJointCoordinates_rightInverse :
    Function.RightInverse kernelJointCoordinateInverse kernelJointCoordinates := by
  rintro ⟨P,q,r⟩
  rw [kernelJointCoordinateInverse_apply,kernelJointCoordinates_coordinatesFor]

end Froehlich
