import Froehlich.Nodes.KE01JointCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- Each block is selected from the actual nine coordinates without scaling. -/
def kernelInputCoordinates (b : Fin 3) : (Fin 9 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin 3 => ContinuousLinearMap.proj
    (⟨3*b.val+i.val,by omega⟩ : Fin 9))

def kernelSumCoordinates : (Fin 9 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  kernelInputCoordinates 0+kernelInputCoordinates 1+kernelInputCoordinates 2

def kernelNegativeCoordinates : (Fin 9 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  -kernelInputCoordinates 0

theorem kernelCoordinateBlock_eq (b : Fin 3) (x : Fin 9 → ℝ) :
    kernelCoordinateBlock b x = (EuclideanSpace.equiv (Fin 3) ℝ).symm (kernelInputCoordinates b x) := rfl

theorem kernelSumCoordinates_physical (x : Fin 9 → ℝ) :
    (EuclideanSpace.equiv (Fin 3) ℝ).symm (kernelSumCoordinates x) =
      kernelCoordinateBlock 0 x+kernelCoordinateBlock 1 x+kernelCoordinateBlock 2 x := by
  change (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ((kernelInputCoordinates 0 x+kernelInputCoordinates 1 x)+kernelInputCoordinates 2 x) = _
  rw [map_add,map_add]
  rfl

theorem kernelNegativeCoordinates_physical (x : Fin 9 → ℝ) :
    (EuclideanSpace.equiv (Fin 3) ℝ).symm (kernelNegativeCoordinates x) =
      -kernelCoordinateBlock 0 x := by
  change (EuclideanSpace.equiv (Fin 3) ℝ).symm (-kernelInputCoordinates 0 x) = _
  rw [map_neg]
  rfl

/-- The native affine chain rule retains exactly one linear-map factor per
ordinary derivative; there are no higher derivatives of these inputs. -/
theorem ke01_iteratedFDeriv_linear_pullback_bound {d : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (Fin 3 → ℝ) → V) (hF : ContDiff ℝ 3 F)
    (L : (Fin d → ℝ) →L[ℝ] (Fin 3 → ℝ)) (k : ℕ) (hk : k ≤ 3)
    (K : ℝ) (hK : ∀ y, ‖iteratedFDeriv ℝ k F y‖ ≤ K) (x : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ k (F ∘ L) x‖ ≤ K*‖L‖^k := by
  rw [L.iteratedFDeriv_comp_right hF x (by exact_mod_cast hk)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    mul_le_mul_of_nonneg_right (hK (L x)) (pow_nonneg (norm_nonneg L) k)

end Froehlich
