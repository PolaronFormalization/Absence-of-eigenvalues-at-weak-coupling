import Froehlich.Nodes.KE01JointRegularity
import Froehlich.Nodes.CA01MultiIndexBlocks

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- Nine real coordinates, in the source order P, q, r. -/
def kernelCoordinateBlock (b : Fin 3) : (Fin 9 → ℝ) →L[ℝ] GW.Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 => ContinuousLinearMap.proj
      (⟨3*b.val+i.val,by omega⟩ : Fin 9)))

def kernelJointCoordinates : (Fin 9 → ℝ) →L[ℝ] GW.Space × (GW.Space × GW.Space) :=
  (kernelCoordinateBlock 0).prod ((kernelCoordinateBlock 1).prod (kernelCoordinateBlock 2))

theorem kernelJointCoordinates_apply (x : Fin 9 → ℝ) :
    kernelJointCoordinates x =
      (kernelCoordinateBlock 0 x,(kernelCoordinateBlock 1 x,kernelCoordinateBlock 2 x)) := rfl

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

def thresholdKernelJCoordinates (x : Fin 9 → ℝ) : ℂ :=
  thresholdKernelJ e he g hg hs (kernelCoordinateBlock 0 x)
    (kernelCoordinateBlock 1 x) (kernelCoordinateBlock 2 x)

def thresholdKernelCCoordinates (x : Fin 9 → ℝ) : ℂ :=
  thresholdKernelC e he g hg hs (kernelCoordinateBlock 0 x)
    (kernelCoordinateBlock 1 x) (kernelCoordinateBlock 2 x)

theorem thresholdKernelJCoordinates_contDiff :
    ContDiff ℝ 3 (thresholdKernelJCoordinates e he g hg hs) := by
  have h := (thresholdKernelJ_contDiff e he g hg hs).comp kernelJointCoordinates.contDiff
  simpa only [Function.comp_def,kernelJointCoordinates_apply,thresholdKernelJCoordinates] using! h

theorem thresholdKernelCCoordinates_contDiffAt (x : Fin 9 → ℝ)
    (hx : ‖kernelCoordinateBlock 0 x‖ < 1/3) :
    ContDiffAt ℝ 3 (thresholdKernelCCoordinates e he g hg hs) x := by
  have h := (thresholdKernelC_contDiffAt e he g hg hs (kernelJointCoordinates x) hx).comp x
    kernelJointCoordinates.contDiff.contDiffAt
  simpa only [Function.comp_def,kernelJointCoordinates_apply,thresholdKernelCCoordinates] using! h

theorem thresholdKernelCCoordinates_contDiffAt_closedBall (x : Fin 9 → ℝ)
    (hx : ‖kernelCoordinateBlock 0 x‖ ≤ 1/4) :
    ContDiffAt ℝ 3 (thresholdKernelCCoordinates e he g hg hs) x := by
  apply thresholdKernelCCoordinates_contDiffAt e he g hg hs x
  linarith

end Froehlich
