import Froehlich.Nodes.UV01SourceLoads

/-! Source solutions in fixed coordinates are the physical coordinate images
of the actual cutoff and singular full-domain energy solutions. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem highEnergyCoordinateChange_adjoint_load (P Q : GW.Space) (n : ℕ)
    (F : ConjugateLoad (HighEnergySpace Q n)) :
    (highEnergyCoordinateChange P Q n).adjoint
      (loadRiesz (F.comp (highEnergyCoordinateChange Q P n))) = loadRiesz F := by
  apply loadRiesz_unique
  intro w
  rw [(highEnergyCoordinateChange P Q n).adjoint_inner_right]
  rw [← loadRiesz_spec]
  change F w = F (highEnergyCoordinateChange Q P n (highEnergyCoordinateChange P Q n w))
  rw [highEnergyCoordinateChange_cancel]

variable (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def cutoffCommonSourceSolution (Λ : GW.Operators.PositiveCutoff) : HighEnergySpace (-p0) n :=
  cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ
    (loadRiesz (cutoffCommonSourceLoad g p0 p n Λ.val))

def singularCommonSourceSolution : HighEnergySpace (-p0) n :=
  singularCommonEnergyInverse n e p0 p hn he g hg hsmall
    (loadRiesz (singularCommonSourceLoad g p0 p n))

theorem cutoffCommonSourceSolution_eq (Λ : GW.Operators.PositiveCutoff) :
    cutoffCommonSourceSolution n e p0 p hn he g hg hsmall Λ =
      highEnergyCoordinateChange (-p0) (-p) n
        (cutoffAuxiliaryDualSolution n e p hn he g hg hsmall Λ
          (cutoffHighFiberSourceLoad g (-p) n Λ.val)) := by
  change highEnergyCoordinateChange (-p0) (-p) n
    (cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ
      ((highEnergyCoordinateChange (-p0) (-p) n).adjoint
        (loadRiesz ((cutoffHighFiberSourceLoad g (-p) n Λ.val).comp
          (highEnergyCoordinateChange (-p) (-p0) n))))) = _
  rw [highEnergyCoordinateChange_adjoint_load,cutoffAuxiliaryEnergyInverse_load]

theorem singularCommonSourceSolution_eq :
    singularCommonSourceSolution n e p0 p hn he g hg hsmall =
      highEnergyCoordinateChange (-p0) (-p) n
        (auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall
          (loadRiesz (singularHighFiberSourceLoad g (-p) n))) := by
  change highEnergyCoordinateChange (-p0) (-p) n
    (auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall
      ((highEnergyCoordinateChange (-p0) (-p) n).adjoint
        (loadRiesz ((singularHighFiberSourceLoad g (-p) n).comp
          (highEnergyCoordinateChange (-p) (-p0) n))))) = _
  rw [highEnergyCoordinateChange_adjoint_load]

end Froehlich
