import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! Continuous restriction of the genuine complex scalar action to real scalars,
without replacing a native topological module by a normed-space projection. -/
noncomputable section
namespace Froehlich

theorem realContinuousSMulOfComplex {E : Type*} [AddCommGroup E]
    [Module ℂ E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousSMul ℂ E] [IsScalarTower ℝ ℂ E] : ContinuousSMul ℝ E := by
  refine ⟨?_⟩
  have h : Continuous (fun z : ℝ × E => (z.1 : ℂ) • z.2) :=
    (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd
  convert h using 1
  funext z
  exact (algebraMap_smul ℂ z.1 z.2).symm

end Froehlich
