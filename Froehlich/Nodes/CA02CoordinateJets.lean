import Froehlich.Nodes.CA01TotalDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

/-! Finite continuous coordinate jets give norm C^r regularity. The
partial hypotheses are genuine native derivatives; the result iterates
CA01's checked total derivative and the native fderiv characterization.
This is an intermediate calculus lemma, not the final multiplier theorem. -/
noncomputable section
open scoped Topology
namespace Froehlich
variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem contDiffOn_of_continuousCoordinateJets
    (J : List (Fin d) → (Fin d → ℝ) → V) (r : ℕ)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hcontinuous : ∀ is, is.length ≤ r → ContinuousOn (J is) S)
    (hpartial : ∀ is, is.length < r → ∀ p ∈ S, ∀ i : Fin d,
      HasDerivAt (fun t : ℝ => J is (Function.update p i t)) (J (i::is) p) (p i)) :
    ∀ k : ℕ, ∀ is : List (Fin d), is.length+k ≤ r → ContDiffOn ℝ k (J is) S := by
  intro k
  induction k with
  | zero =>
    intro is hlen
    exact contDiffOn_zero.mpr (hcontinuous is (by omega))
  | succ k ih =>
    intro is hlen
    have hnext : ∀ i : Fin d, ContDiffOn ℝ k (J (i::is)) S := by
      intro i
      apply ih
      simp only [List.length_cons]
      omega
    have hD : ∀ i : Fin d, ContinuousOn (fun p => J (i::is) p) S :=
      fun i => (hnext i).continuousOn
    have hFD : ∀ p ∈ S, HasFDerivAt (J is)
        (coordinateDerivative d (fun i => J (i::is) p)) p := by
      intro p hp
      exact continuousCoordinatePartials_hasFDerivAt d (J is) (fun p i => J (i::is) p)
        S hS hD (hpartial is (by omega)) p hp
    have htuple : ContDiffOn ℝ k (fun p => (fun i : Fin d => J (i::is) p)) S :=
      contDiffOn_pi.mpr hnext
    have hL : ContDiffOn ℝ k (fun p => coordinateDerivative d (fun i => J (i::is) p)) S :=
      (coordinateDerivativeAssembler (E := V) d).contDiff.comp_contDiffOn htuple
    have he : ((k+1 : ℕ) : WithTop ENat) = (k : WithTop ENat)+1 := by simp
    rw [he,contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨?_,?_,?_⟩
    · intro p hp
      exact (hFD p hp).differentiableAt.differentiableWithinAt
    · intro hk
      simp at hk
    · exact hL.congr (fun p hp => (hFD p hp).fderiv)

end Froehlich
