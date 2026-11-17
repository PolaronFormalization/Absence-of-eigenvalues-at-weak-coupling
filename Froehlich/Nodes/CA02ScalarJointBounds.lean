import Froehlich.Nodes.CA02AuxiliarySymbolDerivatives
import Froehlich.Nodes.CA01TotalDerivative

set_option autoImplicit false

/-! Uniform joint chart bounds for the actual symbols. Scalar smoothness and
native coordinate assembly provide uniform continuity before any operator
jet regularity theorem is invoked. -/
noncomputable section
namespace Froehlich

theorem auxiliaryInverseWeightJetChart_hasFDerivAt (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (he : e ≤ 0) (K : GW.Fock.Coordinates m) (p : Fin 3 → ℝ) :
    HasFDerivAt (fun q : Fin 3 → ℝ => auxiliaryInverseWeightJetChart is n e q m K)
      (coordinateDerivative 3 (fun i => auxiliaryInverseWeightJetChart (i::is) n e p m K)) p := by
  apply continuousCoordinatePartials_hasFDerivAt 3
    (fun q => auxiliaryInverseWeightJetChart is n e q m K)
    (fun q i => auxiliaryInverseWeightJetChart (i::is) n e q m K) Set.univ isOpen_univ
  · intro i
    exact (auxiliaryInverseWeightJetChart_contDiff (i::is) n m e he K 0).continuous.continuousOn
  · intro q _ i
    exact auxiliaryInverseWeightJetChart_hasDerivAt_update is n m e he q K i
  · exact Set.mem_univ p

theorem auxiliaryInverseWeightJetChart_joint_lipschitz
    (is : List (Fin 3)) (n m : ℕ) (e : ℝ) (he : e ≤ 0)
    (K : GW.Fock.Coordinates m) (p q : Fin 3 → ℝ) :
    |auxiliaryInverseWeightJetChart is n e q m K-auxiliaryInverseWeightJetChart is n e p m K| ≤
      (‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1))*‖q-p‖ := by
  have hbound (u : Fin 3 → ℝ) :
      ‖coordinateDerivative 3 (fun i => auxiliaryInverseWeightJetChart (i::is) n e u m K)‖ ≤
        ‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1) := by
    have htuple : ‖(fun i : Fin 3 => auxiliaryInverseWeightJetChart (i::is) n e u m K)‖ ≤
        scalarDerivativeCoefficientBound (is.length+1) := by
      apply (pi_norm_le_iff_of_nonneg (scalarDerivativeCoefficientBound_nonnegative (is.length+1))).mpr
      intro i
      simpa only [auxiliaryInverseWeightJetChart,List.length_cons,Real.norm_eq_abs] using
        auxiliaryInverseWeightJet_bound (i::is) n m e ((EuclideanSpace.equiv (Fin 3) ℝ).symm u) he K
    exact ((coordinateDerivativeAssembler (E := ℝ) 3).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left htuple (norm_nonneg _))
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u (_ : u ∈ (Set.univ : Set (Fin 3 → ℝ))) =>
      (auxiliaryInverseWeightJetChart_hasFDerivAt is n m e he K u).hasFDerivWithinAt)
    (fun u (_ : u ∈ (Set.univ : Set (Fin 3 → ℝ))) => hbound u)
    (convex_univ : Convex ℝ (Set.univ : Set (Fin 3 → ℝ))) (Set.mem_univ p) (Set.mem_univ q)
  simpa only [Real.norm_eq_abs] using h

end Froehlich
