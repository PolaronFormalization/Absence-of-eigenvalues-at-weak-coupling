import Froehlich.Nodes.CA02ScalarJointBounds
import Froehlich.Nodes.CA02WeightedScalarRemainder

set_option autoImplicit false

/-! Uniform local joint bounds for the actual normalized weighted symbols.
The fixed weighted target is genuine on the whole parameter space. -/
noncomputable section
namespace Froehlich

theorem auxiliaryFixedWeightJetChart_hasFDerivAt (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) (K : GW.Fock.Coordinates m) (p : Fin 3 → ℝ) :
    HasFDerivAt (fun q : Fin 3 → ℝ => auxiliaryWeight n e p0 m K*auxiliaryInverseWeightJetChart is n e q m K)
      (coordinateDerivative 3 (fun i => auxiliaryWeight n e p0 m K*
        auxiliaryInverseWeightJetChart (i::is) n e p m K)) p := by
  apply continuousCoordinatePartials_hasFDerivAt 3 _
    (fun q i => auxiliaryWeight n e p0 m K*auxiliaryInverseWeightJetChart (i::is) n e q m K)
    Set.univ isOpen_univ
  · intro i
    exact (continuous_const.mul
      (auxiliaryInverseWeightJetChart_contDiff (i::is) n m e he K 0).continuous).continuousOn
  · intro q _ i
    exact (auxiliaryInverseWeightJetChart_hasDerivAt_update is n m e he q K i).const_mul _
  · exact Set.mem_univ p

theorem auxiliaryFixedWeightJetChart_joint_lipschitzOn (is : List (Fin 3)) (n m : ℕ)
    (e : ℝ) (p0 : GW.Space) (he : e ≤ 0) (K : GW.Fock.Coordinates m)
    (p q r : Fin 3 → ℝ) (hq : q ∈ Metric.closedBall p 1) (hr : r ∈ Metric.closedBall p 1) :
    |auxiliaryWeight n e p0 m K*(auxiliaryInverseWeightJetChart is n e r m K-
      auxiliaryInverseWeightJetChart is n e q m K)| ≤
      (‖coordinateDerivativeAssembler (E := ℝ) 3‖*scalarDerivativeCoefficientBound (is.length+1)*
        (1+‖p0-(EuclideanSpace.equiv (Fin 3) ℝ).symm p‖+euclideanChartInverseNorm))*‖r-q‖ := by
  let L : (Fin 3 → ℝ) →L[ℝ] GW.Space :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap
  let C := scalarDerivativeCoefficientBound (is.length+1)*(1+‖p0-L p‖+‖L‖)
  have hcoef := scalarDerivativeCoefficientBound_nonnegative (is.length+1)
  have hC : 0 ≤ C := mul_nonneg hcoef (by positivity)
  have hbound (u : Fin 3 → ℝ) (hu : u ∈ Metric.closedBall p 1) :
      ‖coordinateDerivative 3 (fun i => auxiliaryWeight n e p0 m K*
        auxiliaryInverseWeightJetChart (i::is) n e u m K)‖ ≤
        ‖coordinateDerivativeAssembler (E := ℝ) 3‖*C := by
    have hu' : ‖u-p‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hu
    have hdelta : ‖L u-L p‖ ≤ ‖L‖ := by
      calc
        _ = ‖L (u-p)‖ := by rw [map_sub]
        _ ≤ ‖L‖*‖u-p‖ := L.le_opNorm _
        _ ≤ ‖L‖ := by nlinarith [norm_nonneg L]
    have htri := norm_sub_le_norm_sub_add_norm_sub p0 (L p) (L u)
    rw [norm_sub_rev (L p)] at htri
    have htuple : ‖(fun i : Fin 3 => auxiliaryWeight n e p0 m K*
        auxiliaryInverseWeightJetChart (i::is) n e u m K)‖ ≤ C := by
      apply (pi_norm_le_iff_of_nonneg hC).mpr
      intro i
      have h := auxiliaryInverseWeightJet_fixed_weight_bound (i::is) n m e he p0 (L u) K
      have h' : ‖auxiliaryWeight n e p0 m K*auxiliaryInverseWeightJetChart (i::is) n e u m K‖ ≤
          scalarDerivativeCoefficientBound (is.length+1)*(1+‖p0-L u‖) := by
        simpa only [L,auxiliaryInverseWeightJetChart,List.length_cons,Real.norm_eq_abs] using! h
      exact h'.trans (mul_le_mul_of_nonneg_left (by linarith) hcoef)
    exact ((coordinateDerivativeAssembler (E := ℝ) 3).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left htuple (norm_nonneg _))
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun u (_ : u ∈ Metric.closedBall p 1) =>
      (auxiliaryFixedWeightJetChart_hasFDerivAt is n m e p0 he K u).hasFDerivWithinAt)
    hbound (convex_closedBall p 1) hq hr
  have heq : auxiliaryWeight n e p0 m K*auxiliaryInverseWeightJetChart is n e r m K-
      auxiliaryWeight n e p0 m K*auxiliaryInverseWeightJetChart is n e q m K =
        auxiliaryWeight n e p0 m K*(auxiliaryInverseWeightJetChart is n e r m K-
          auxiliaryInverseWeightJetChart is n e q m K) := by ring
  rw [heq] at h
  simpa only [Real.norm_eq_abs,C,L,euclideanChartInverseNorm,mul_assoc] using! h

end Froehlich
