import Froehlich.Nodes.SP01EnergyResolvent

/-! Self-adjointness of the actual full energy representative, and two-sided
inversion from an explicitly constructed right inverse. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem vacuumEnergyOperator_selfadjoint (g : ℝ) (P : GW.Space) (lam : ℝ) :
    (vacuumEnergyOperator g P lam).adjoint = vacuumEnergyOperator g P lam := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro w u
  rw [← inner_conj_symm,vacuumEnergyOperator_spec,(fiberFormData g P none).hermitian u w]
  simpa only [Complex.star_def,map_sub,map_mul,Complex.conj_conj,Complex.conj_ofReal,
    inner_conj_symm] using (vacuumEnergyOperator_spec g P lam w u).symm

theorem vacuumEnergyOperator_left_of_right (g : ℝ) (P : GW.Space) (lam : ℝ)
    (R : EnergySpace P →L[ℂ] EnergySpace P)
    (hTR : vacuumEnergyOperator g P lam * R = 1) :
    R * vacuumEnergyOperator g P lam = 1 := by
  let T := vacuumEnergyOperator g P lam
  have hstar : R.adjoint * T = 1 := by
    have h := congrArg ContinuousLinearMap.adjoint hTR
    simpa only [ContinuousLinearMap.mul_def,ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_one,vacuumEnergyOperator_selfadjoint] using h
  have hR : R.adjoint = R := by
    calc
      R.adjoint = R.adjoint * (T * R) := by rw [hTR,mul_one]
      _ = (R.adjoint * T) * R := (mul_assoc _ _ _).symm
      _ = R := by rw [hstar,one_mul]
  simpa only [hR] using hstar

end Froehlich
