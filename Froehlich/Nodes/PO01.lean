import Froehlich.Nodes.PO01Form
import Froehlich.Nodes.PO01Cauchy
import Froehlich.Nodes.PO01Scalar

/-! PO01: sufficient unnormalized two-vector positivity, for arbitrary real c.
The inverse is the actual retained coercive inverse of the given positive B. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem twoVector_positivity (B : H →L[ℂ] H) (hB : B.adjoint = B)
    (beta : ℝ) (hb : 0 < beta)
    (hp : ∀ v, beta*‖v‖^2 ≤ (⟪v,B v⟫_ℂ).re) (b t : H) (c : ℝ) :
    let R := coerciveEnergyInverse B hB hb hp
    let N := (⟪b,R b⟫_ℂ).re
    let U := ⟪b,R t⟫_ℂ
    let T := (⟪t,R t⟫_ℂ).re
    1+U ≠ 0 → 0 ≤ ‖1+U‖^2+T*(c-N) →
      ∀ u, 0 ≤ (twoVectorForm B b t c u u).re := by
  dsimp only
  intro hne hcriterion u
  let R := coerciveEnergyInverse B hB hb hp
  let U : ℂ := ⟪b,R t⟫_ℂ
  let a : ℂ := ⟪t,u⟫_ℂ
  let y : H := u+a • R b
  have hRT : R*B = 1 := coerciveEnergyInverse_left B hB hb hp
  have hBR : B*R = 1 := coerciveEnergyInverse_right B hB hb hp
  have hBR_apply (v : H) : B (R v) = v := congrArg (fun S : H →L[ℂ] H => S v) hBR
  have hR : R.adjoint = R := inverse_selfadjoint B R hB hRT hBR
  have hU : ⟪t,R b⟫_ℂ = (starRingEnd ℂ) U := by
    rw [← R.adjoint_inner_left,hR]
    exact (inner_conj_symm _ _).symm
  have hy : ⟪t,y⟫_ℂ = (1+(starRingEnd ℂ) U)*a := by
    change ⟪t,u+a • R b⟫_ℂ = _
    rw [inner_add_right,inner_smul_right,hU]
    change a+a*((starRingEnd ℂ) U) = _
    ring
  have hn : ‖1+(starRingEnd ℂ) U‖ = ‖1+U‖ := by
    have he : 1+(starRingEnd ℂ) U = (starRingEnd ℂ) (1+U) := by rw [map_add,map_one]
    rw [he]
    exact Complex.norm_conj _
  have hcs := twoVector_inverse_cauchy B R hB hBR_apply beta hb hp t y
  rw [hy,norm_mul,mul_pow,hn] at hcs
  have hA : 0 < ‖1+U‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hBy : 0 ≤ (⟪y,B y⟫_ℂ).re :=
    (mul_nonneg hb.le (sq_nonneg ‖y‖)).trans (hp y)
  have hresult := twoVector_scalar_positivity hA hBy (sq_nonneg ‖a‖) hcs hcriterion
  have he : (twoVectorForm B b t c u u).re =
      (⟪y,B y⟫_ℂ).re + (c-(⟪b,R b⟫_ℂ).re)*‖a‖^2 :=
    (twoVectorForm_diagonal B b t c u).trans
      (twoVector_completion_square B R hB hBR_apply b u a c)
  exact hresult.trans_eq he.symm

end Froehlich
