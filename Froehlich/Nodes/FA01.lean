import Froehlich.Nodes.FA00

/-! FA01: an actual bounded inverse in energy coordinates gives the three
retained GW resolvent fields on the physical operator's full domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def physicalEnergyInverse (d : GW.Operators.CoerciveFormData V H) (R : V →L[ℂ] V) : H →L[ℂ] H :=
  d.embedding.comp (R.comp d.embedding.adjoint)

theorem physicalEnergyInverse_norm_le (d : GW.Operators.CoerciveFormData V H)
    (R : V →L[ℂ] V) : ‖physicalEnergyInverse d R‖ ≤ ‖d.embedding‖ ^ 2 * ‖R‖ := by
  calc
    ‖physicalEnergyInverse d R‖ ≤ ‖d.embedding‖ * ‖R.comp d.embedding.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖d.embedding‖ * (‖R‖ * ‖d.embedding.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = ‖d.embedding‖ ^ 2 * ‖R‖ := by rw [LinearIsometryEquiv.norm_map]; ring

theorem physicalEnergyInverse_isResolvent (d : GW.Operators.CoerciveFormData V H)
    (lam : ℝ) (T R : V →L[ℂ] V)
    (hrep : ∀ w u, ⟪w, T u⟫_ℂ = d.form w u - (lam : ℂ) * ⟪d.embedding w, d.embedding u⟫_ℂ)
    (hRT : R * T = 1) (hTR : T * R = 1) :
    GW.Operators.IsResolvent (GW.Operators.formOperator d) (lam : ℂ) (physicalEnergyInverse d R) := by
  have hTR_apply (z : V) : T (R z) = z := congrArg (fun L : V →L[ℂ] V => L z) hTR
  have hRT_apply (z : V) : R (T z) = z := congrArg (fun L : V →L[ℂ] V => L z) hRT
  have hsol (f : H) (w : V) : d.form w (R (d.embedding.adjoint f)) =
      ⟪d.embedding w, f + (lam : ℂ) • physicalEnergyInverse d R f⟫_ℂ := by
    have h := hrep w (R (d.embedding.adjoint f))
    rw [hTR_apply, d.embedding.adjoint_inner_right] at h
    change d.form w (R (d.embedding.adjoint f)) =
      ⟪d.embedding w, f + (lam : ℂ) • d.embedding (R (d.embedding.adjoint f))⟫_ℂ
    rw [inner_add_right, inner_smul_right]
    linear_combination -h
  have heq (f : H) := GW.Operators.formOperator_domain_of_equation d
    (R (d.embedding.adjoint f)) (f + (lam : ℂ) • physicalEnergyInverse d R f) (hsol f)
  have hmem (f : H) : physicalEnergyInverse d R f ∈ (GW.Operators.formOperator d).domain := (heq f).choose
  refine ⟨hmem, ?_, ?_⟩
  · intro f
    change GW.Operators.formOperator d
      ⟨d.embedding (R (d.embedding.adjoint f)), (heq f).choose⟩ -
      (lam : ℂ) • physicalEnergyInverse d R f = f
    rw [(heq f).choose_spec, add_sub_cancel_right]
  · intro u
    let x := GW.Operators.operatorFormCoordinate d u
    have hx : d.embedding x = (u : H) := GW.Operators.operatorFormCoordinate_embedding d u
    have ht : T x = d.embedding.adjoint
        (GW.Operators.formOperator d u - (lam : ℂ) • (u : H)) := by
      apply ext_inner_left ℂ
      intro w
      rw [hrep, d.embedding.adjoint_inner_right, inner_sub_right, inner_smul_right, hx]
      exact congrArg (fun z : ℂ => z - (lam : ℂ) * ⟪d.embedding w, (u : H)⟫_ℂ)
        (GW.Operators.formOperator_form_identity d u w)
    change d.embedding (R (d.embedding.adjoint
      (GW.Operators.formOperator d u - (lam : ℂ) • (u : H)))) = (u : H)
    rw [← ht, hRT_apply, hx]

theorem energyKernel_hasEigenvector (d : GW.Operators.CoerciveFormData V H)
    (lam : ℝ) (T : V →L[ℂ] V)
    (hrep : ∀ w u, ⟪w, T u⟫_ℂ = d.form w u - (lam : ℂ) * ⟪d.embedding w, d.embedding u⟫_ℂ)
    (u : V) (hu : u ≠ 0) (hTu : T u = 0) :
    HasEigenvector (GW.Operators.formOperator d) lam := by
  have hs (w : V) : d.form w u = ⟪d.embedding w, (lam : ℂ) • d.embedding u⟫_ℂ := by
    have h := hrep w u
    rw [hTu, inner_zero_right] at h
    rw [inner_smul_right]
    linear_combination -h
  obtain ⟨hm, he⟩ := GW.Operators.formOperator_domain_of_equation d u ((lam : ℂ) • d.embedding u) hs
  refine ⟨⟨d.embedding u, hm⟩, ?_, he⟩
  intro hz
  apply hu
  apply d.embedding_injective
  simpa only [map_zero] using hz
end Froehlich
