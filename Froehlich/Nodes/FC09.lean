import Froehlich.Nodes.FC08
import GW.Fock.FockAmplification

/-! FC09: dense constant tests and scalar L² tests determine one vector residual.
No separability or countable dense test family is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

namespace Froehlich
section Residual
variable {X V : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem residual_test_eq_contraction_inner (r : Lp V 2 μ) (w : V) (χ : Lp ℂ 2 μ) :
    (∫ k, (starRingEnd ℂ) (χ k) * ⟪w,r k⟫_ℂ ∂μ) =
      ⟪w,GW.Fock.contraction μ χ r⟫_ℂ := by
  change (∫ k, (starRingEnd ℂ) (χ k) * ⟪w,r k⟫_ℂ ∂μ) =
    ⟪w,∫ k, (starRingEnd ℂ) (χ k) • r k ∂μ⟫_ℂ
  simpa only [inner_smul_right] using
    integral_inner (𝕜 := ℂ) (GW.Fock.contraction_integrable μ χ r) w

theorem residual_dense_tests_extend (r : Lp V 2 μ) (D : Submodule ℂ V)
    (hD : Dense (D : Set V))
    (h : ∀ w ∈ D, ∀ χ : Lp ℂ 2 μ,
      (∫ k, (starRingEnd ℂ) (χ k) * ⟪w,r k⟫_ℂ ∂μ) = 0) :
    ∀ w : V, ∀ χ : Lp ℂ 2 μ, ⟪w,GW.Fock.contraction μ χ r⟫_ℂ = 0 := by
  intro w χ
  have hc : IsClosed {v : V | ⟪v,GW.Fock.contraction μ χ r⟫_ℂ = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hs : (D : Set V) ⊆ {v : V | ⟪v,GW.Fock.contraction μ χ r⟫_ℂ = 0} := by
    intro v hv
    change ⟪v,GW.Fock.contraction μ χ r⟫_ℂ = 0
    rw [← residual_test_eq_contraction_inner]
    exact h v hv χ
  exact closure_minimal hs hc (hD w)

/-- The proof also works for arbitrary μ: the pinned Lp induction uses only
finite-measure indicator sets. In particular finite and zero measures are included. -/
theorem residual_zero_of_dense_scalar_tests (r : Lp V 2 μ) (D : Submodule ℂ V)
    (hD : Dense (D : Set V))
    (h : ∀ w ∈ D, ∀ χ : Lp ℂ 2 μ,
      (∫ k, (starRingEnd ℂ) (χ k) * ⟪w,r k⟫_ℂ ∂μ) = 0) : r = 0 := by
  have he := residual_dense_tests_extend μ r D hD h
  have ht (w : V) (χ : Lp ℂ 2 μ) : ⟪GW.Fock.tensorEmbedding μ χ w,r⟫_ℂ = 0 :=
    (GW.Fock.contraction_pairing μ χ w r).symm.trans (he w χ)
  have hall (s : Lp V 2 μ) : ⟪s,r⟫_ℂ = 0 := by
    apply Lp.induction (p := 2) (μ := μ) (by norm_num) (fun s => ⟪s,r⟫_ℂ = 0)
      ?_ ?_ ?_ s
    · intro w A hA hAf
      change ⟪indicatorConstLp 2 hA hAf.ne w,r⟫_ℂ = 0
      have hz := ht w (indicatorConstLp 2 hA hAf.ne (1 : ℂ))
      change ⟪(ContinuousLinearMap.toSpanSingleton ℂ w).compLp
        (indicatorConstLp 2 hA hAf.ne (1 : ℂ)),r⟫_ℂ = 0 at hz
      rw [GW.Fock.simpleTensor_indicatorConst] at hz
      exact hz
    · intro f g hf hg _ hfr hgr
      rw [inner_add_left, hfr, hgr, add_zero]
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hall r)

theorem residual_zero_common_ae (r : Lp V 2 μ) (D : Submodule ℂ V)
    (hD : Dense (D : Set V))
    (h : ∀ w ∈ D, ∀ χ : Lp ℂ 2 μ,
      (∫ k, (starRingEnd ℂ) (χ k) * ⟪w,r k⟫_ℂ ∂μ) = 0) :
    ∀ᵐ k ∂μ, r k = 0 :=
  Lp.eq_zero_iff_ae_eq_zero.mp (residual_zero_of_dense_scalar_tests μ r D hD h)

theorem residual_all_tests_common_ae (r : Lp V 2 μ) (D : Submodule ℂ V)
    (hD : Dense (D : Set V))
    (h : ∀ w ∈ D, ∀ χ : Lp ℂ 2 μ,
      (∫ k, (starRingEnd ℂ) (χ k) * ⟪w,r k⟫_ℂ ∂μ) = 0) :
    ∀ᵐ k ∂μ, ∀ w : V, ⟪w,r k⟫_ℂ = 0 := by
  filter_upwards [residual_zero_common_ae μ r D hD h] with k hk
  intro w
  rw [hk, inner_zero_right]

end Residual
end Froehlich
