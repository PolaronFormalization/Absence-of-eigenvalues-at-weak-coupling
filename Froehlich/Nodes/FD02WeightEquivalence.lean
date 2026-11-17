import Froehlich.Nodes.FD02WeightComparison

/-! Two-sided comparison of the same physical weighted domains. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich
section Weights
variable (w v : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n k, 1 ≤ w n k)
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, w n (fun i => k (τ i)) = w n k)
  (hv : ∀ n, Measurable (v n)) (hv1 : ∀ n k, 1 ≤ v n k)
  (hvp : ∀ n (τ : Equiv.Perm (Fin n)) k, v n (fun i => k (τ i)) = v n k)

theorem weightComparison_domain_subset (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ n, (fun k => w n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => C * v n k)) :
    (fockWeightedGraph v hv hv1 hvp).domain ≤ (fockWeightedGraph w hw hw1 hp).domain := by
  intro u hu
  let x : GW.Spaces.WeightedDomain (fockWeightedGraph v hv hv1 hvp) := ⟨u,hu⟩
  have he := weightComparisonMap_physical w v hw hw1 hp hv hv1 hvp C hC hdom x
  change weightedFockValue w hw hw1 hp (weightComparisonMap w v hw hw1 hp hv hv1 hvp C hC x) = u at he
  exact he ▸ (weightComparisonMap w v hw hw1 hp hv hv1 hvp C hC x).property

theorem weightComparison_inverse_bound (c : ℝ) (hc : 0 < c)
    (hlower : ∀ n, (fun k => c * v n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => w n k)) :
    ∀ n, (fun k => v n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => (1/c) * w n k) := by
  intro n
  filter_upwards [hlower n] with k hk
  calc
    v n k = (1/c) * (c * v n k) := by field_simp [ne_of_gt hc]
    _ ≤ (1/c) * w n k := mul_le_mul_of_nonneg_left hk (by positivity)

theorem equivalentWeights_domain_eq (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
    (hlower : ∀ n, (fun k => c * v n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => w n k))
    (hupper : ∀ n, (fun k => w n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => C * v n k)) :
    (fockWeightedGraph w hw hw1 hp).domain = (fockWeightedGraph v hv hv1 hvp).domain := by
  apply le_antisymm
  · exact weightComparison_domain_subset v w hv hv1 hvp hw hw1 hp (1/c) (by positivity)
      (weightComparison_inverse_bound w v c hc hlower)
  · exact weightComparison_domain_subset w v hw hw1 hp hv hv1 hvp C (hc.le.trans hcC) hupper

theorem comparisonMap_cancel (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hupper : ∀ n, (fun k => w n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => C * v n k))
    (hreverse : ∀ n, (fun k => v n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => D * w n k))
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph v hv hv1 hvp)) :
    weightComparisonMap v w hv hv1 hvp hw hw1 hp D hD
      (weightComparisonMap w v hw hw1 hp hv hv1 hvp C hC u) = u := by
  apply fockWeightedInclusion_injective v hv hv1 hvp
  rw [fockWeightedInclusion_apply, fockWeightedInclusion_apply,
    weightComparisonMap_physical v w hv hv1 hvp hw hw1 hp D hD hreverse,
    weightComparisonMap_physical w v hw hw1 hp hv hv1 hvp C hC hupper]

def weightEquivalence (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
    (hlower : ∀ n, (fun k => c * v n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => w n k))
    (hupper : ∀ n, (fun k => w n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => C * v n k)) :
    GW.Spaces.WeightedDomain (fockWeightedGraph v hv hv1 hvp) ≃L[ℂ]
      GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) where
  toLinearEquiv :=
    { toLinearMap := (weightComparisonMap w v hw hw1 hp hv hv1 hvp C (hc.le.trans hcC)).toLinearMap
      invFun := weightComparisonMap v w hv hv1 hvp hw hw1 hp (1/c) (by positivity)
      left_inv := comparisonMap_cancel w v hw hw1 hp hv hv1 hvp C (1/c) (hc.le.trans hcC)
        (by positivity) hupper (weightComparison_inverse_bound w v c hc hlower)
      right_inv := comparisonMap_cancel v w hv hv1 hvp hw hw1 hp (1/c) C (by positivity)
        (hc.le.trans hcC) (weightComparison_inverse_bound w v c hc hlower) hupper }
  continuous_toFun := (weightComparisonMap w v hw hw1 hp hv hv1 hvp C (hc.le.trans hcC)).continuous
  continuous_invFun := (weightComparisonMap v w hv hv1 hvp hw hw1 hp (1/c) (by positivity)).continuous

theorem weightEquivalence_norm_bounds (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C)
    (hlower : ∀ n, (fun k => c * v n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => w n k))
    (hupper : ∀ n, (fun k => w n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => C * v n k))
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph v hv hv1 hvp)) :
    c * ‖u‖ ≤ ‖weightEquivalence w v hw hw1 hp hv hv1 hvp c C hc hcC hlower hupper u‖ ∧
      ‖weightEquivalence w v hw hw1 hp hv hv1 hvp c C hc hcC hlower hupper u‖ ≤ C * ‖u‖ := by
  let E := weightEquivalence w v hw hw1 hp hv hv1 hvp c C hc hcC hlower hupper
  have hb := weightComparisonMap_bound v w hv hv1 hvp hw hw1 hp (1/c) (by positivity) (E u)
  have he : weightComparisonMap v w hv hv1 hvp hw hw1 hp (1/c) (by positivity) (E u) = u :=
    E.symm_apply_apply u
  rw [he] at hb
  refine ⟨?_, weightComparisonMap_bound w v hw hw1 hp hv hv1 hvp C (hc.le.trans hcC) u⟩
  calc
    c * ‖u‖ ≤ c * ((1/c) * ‖E u‖) := mul_le_mul_of_nonneg_left hb hc.le
    _ = ‖E u‖ := by field_simp [ne_of_gt hc]

end Weights
end Froehlich
