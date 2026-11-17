import Froehlich.Nodes.FD02WeightedConjugation
import Froehlich.Nodes.FC01Multipliers

/-! One-direction comparison of actual weighted domains. The bounded ratio
is clipped globally and agrees with the literal ratio almost everywhere. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich
section Comparison
variable (w v : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n k, 1 ≤ w n k)
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, w n (fun i => k (τ i)) = w n k)
  (hv : ∀ n, Measurable (v n)) (hv1 : ∀ n k, 1 ≤ v n k)
  (hvp : ∀ n (τ : Equiv.Perm (Fin n)) k, v n (fun i => k (τ i)) = v n k)
  (C : ℝ) (hC : 0 ≤ C)

def comparisonRatio (n : ℕ) (k : GW.Fock.Coordinates n) : ℝ := min C (w n k / v n k)

include hw hv in
theorem comparisonRatio_measurable (n : ℕ) : Measurable (comparisonRatio w v C n) :=
  measurable_const.min ((hw n).div (hv n))

include hw1 hv1 hC in
theorem comparisonRatio_bound (n : ℕ) (k : GW.Fock.Coordinates n) :
    |comparisonRatio w v C n k| ≤ C := by
  change |min C (w n k / v n k)| ≤ C
  rw [abs_of_nonneg (le_min hC (div_nonneg (zero_le_one.trans (hw1 n k))
    (zero_le_one.trans (hv1 n k))))]
  exact min_le_left _ _

include hp hvp in
theorem comparisonRatio_permutation (n : ℕ) (τ : Equiv.Perm (Fin n)) (k : GW.Fock.Coordinates n) :
    comparisonRatio w v C n (fun i => k (τ i)) = comparisonRatio w v C n k := by
  simp only [comparisonRatio, hp n τ k, hvp n τ k]

def weightComparisonMap :
    GW.Spaces.WeightedDomain (fockWeightedGraph v hv hv1 hvp) →L[ℂ]
      GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) :=
  (fockWeightedCoordinates w hw hw1 hp).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((boundedFockAction (comparisonRatio w v C) (comparisonRatio_measurable w v hw hv C) C hC
      (comparisonRatio_bound w v hw1 hv1 C hC) (comparisonRatio_permutation w v hp hvp C)).comp
        (fockWeightedCoordinates v hv hv1 hvp).toLinearIsometry.toContinuousLinearMap)

theorem weightComparisonMap_bound
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph v hv hv1 hvp)) :
    ‖weightComparisonMap w v hw hw1 hp hv hv1 hvp C hC u‖ ≤ C * ‖u‖ := by
  have h := GW.Spaces.diagonal_norm_bound
    (boundedFockSector (comparisonRatio w v C) (comparisonRatio_measurable w v hw hv C) C
      (comparisonRatio_bound w v hw1 hv1 C hC) (comparisonRatio_permutation w v hp hvp C)) hC
    (boundedFockSector_norm (comparisonRatio w v C) (comparisonRatio_measurable w v hw hv C) C hC
      (comparisonRatio_bound w v hw1 hv1 C hC) (comparisonRatio_permutation w v hp hvp C))
    (fockWeightedCoordinates v hv hv1 hvp u)
  change ‖(fockWeightedCoordinates w hw hw1 hp).symm
    (boundedFockAction (comparisonRatio w v C) (comparisonRatio_measurable w v hw hv C) C hC
      (comparisonRatio_bound w v hw1 hv1 C hC) (comparisonRatio_permutation w v hp hvp C)
        (fockWeightedCoordinates v hv hv1 hvp u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  change ‖boundedFockAction (comparisonRatio w v C) (comparisonRatio_measurable w v hw hv C) C hC
    (comparisonRatio_bound w v hw1 hv1 C hC) (comparisonRatio_permutation w v hp hvp C)
      (fockWeightedCoordinates v hv hv1 hvp u)‖ ≤ C * ‖fockWeightedCoordinates v hv hv1 hvp u‖ at h
  rw [LinearIsometryEquiv.norm_map] at h
  exact h

theorem weightComparisonMap_physical
    (hdom : ∀ n, (fun k => w n k) ≤ᵐ[GW.Fock.sectorMeasure n] (fun k => C * v n k))
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph v hv hv1 hvp)) :
    weightedFockValue w hw hw1 hp (weightComparisonMap w v hw hw1 hp hv hv1 hvp C hC u) =
      weightedFockValue v hv hv1 hvp u := by
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have ht := fockWeightedCoordinates_physical w hw hw1 hp
    (weightComparisonMap w v hw hw1 hp hv hv1 hvp C hC u) n
  have he : fockWeightedCoordinates w hw hw1 hp
      (weightComparisonMap w v hw hw1 hp hv hv1 hvp C hC u) =
      boundedFockAction (comparisonRatio w v C) (comparisonRatio_measurable w v hw hv C) C hC
        (comparisonRatio_bound w v hw1 hv1 C hC) (comparisonRatio_permutation w v hp hvp C)
          (fockWeightedCoordinates v hv hv1 hvp u) := by
    change fockWeightedCoordinates w hw hw1 hp ((fockWeightedCoordinates w hw hw1 hp).symm _) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [he] at ht
  have ha := boundedFockAction_ae (comparisonRatio w v C) (comparisonRatio_measurable w v hw hv C) C hC
    (comparisonRatio_bound w v hw1 hv1 C hC) (comparisonRatio_permutation w v hp hvp C)
    (fockWeightedCoordinates v hv hv1 hvp u) n
  filter_upwards [ht, ha, fockWeightedCoordinates_physical v hv hv1 hvp u n, hdom n]
    with k ht ha hvu hdom
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (hw1 n k))))
  have hratio : comparisonRatio w v C n k = w n k / v n k :=
    min_eq_right ((div_le_iff₀ (zero_lt_one.trans_le (hv1 n k))).mpr hdom)
  rw [ht, ← ha, hratio, ← hvu]
  simp only [smul_eq_mul, Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (hv1 n k)))]
  <;> ring

end Comparison
end Froehlich
