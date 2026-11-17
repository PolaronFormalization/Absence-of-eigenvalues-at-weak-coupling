import Froehlich.Nodes.FD02Weights

/-! Operations on the actual generic weighted domains. The sector projection
is transported through the retained weighted-coordinate isometry. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich
section Weights
variable (w : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n k, 1 ≤ w n k)
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, w n (fun i => k (τ i)) = w n k)

def weightedSectorProjection (m : ℕ) :
    GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) →L[ℂ]
      GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) :=
  (fockWeightedCoordinates w hw hw1 hp).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((sectorProjection m).comp (fockWeightedCoordinates w hw hw1 hp).toLinearIsometry.toContinuousLinearMap)

theorem weightedSectorProjection_norm_le (m : ℕ)
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    ‖weightedSectorProjection w hw hw1 hp m u‖ ≤ ‖u‖ := by
  change ‖(fockWeightedCoordinates w hw hw1 hp).symm
    (sectorProjection m (fockWeightedCoordinates w hw hw1 hp u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (sectorProjection_norm_le m _).trans_eq ((fockWeightedCoordinates w hw hw1 hp).norm_map u)

theorem weightedSectorProjection_intertwines (m : ℕ)
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    fockWeightedInclusion w hw hw1 hp (weightedSectorProjection w hw hw1 hp m u) =
      sectorProjection m (fockWeightedInclusion w hw hw1 hp u) := by
  let G := fockWeightSectorGraph w hw hw1 hp
  change sumGraphEmbedding G
    (fockWeightedCoordinates w hw hw1 hp ((fockWeightedCoordinates w hw hw1 hp).symm
      (sectorProjection m (fockWeightedCoordinates w hw hw1 hp u)))) =
    sectorProjection m (sumGraphEmbedding G (fockWeightedCoordinates w hw hw1 hp u))
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext n
  change (G n).embedding ((sectorProjection m (fockWeightedCoordinates w hw hw1 hp u)) n) = _
  rw [sectorProjection_apply, sectorProjection_apply]
  by_cases hn : n = m
  · subst n
    simp only [lp.single_apply_self]
    rfl
  · rw [lp.single_apply_ne _ _ _ hn, lp.single_apply_ne _ _ _ hn, map_zero]

theorem weightedDomain_sectorProjection_mem (m : ℕ) (u : GW.Fock.Carrier)
    (hu : u ∈ (fockWeightedGraph w hw hw1 hp).domain) :
    sectorProjection m u ∈ (fockWeightedGraph w hw hw1 hp).domain := by
  let x : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) := ⟨u,hu⟩
  have he := weightedSectorProjection_intertwines w hw hw1 hp m x
  rw [fockWeightedInclusion_apply] at he
  have hx : fockWeightedInclusion w hw hw1 hp x = u := fockWeightedInclusion_apply w hw hw1 hp x
  rw [hx] at he
  exact he ▸ (weightedSectorProjection w hw hw1 hp m x).property

end Weights
end Froehlich
