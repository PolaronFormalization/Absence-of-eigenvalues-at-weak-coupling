import Froehlich.Nodes.FD02WeightedConjugation

/-! Semilinear packaging of actual physical weighted conjugation. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem ambientConjugation_add (n : ℕ) (u v : GW.Fock.AmbientSector n) :
    ambientConjugation n (u+v) = ambientConjugation n u + ambientConjugation n v := by
  exact (Complex.conjCLE.toContinuousLinearMap.compLpL 2 (GW.Fock.sectorMeasure n)).map_add u v

theorem ambientConjugation_smul (n : ℕ) (c : ℂ) (u : GW.Fock.AmbientSector n) :
    ambientConjugation n (c • u) = (starRingEnd ℂ) c • ambientConjugation n u := by
  apply Lp.ext
  filter_upwards [ambientConjugation_ae n (c • u), ambientConjugation_ae n u,
    Lp.coeFn_smul c u, Lp.coeFn_smul ((starRingEnd ℂ) c) (ambientConjugation n u)] with k hc hu hs ht
  simp only [Pi.smul_apply, smul_eq_mul] at hs ht
  rw [hc, hs, map_mul, ht, hu]

theorem sectorConjugation_add (n : ℕ) (u v : GW.Fock.Sector n) :
    sectorConjugation n (u+v) = sectorConjugation n u + sectorConjugation n v := by
  apply (physicalSector n).injective
  rw [map_add, sectorConjugation_physical, sectorConjugation_physical,
    sectorConjugation_physical, map_add, ambientConjugation_add]

theorem sectorConjugation_smul (n : ℕ) (c : ℂ) (u : GW.Fock.Sector n) :
    sectorConjugation n (c • u) = (starRingEnd ℂ) c • sectorConjugation n u := by
  apply (physicalSector n).injective
  rw [map_smul, sectorConjugation_physical, sectorConjugation_physical,
    map_smul, ambientConjugation_smul]

theorem fockConjugation_add (u v : GW.Fock.Carrier) :
    fockConjugation (u+v) = fockConjugation u + fockConjugation v := by
  apply lp.ext
  funext n
  exact sectorConjugation_add n (u n) (v n)

theorem fockConjugation_smul (c : ℂ) (u : GW.Fock.Carrier) :
    fockConjugation (c • u) = (starRingEnd ℂ) c • fockConjugation u := by
  apply lp.ext
  funext n
  exact sectorConjugation_smul n c (u n)

section Weights
variable (w : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n k, 1 ≤ w n k)
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, w n (fun i => k (τ i)) = w n k)

def weightedConjugationLinear :
    GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) →ₗ⋆[ℂ]
      GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) where
  toFun := weightedConjugation w hw hw1 hp
  map_add' u v := by
    apply (fockWeightedCoordinates w hw hw1 hp).injective
    change fockWeightedCoordinates w hw hw1 hp
      ((fockWeightedCoordinates w hw hw1 hp).symm (fockConjugation (fockWeightedCoordinates w hw hw1 hp (u+v)))) = _
    rw [LinearIsometryEquiv.apply_symm_apply, map_add, fockConjugation_add, map_add]
    simp only [weightedConjugation, LinearIsometryEquiv.apply_symm_apply]
  map_smul' c u := by
    apply (fockWeightedCoordinates w hw hw1 hp).injective
    change fockWeightedCoordinates w hw hw1 hp
      ((fockWeightedCoordinates w hw hw1 hp).symm (fockConjugation (fockWeightedCoordinates w hw hw1 hp (c • u)))) = _
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, fockConjugation_smul, map_smul]
    simp only [weightedConjugation, LinearIsometryEquiv.apply_symm_apply, RingHom.id_apply]

def weightedConjugationIsometry :
    GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) →ₗᵢ⋆[ℂ]
      GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) where
  toLinearMap := weightedConjugationLinear w hw hw1 hp
  norm_map' := weightedConjugation_norm w hw hw1 hp

theorem weightedDomain_conjugation_mem (u : GW.Fock.Carrier)
    (hu : u ∈ (fockWeightedGraph w hw hw1 hp).domain) :
    fockConjugation u ∈ (fockWeightedGraph w hw hw1 hp).domain := by
  let x : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) := ⟨u,hu⟩
  have he := weightedConjugation_physical w hw hw1 hp x
  change weightedFockValue w hw hw1 hp (weightedConjugation w hw hw1 hp x) = fockConjugation u at he
  exact he ▸ (weightedConjugation w hw hw1 hp x).property

end Weights
end Froehlich
