import Froehlich.Nodes.FD02WeightedSymmetries

/-! Actual physical conjugation on the real weighted domains, using native
sector conjugation and the retained weighted-coordinate isometry. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

def fockConjugation (u : GW.Fock.Carrier) : GW.Fock.Carrier :=
  ⟨fun n => sectorConjugation n (u n), (GW.Analysis.memℓp_two_iff_sq _).mpr (by
    simpa only [sectorConjugation_norm] using (GW.Analysis.memℓp_two_iff_sq _).mp u.property)⟩

theorem fockConjugation_norm (u : GW.Fock.Carrier) : ‖fockConjugation u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [GW.Fock.carrier_norm_sq, GW.Fock.carrier_norm_sq]
  exact tsum_congr (fun n => congrArg (fun r : ℝ => r^2) (sectorConjugation_norm n (u n)))

theorem fockConjugation_physical (u : GW.Fock.Carrier) (n : ℕ) :
    physicalSector n (fockConjugation u n) =ᵐ[GW.Fock.sectorMeasure n]
      (fun k => (starRingEnd ℂ) (physicalSector n (u n) k)) := by
  change physicalSector n (sectorConjugation n (u n)) =ᵐ[_] _
  rw [sectorConjugation_physical]
  exact ambientConjugation_ae n _

theorem fockConjugation_involutive : Function.Involutive fockConjugation := by
  intro u
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  filter_upwards [fockConjugation_physical (fockConjugation u) n,
    fockConjugation_physical u n] with k hk hu
  rw [hk, hu, starRingEnd_self_apply]

section Weights
variable (w : ∀ n, GW.Fock.Coordinates n → ℝ)
  (hw : ∀ n, Measurable (w n)) (hw1 : ∀ n k, 1 ≤ w n k)
  (hp : ∀ n (τ : Equiv.Perm (Fin n)) k, w n (fun i => k (τ i)) = w n k)

theorem fockWeightedCoordinates_physical
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) (n : ℕ) :
    (fun k => (w n k : ℂ) * physicalSector n (weightedFockValue w hw hw1 hp u n) k)
      =ᵐ[GW.Fock.sectorMeasure n]
        physicalSector n (fockWeightedCoordinates w hw hw1 hp u n) := by
  let a : (fockWeightedGraph w hw hw1 hp).domain := u
  let s := GW.Fock.operatorSumInput GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) a n
  have he := GW.Fock.operatorSum_apply_component GW.Fock.Sector
    (sectorWeightPartial (fockWeightSectorGraph w hw hw1 hp)) a n
  change (fockWeightSectorGraph w hw hw1 hp n).product s =
    fockWeightedCoordinates w hw hw1 hp u n at he
  have h := fockSectorWeightProduct_ae w hw hw1 hp n s
  rw [he] at h
  have hs : (s : GW.Fock.Sector n) = weightedFockValue w hw hw1 hp u n := rfl
  rw [hs] at h
  simpa only [smul_eq_mul] using h

def weightedConjugation (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp) :=
  (fockWeightedCoordinates w hw hw1 hp).symm
    (fockConjugation (fockWeightedCoordinates w hw hw1 hp u))

theorem weightedConjugation_norm (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    ‖weightedConjugation w hw hw1 hp u‖ = ‖u‖ := by
  change ‖(fockWeightedCoordinates w hw hw1 hp).symm
    (fockConjugation (fockWeightedCoordinates w hw hw1 hp u))‖ = _
  rw [LinearIsometryEquiv.norm_map, fockConjugation_norm, LinearIsometryEquiv.norm_map]

theorem weightedConjugation_involutive : Function.Involutive (weightedConjugation w hw hw1 hp) := by
  intro u
  change (fockWeightedCoordinates w hw hw1 hp).symm (fockConjugation
    (fockWeightedCoordinates w hw hw1 hp ((fockWeightedCoordinates w hw hw1 hp).symm
      (fockConjugation (fockWeightedCoordinates w hw hw1 hp u))))) = u
  rw [LinearIsometryEquiv.apply_symm_apply, fockConjugation_involutive,
    LinearIsometryEquiv.symm_apply_apply]

theorem weightedConjugation_physical
    (u : GW.Spaces.WeightedDomain (fockWeightedGraph w hw hw1 hp)) :
    weightedFockValue w hw hw1 hp (weightedConjugation w hw hw1 hp u) =
      fockConjugation (weightedFockValue w hw hw1 hp u) := by
  apply lp.ext
  funext n
  apply (physicalSector n).injective
  apply Lp.ext
  have hc := fockWeightedCoordinates_physical w hw hw1 hp (weightedConjugation w hw hw1 hp u) n
  have he : fockWeightedCoordinates w hw hw1 hp (weightedConjugation w hw hw1 hp u) =
      fockConjugation (fockWeightedCoordinates w hw hw1 hp u) :=
    (fockWeightedCoordinates w hw hw1 hp).apply_symm_apply _
  rw [he] at hc
  filter_upwards [hc, fockWeightedCoordinates_physical w hw hw1 hp u n,
    fockConjugation_physical (fockWeightedCoordinates w hw hw1 hp u) n,
    fockConjugation_physical (weightedFockValue w hw hw1 hp u) n] with k hc hu hf hv
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (hw1 n k))))
  rw [hc, hf, ← hu, hv, map_mul, Complex.conj_ofReal]

end Weights
end Froehlich
