import Froehlich.Nodes.FC04Cutoff

/-! Fixed-energy sector reconstruction, supported on the bounded external set. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace Classical
namespace Froehlich

theorem fixedEnergyProductClass_physical (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)
    (x : OperatorGraphSpace P) (n : ℕ) :
    fixedEnergyProductClass P K hK R hR hKR x n
      =ᵐ[(volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)]
        (fun p => if p.1 ∈ K then
          (energyWeight 0 n p.2 : ℂ) * (Real.sqrt (n+1 : ℕ) : ℂ) *
            physicalSector (n+1) (graphEmbedding P x (n+1))
              ((GW.Fock.splitCoordinates n 0).symm p) else 0) := by
  classical
  filter_upwards [GW.Analysis.boundedMultiplier_ae (fixedEnergyRatio P K n)
    (fixedEnergyRatio_measurable P K hK n)
    (Eventually.of_forall (fixedEnergyRatio_bound P K R hR hKR n)) (movingEnergySectorClass P x n),
    movingEnergySectorClass_ae P x n] with p hp hm
  have he : fixedEnergyProductClass P K hK R hR hKR x n p =
      fixedEnergyRatio P K n p • movingEnergySectorClass P x n p := hp.symm
  rw [he, hm]
  simp only [smul_eq_mul]
  by_cases hk : p.1 ∈ K
  · have hp' : p ∈ K ×ˢ (Set.univ : Set (GW.Fock.Coordinates n)) := ⟨hk,Set.mem_univ _⟩
    simp only [fixedEnergyRatio, Set.indicator_of_mem hp', if_pos hk, movingEnergySection,
      Complex.ofReal_div]
    have hn : (energyWeight (P-p.1) n p.2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans_le (energyWeight_ge_one _ _ _)))
    field_simp [hn]
    <;> ring
  · have hp' : p ∉ K ×ˢ (Set.univ : Set (GW.Fock.Coordinates n)) := fun h => hk h.1
    simp only [fixedEnergyRatio, Set.indicator_of_notMem hp', zero_mul, if_neg hk]

theorem fixedEnergyAmbientSectorField_physical (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (x : OperatorGraphSpace P) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∀ n,
      (fun L => (energyWeight 0 n L : ℂ) * physicalSector n
        ((K.indicator (annihilationField (freeGraphNumberCoordinates P x)) k) n) L)
        =ᵐ[GW.Fock.sectorMeasure n] fixedEnergyAmbientSectorField P K hK R hR hKR x n k := by
  classical
  have hs (n : ℕ) := productUnitary_sections volume (GW.Fock.sectorMeasure n)
    (fixedEnergyAmbientSectorField P K hK R hR hKR x n)
  have hc (n : ℕ) := Measure.ae_ae_of_ae_prod (fixedEnergyProductClass_physical P K hK R hR hKR x n)
  have ha := annihilationField_representative_common_ae (freeGraphNumberCoordinates P x)
  rw [freeGraphNumberCoordinates_embedding] at ha
  filter_upwards [ae_all_iff.mpr hs, ae_all_iff.mpr hc, ha] with k hs hc ha
  intro n
  have he : GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n)
      (fixedEnergyAmbientSectorField P K hK R hR hKR x n) =
      fixedEnergyProductClass P K hK R hR hKR x n :=
    (GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n)).apply_symm_apply _
  have hn := hs n
  rw [he] at hn
  have han := ha n
  rw [kernelRepresentative_physical] at han
  filter_upwards [hn, hc n, han,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure n)] with L hL hcL haL hzero
  by_cases hk : k ∈ K
  · rw [Set.indicator_of_mem hk]
    rw [← hL, hcL, if_pos hk, haL]
    simp only [smul_eq_mul]
    dsimp only [physicalSector]
    ring
  · rw [Set.indicator_of_notMem hk]
    change (energyWeight 0 n L : ℂ) * physicalSector n (0 : GW.Fock.Sector n) L = _
    rw [map_zero]
    simp only [Pi.zero_apply] at hzero
    rw [hzero, mul_zero]
    have hc0 := hcL
    simp only [if_neg hk] at hc0
    exact hc0.symm.trans hL

end Froehlich
