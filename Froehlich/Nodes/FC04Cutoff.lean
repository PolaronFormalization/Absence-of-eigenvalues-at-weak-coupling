import Froehlich.Nodes.FC04Fixed

/-! Fixed-energy product classes supported in a bounded external momentum set.
The indicator construction gives a global L² class and hence its restriction. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

def fixedEnergyRatio (P : GW.Space) (K : Set GW.Space) (n : ℕ)
    (p : GW.Space × GW.Fock.Coordinates n) : ℂ :=
  (K ×ˢ Set.univ).indicator (fun p =>
    ((energyWeight 0 n p.2 / energyWeight (P-p.1) n p.2 : ℝ) : ℂ)) p

theorem fixedEnergyRatio_measurable (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K) (n : ℕ) :
    Measurable (fixedEnergyRatio P K n) :=
  (Complex.continuous_ofReal.measurable.comp
    (((energyWeight_measurable 0 n).comp measurable_snd).div (movingEnergyWeight_measurable P n))).indicator
      (hK.prod MeasurableSet.univ)

theorem fixedEnergyRatio_bound (P : GW.Space) (K : Set GW.Space) (R : ℝ) (hR : 0 ≤ R)
    (hKR : ∀ k ∈ K, ‖k‖ ≤ R) (n : ℕ) (p : GW.Space × GW.Fock.Coordinates n) :
    ‖fixedEnergyRatio P K n p‖ ≤ fixedEnergyFieldConstant P R := by
  classical
  by_cases hp : p.1 ∈ K
  · have hpos := zero_lt_one.trans_le (energyWeight_ge_one (P-p.1) n p.2)
    have hp' : p ∈ K ×ˢ (Set.univ : Set (GW.Fock.Coordinates n)) := ⟨hp, Set.mem_univ _⟩
    simp only [fixedEnergyRatio, Set.indicator_of_mem hp',
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (zero_le_one.trans (energyWeight_ge_one 0 n p.2)) hpos.le)]
    exact (div_le_iff₀ hpos).mpr (fixedEnergyWeight_bound P p.1 R hR (hKR p.1 hp) n p.2)
  · have hp' : p ∉ K ×ˢ (Set.univ : Set (GW.Fock.Coordinates n)) := fun h => hp h.1
    simp only [fixedEnergyRatio, Set.indicator_of_notMem hp',
      norm_zero]
    exact Real.sqrt_nonneg _

def fixedEnergyProductClass (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)
    (x : OperatorGraphSpace P) (n : ℕ) :
    Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) :=
  GW.Analysis.boundedMultiplier (fixedEnergyRatio P K n) (fixedEnergyRatio_measurable P K hK n)
    (Eventually.of_forall (fixedEnergyRatio_bound P K R hR hKR n)) (movingEnergySectorClass P x n)

theorem fixedEnergyProductClass_norm (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)
    (x : OperatorGraphSpace P) (n : ℕ) :
    ‖fixedEnergyProductClass P K hK R hR hKR x n‖ ≤
      fixedEnergyFieldConstant P R * ‖movingEnergySectorClass P x n‖ := by
  let A : Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)) :=
    GW.Analysis.boundedMultiplier (fixedEnergyRatio P K n) (fixedEnergyRatio_measurable P K hK n)
      (Eventually.of_forall (fixedEnergyRatio_bound P K R hR hKR n))
  have hA : ‖A‖ ≤ fixedEnergyFieldConstant P R :=
    GW.Analysis.boundedMultiplier_opNorm_le (fixedEnergyRatio P K n)
      (fixedEnergyRatio_measurable P K hK n) (Real.sqrt_nonneg _)
      (Eventually.of_forall (fixedEnergyRatio_bound P K R hR hKR n))
  exact (A.le_opNorm (movingEnergySectorClass P x n)).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))

def fixedEnergyAmbientSectorField (P : GW.Space) (K : Set GW.Space) (hK : MeasurableSet K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : ∀ k ∈ K, ‖k‖ ≤ R)
    (x : OperatorGraphSpace P) (n : ℕ) : Lp (GW.Fock.AmbientSector n) 2 (volume : Measure GW.Space) :=
  (GW.Fock.productUnitary volume (GW.Fock.sectorMeasure n)).symm
    (fixedEnergyProductClass P K hK R hR hKR x n)

end Froehlich
