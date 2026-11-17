import GW.Fock.FockAmplification

/-! MS01: specialize the retained rectangle-density criterion to the physical
momentum measure and sector configuration measure. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Froehlich

theorem rectangle_density (n : ℕ)
    (V : Submodule ℂ (Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n))))
    (hV : IsClosed (V : Set (Lp ℂ 2 ((volume : Measure GW.Space).prod (GW.Fock.sectorMeasure n)))))
    (hrect : ∀ (A : Set GW.Space) (B : Set (GW.Fock.Coordinates n))
      (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hAf : volume A ≠ ∞) (hBf : GW.Fock.sectorMeasure n B ≠ ∞) (z : ℂ),
      indicatorConstLp 2 (hA.prod hB)
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hAf hBf) z ∈ V) :
    V = ⊤ :=
  GW.Fock.rectangle_dense_criterion volume (GW.Fock.sectorMeasure n) V hV hrect
end Froehlich
