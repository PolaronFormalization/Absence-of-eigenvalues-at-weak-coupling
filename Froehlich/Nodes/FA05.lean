import Froehlich.Nodes.FA01

/-! FA05 clauses 1–3 reuse GW.isResolvent_unique, HasEigenvector.mem_realSpectrum,
and groundEnergy_eq_of_bottom. This file supplies the interval/image statement
for the very same unbounded-operator inverse predicate, not point spectrum. -/
namespace Froehlich
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem complexSpectrum_realInterval (A : H →ₗ.[ℂ] H) (b : ℝ) :
    complexSpectrum A ∩ (Complex.ofReal '' Set.Iio b) =
      Complex.ofReal '' (realSpectrum A ∩ Set.Iio b) := by
  ext z
  constructor
  · rintro ⟨hz, t, ht, rfl⟩
    exact ⟨t, ⟨hz, ht⟩, rfl⟩
  · rintro ⟨t, ⟨ht, htb⟩, rfl⟩
    exact ⟨ht, t, htb, rfl⟩

theorem realSpectralEquality_to_complex (A : H →ₗ.[ℂ] H) (b e : ℝ)
    (h : realSpectrum A ∩ Set.Iio b = {e}) :
    complexSpectrum A ∩ (Complex.ofReal '' Set.Iio b) = {(e : ℂ)} := by
  rw [complexSpectrum_realInterval, h, Set.image_singleton]
end Froehlich
