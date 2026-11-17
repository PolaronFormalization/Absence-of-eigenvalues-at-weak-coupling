import Froehlich.Nodes.MN02Inverse
import Froehlich.Nodes.MN02Vacuum

/-! MN02: the source free-coupling spectral case on the closed momentum ball. -/
noncomputable section
namespace Froehlich

theorem freeCoupling_resolvent (P : GW.Space) (lam : ℝ) (hl : lam < 1)
    (hv : lam ≠ ‖P‖^2) : lam ∈ realResolventSet (fiberHamiltonian 0 P) := by
  rw [fiberHamiltonian_zero_coupling]
  exact ⟨freeReciprocalAction P lam hl, freeReciprocalAction_isResolvent P lam hl hv⟩

theorem freeCoupling_groundEnergy (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    groundEnergy (fiberHamiltonian 0 P) = ‖P‖^2 := by
  have hlt : ‖P‖^2 < 1 := by nlinarith [norm_nonneg P]
  apply groundEnergy_eq_of_bottom (fiberHamiltonian_zero_vacuum P).mem_realSpectrum
  intro lam hlam
  exact freeCoupling_resolvent P lam (hlam.trans hlt) (ne_of_lt hlam)

theorem freeCoupling_spectrum (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    realSpectrum (fiberHamiltonian 0 P) ∩ Set.Iio 1 = {‖P‖^2} := by
  ext lam
  constructor
  · rintro ⟨hs,hl⟩
    change lam = ‖P‖^2
    by_contra hne
    exact hs (freeCoupling_resolvent P lam hl hne)
  · intro h
    have he : lam = ‖P‖^2 := h
    subst lam
    exact ⟨(fiberHamiltonian_zero_vacuum P).mem_realSpectrum,by
      change ‖P‖^2 < 1
      nlinarith [norm_nonneg P]⟩

theorem freeCoupling (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    groundEnergy (fiberHamiltonian 0 P) = ‖P‖^2 ∧
    groundEnergy (fiberHamiltonian 0 0) = 0 ∧
    realSpectrum (fiberHamiltonian 0 P) ∩ Set.Iio 1 = {‖P‖^2} := by
  refine ⟨freeCoupling_groundEnergy P hP,?_,freeCoupling_spectrum P hP⟩
  simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0)] using
    freeCoupling_groundEnergy (0 : GW.Space) (by norm_num)

/-- The free branch in the exact threshold normalization used by MN03. -/
theorem freeCoupling_mainCase (P : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    (realSpectrum (fiberHamiltonian 0 P) ∩
      Set.Iio (groundEnergy (fiberHamiltonian 0 0)+1) =
      {groundEnergy (fiberHamiltonian 0 P)}) ∧
    HasEigenvector (fiberHamiltonian 0 P) (groundEnergy (fiberHamiltonian 0 P)) := by
  have hz := (freeCoupling P hP).2.1
  rw [hz,zero_add,freeCoupling_groundEnergy P hP]
  exact ⟨freeCoupling_spectrum P hP,fiberHamiltonian_zero_vacuum P⟩

end Froehlich
