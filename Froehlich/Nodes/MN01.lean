import Froehlich.Nodes.SM01
import Froehlich.Nodes.SP03

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

/-- The exhaustive low/near-threshold split excludes the full real spectrum,
with the boundary lambda=L assigned to the near-threshold case. -/
theorem nonzeroCoupling_mainCase (g : ℝ) (P : GW.Space) (hg0 : g ≠ 0)
    (hP : ‖P‖ ≤ 1/4) (hnum : SM01NumericalGuards g)
    (hL : (7/8 : ℝ) ≤ nonvacuumThreshold g)
    (heLower : -(1/8 : ℝ) ≤ groundEnergy (fiberHamiltonian g 0))
    (heUpper : groundEnergy (fiberHamiltonian g 0) ≤ 0)
    (hVac : SM01VacuumData g P) (hPos : SM01PositivityData g) :
    (realSpectrum (fiberHamiltonian g P) ∩ Set.Iio (groundEnergy (fiberHamiltonian g 0)+1) =
      {groundEnergy (fiberHamiltonian g P)}) ∧
    HasEigenvector (fiberHamiltonian g P) (groundEnergy (fiberHamiltonian g P)) := by
  obtain ⟨he,hquarter,hgroundLower,hquadratic,hpositive⟩ := hPos
  refine ⟨?_,hVac.2.2.2⟩
  ext lam
  constructor
  · rintro ⟨hspectrum,hlam⟩
    change lam = groundEnergy (fiberHamiltonian g P)
    by_contra hne
    by_cases hlow : lam < nonvacuumThreshold g
    · have hin : lam ∈ realSpectrum (fiberHamiltonian g P) ∩ Set.Iio (nonvacuumThreshold g) :=
        ⟨hspectrum,hlow⟩
      rw [hVac.2.2.1] at hin
      exact hne hin
    · have hnear : nonvacuumThreshold g ≤ lam := le_of_not_gt hlow
      let eps := groundEnergy (fiberHamiltonian g 0)+1-lam
      have heps : 0 < eps := sub_pos.mpr hlam
      have hepsUpper : eps ≤ 1/8 := by dsimp [eps]; linarith
      have hd : (1/2 : ℝ) ≤ onePhononVacuumDenominator (groundEnergy (fiberHamiltonian g 0)) eps P := by
        have hmargin := sm01_window_denominator _ ‖P‖ eps heLower (norm_nonneg P) hP hepsUpper
        change (1/2 : ℝ) ≤ 1+groundEnergy (fiberHamiltonian g 0)-‖P‖^2-eps
        linarith
      have hSP := (finalSP03 g (groundEnergy (fiberHamiltonian g 0)) eps P hquarter hgroundLower
        heUpper heps.le hquadratic hd hnum.2.2.2.2.2).2.2.2
      have hres : groundEnergy (fiberHamiltonian g 0)+1-eps ∈ realResolventSet (fiberHamiltonian g P) :=
        hSP (hpositive P hP) heps
      have heq : groundEnergy (fiberHamiltonian g 0)+1-eps = lam := by dsimp [eps]; ring
      rw [heq] at hres
      exact hspectrum hres
  · intro h
    have heq : lam = groundEnergy (fiberHamiltonian g P) := h
    subst lam
    refine ⟨hVac.2.2.2.mem_realSpectrum,?_⟩
    have hu := hVac.1
    change groundEnergy (fiberHamiltonian g P) < groundEnergy (fiberHamiltonian g 0)+1
    nlinarith [norm_nonneg P]

/-- The nonzero-coupling branch uses precisely the cutoff selected in SM01. -/
theorem finalMN01 : ∃ s : ℝ, 0 < s ∧ ∀ (g : ℝ) (P : GW.Space),
    g ≠ 0 → |g| < s → ‖P‖ ≤ 1/4 →
    (realSpectrum (fiberHamiltonian g P) ∩ Set.Iio (groundEnergy (fiberHamiltonian g 0)+1) =
      {groundEnergy (fiberHamiltonian g P)}) ∧
    HasEigenvector (fiberHamiltonian g P) (groundEnergy (fiberHamiltonian g P)) := by
  obtain ⟨I,K,Cm,CW,CD,hI,hK,hCm,hCW,hCD,hIntegral,hKernel,hs,hData⟩ := finalSM01
  refine ⟨sm01CouplingCutoff I K Cm,hs,?_⟩
  intro g P hg0 hgs hP
  obtain ⟨hnum,_hAux,hL,heLower,heUpper,hVac,_hWeighted,hPos⟩ := hData g hgs
  exact nonzeroCoupling_mainCase g P hg0 hP hnum hL heLower heUpper (hVac P hP) (hPos hg0)

end Froehlich
