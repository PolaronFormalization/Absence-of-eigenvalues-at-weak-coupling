import Froehlich.Nodes.RS01ReverseMap

/-! Two-sided equivalence with the full original compressed energy domain.
All cancellations are proved through the actual physical embeddings. -/
noncomputable section
namespace Froehlich

theorem auxiliaryFullEmbedding_injective (n : ℕ) (e : ℝ) (p : GW.Space) (he : e ≤ 0) :
    Function.Injective (auxiliaryFullEmbedding n e p he) :=
  fockWeightedInclusion_injective (auxiliaryWeight n e p) (auxiliaryWeight_measurable n e p)
    (fun m K => auxiliaryWeight_ge_one n m e p he K)
    (fun m tau K => auxiliaryWeight_permutation n m e p tau K)

variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)

def auxiliaryToHighEnergy : AuxiliaryEnergySpace n e p he.2 →L[ℂ] HighEnergySpace (-p) n :=
  (auxiliaryToEnergy n e p he.2).codRestrict _ (by
    intro u
    apply (highEnergy_mem_iff (-p) n _).mpr
    apply energyEmbedding_injective (-p)
    rw [energyHighProjection_intertwines,auxiliaryToEnergy_physical n e p hn he,
      ← auxiliaryEnergyEmbedding_val]
    exact (highSector_mem_iff n (auxiliaryEnergyEmbedding n e p he.2 u)).mp
      (auxiliaryEnergyEmbedding n e p he.2 u).property)

def auxiliaryFromHighEnergy : HighEnergySpace (-p) n →L[ℂ] AuxiliaryEnergySpace n e p he.2 :=
  ((auxiliaryFromEnergyFull n e p he.2).comp (HighEnergySpace (-p) n).subtypeL).codRestrict _ (by
    intro u
    apply (auxiliaryEnergy_mem_iff n e p he.2 _).mpr
    apply auxiliaryFullEmbedding_injective n e p he.2
    change auxiliaryFullEmbedding n e p he.2
      (auxiliaryHighProjection n e p he.2 (auxiliaryFromEnergyFull n e p he.2 (u : EnergySpace (-p)))) =
      auxiliaryFullEmbedding n e p he.2 (auxiliaryFromEnergyFull n e p he.2 (u : EnergySpace (-p)))
    rw [auxiliaryHighProjection_physical,auxiliaryFromEnergyFull_physical n e p he,
      ← energyHighProjection_intertwines,(highEnergy_mem_iff (-p) n u).mp u.property])

theorem auxiliaryFromHighEnergy_to (u : AuxiliaryEnergySpace n e p he.2) :
    auxiliaryFromHighEnergy n e p he (auxiliaryToHighEnergy n e p hn he u) = u := by
  apply Subtype.ext
  apply auxiliaryFullEmbedding_injective n e p he.2
  change auxiliaryFullEmbedding n e p he.2
    (auxiliaryFromEnergyFull n e p he.2 (auxiliaryToEnergy n e p he.2 u)) =
      auxiliaryFullEmbedding n e p he.2 (u : AuxiliaryFullEnergy n e p he.2)
  rw [auxiliaryFromEnergyFull_physical n e p he,auxiliaryToEnergy_physical n e p hn he]

theorem auxiliaryToHighEnergy_from (u : HighEnergySpace (-p) n) :
    auxiliaryToHighEnergy n e p hn he (auxiliaryFromHighEnergy n e p he u) = u := by
  apply Subtype.ext
  apply energyEmbedding_injective (-p)
  change energyEmbedding (-p)
    (auxiliaryToEnergy n e p he.2 (auxiliaryFromHighEnergy n e p he u)) =
      energyEmbedding (-p) (u : EnergySpace (-p))
  rw [auxiliaryToEnergy_physical n e p hn he]
  change auxiliaryFullEmbedding n e p he.2
    (auxiliaryFromEnergyFull n e p he.2 (u : EnergySpace (-p))) = _
  exact auxiliaryFromEnergyFull_physical n e p he u

def auxiliaryHighEnergyEquivalence :
    AuxiliaryEnergySpace n e p he.2 ≃L[ℂ] HighEnergySpace (-p) n where
  toLinearEquiv :=
    { toLinearMap := (auxiliaryToHighEnergy n e p hn he).toLinearMap
      invFun := auxiliaryFromHighEnergy n e p he
      left_inv := auxiliaryFromHighEnergy_to n e p hn he
      right_inv := auxiliaryToHighEnergy_from n e p hn he }
  continuous_toFun := (auxiliaryToHighEnergy n e p hn he).continuous
  continuous_invFun := (auxiliaryFromHighEnergy n e p he).continuous

theorem auxiliaryHighEnergyEquivalence_norm_le (u : AuxiliaryEnergySpace n e p he.2) :
    ‖auxiliaryHighEnergyEquivalence n e p hn he u‖ ≤ Real.sqrt 3 * ‖u‖ :=
  auxiliaryToEnergy_norm_le n e p he.2 u

theorem auxiliaryHighEnergyEquivalence_symm_norm_le (u : HighEnergySpace (-p) n) :
    ‖(auxiliaryHighEnergyEquivalence n e p hn he).symm u‖ ≤ Real.sqrt (5/4 : ℝ) * ‖u‖ :=
  auxiliaryFromEnergyFull_norm_le n e p he.2 u

end Froehlich
