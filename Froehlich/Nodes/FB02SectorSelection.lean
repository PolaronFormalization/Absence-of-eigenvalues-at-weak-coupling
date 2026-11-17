import Froehlich.Nodes.FB02A

/-! Particle-number selection for actual cutoff fields and their norm limit. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem creationRestriction_sector_zero (f : GW.OnePhonon) (x : NumberFormSpace) :
    creationRestriction f x 0 = 0 := by
  rw [creationRestriction_apply,GW.Fock.ordinaryCreation_zero]

theorem creationRestriction_sector_succ (f : GW.OnePhonon) (x : NumberFormSpace) (n : ℕ) :
    creationRestriction f x (n+1) =
      GW.Fock.sectorCreation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n (numberFormEmbedding x n) := by
  rw [creationRestriction_apply,GW.Fock.ordinaryCreation_succ]
  rfl

theorem annihilationRestriction_sector (f : GW.OnePhonon) (x : NumberFormSpace) (n : ℕ) :
    annihilationRestriction f x n =
      GW.Fock.sectorAnnihilation GW.Fock.ordinarySectorKernel (GW.Fock.ordinaryKernel f) n
        (numberFormEmbedding x (n+1)) := by
  rw [annihilationRestriction_apply,GW.Fock.ordinaryAnnihilation_apply]
  rfl

theorem fieldRestriction_sector_eq_zero (f : GW.OnePhonon) (x : NumberFormSpace)
    (m n : ℕ) (v : GW.Fock.Carrier) (hx : numberFormEmbedding x = sectorProjection m v)
    (hnm : n ≠ m+1) (hmn : m ≠ n+1) : fieldRestriction f x n = 0 := by
  have hz (j : ℕ) (hj : j ≠ m) : numberFormEmbedding x j = 0 := by
    rw [hx,sectorProjection_apply]
    exact lp.single_apply_ne _ _ _ hj
  change annihilationRestriction f x n + creationRestriction f x n = 0
  rw [annihilationRestriction_sector,hz (n+1) (Ne.symm hmn),map_zero,zero_add]
  cases n with
  | zero => exact creationRestriction_sector_zero f x
  | succ n =>
    rw [creationRestriction_sector_succ,hz n (by omega),map_zero]

theorem cutoffInteraction_sector_selection (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (m n : ℕ) (w u : EnergySpace P) (hnm : n ≠ m+1) (hmn : m ≠ n+1) :
    cutoffInteractionForm g Λ hΛ P (energySectorProjection P n w) (energySectorProjection P m u) = 0 := by
  change ⟪energyEmbedding P (energySectorProjection P n w),
    fieldRestriction (cutoffFormFactorL2 g Λ hΛ)
      (energyNumberCoordinates P (energySectorProjection P m u))⟫_ℂ = 0
  rw [energySectorProjection_intertwines,sectorProjection_apply,lp.inner_single_left]
  have hx : numberFormEmbedding (energyNumberCoordinates P (energySectorProjection P m u)) =
      sectorProjection m (energyEmbedding P u) := by
    rw [energyNumberCoordinates_intertwines,energySectorProjection_intertwines]
  rw [fieldRestriction_sector_eq_zero _ _ m n _ hx hnm hmn,inner_zero_right]

theorem singularInteraction_sector_selection (g : ℝ) (P : GW.Space) (m n : ℕ)
    (w u : EnergySpace P) (hnm : n ≠ m+1) (hmn : m ≠ n+1) :
    singularInteraction g P (energySectorProjection P n w) (energySectorProjection P m u) = 0 :=
  boundedForm_limit_entry_zero (cutoffInteraction_tendsto g P)
    (energySectorProjection P n w) (energySectorProjection P m u)
    (fun Λ => cutoffInteraction_sector_selection g Λ.val Λ.property P m n w u hnm hmn)

end Froehlich
