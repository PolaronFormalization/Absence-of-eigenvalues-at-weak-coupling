import Froehlich.Nodes.SE01CutoffProjection
import Froehlich.Nodes.SE01SectorEquations
import Froehlich.Nodes.UV01Coupling
import Mathlib.Tactic.LinearCombination

/-! The same actual source sector equations at every finite cutoff,
with the reference e unchanged and all original form tests allowed. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem se01_cutoffSource_one (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (f : OneParticleEnergySpace P) :
    cutoffFiberSourceLoad g P Λ.val (onePhononEnergyLift P f) = isolatedCutoffFiberSourceLoad g P Λ.val f := by
  change isolatedCutoffFiberSourceLoad g P Λ.val (oneParticleEnergyProjection P (onePhononEnergyLift P f)) = _
  rw [oneParticleEnergyProjection_lift]

theorem se01_cutoffSource_high (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (w : HighEnergySpace P 2) : cutoffFiberSourceLoad g P Λ.val (w : EnergySpace P) = 0 := by
  change isolatedCutoffFiberSourceLoad g P Λ.val (oneParticleEnergyProjection P w) = 0
  rw [oneParticleEnergyProjection_high_two,map_zero]

theorem se01_cutoffForm_one_one (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (f h : OneParticleEnergySpace P) :
    (fiberFormData g P (some Λ)).form (onePhononEnergyLift P f) (onePhononEnergyLift P h) = ⟪f,h⟫_ℂ := by
  have hz := cutoffInteraction_sector_selection g Λ.val Λ.property P 1 1
    (onePhononEnergyLift P f) (onePhononEnergyLift P h) (by omega) (by omega)
  simp only [onePhononEnergyLift_sector] at hz
  rw [fiberFormData_cutoff_apply,freeFiberForm_onePhonon,hz,add_zero]

theorem se01_cutoffForm_high_one (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (f : OneParticleEnergySpace P) (w : HighEnergySpace P 2) :
    (fiberFormData g P (some Λ)).form (w : EnergySpace P) (onePhononEnergyLift P f) =
      ⟪w,cutoffTwoSectorCoupling g P Λ f⟫_ℂ := by
  rw [fiberFormData_cutoff_apply,freeFiberForm_hermitian,freeFiberForm_onePhonon_high,star_zero,zero_add]
  exact (cutoffTwoSectorCoupling_spec g P Λ f w).symm

theorem se01_cutoffForm_one_high (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (f : OneParticleEnergySpace P) (w : HighEnergySpace P 2) :
    (fiberFormData g P (some Λ)).form (onePhononEnergyLift P f) (w : EnergySpace P) =
      ⟪f,(cutoffTwoSectorCoupling g P Λ).adjoint w⟫_ℂ := by
  rw [(fiberFormData g P (some Λ)).hermitian,se01_cutoffForm_high_one]
  simp only [Complex.star_def,inner_conj_symm]
  exact ((cutoffTwoSectorCoupling g P Λ).adjoint_inner_right f w).symm

private theorem se01_one_physical_pair (P : GW.Space) (f h : OneParticleEnergySpace P) :
    ⟪energyEmbedding P (onePhononEnergyLift P f),energyEmbedding P (onePhononEnergyLift P h)⟫_ℂ =
      ⟪oneParticleEnergyEmbedding P f,oneParticleEnergyEmbedding P h⟫_ℂ := by
  rw [onePhononEnergyLift_physical,onePhononEnergyLift_physical,
    oneParticleInclusion_pairing,oneParticleExtraction_inclusion]

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem cutoffGroundSource_one_equation (Λ : GW.Operators.PositiveCutoff) (f : OneParticleEnergySpace 0) :
    ⟪f,cutoffGroundSourceOneEnergy e he g hg hs Λ⟫_ℂ +
      ⟪f,(cutoffTwoSectorCoupling g 0 Λ).adjoint (cutoffGroundSourceHighEnergy e he g hg hs Λ)⟫_ℂ -
      (e : ℂ)*⟪oneParticleEnergyEmbedding 0 f,
        oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ)⟫_ℂ =
      isolatedCutoffFiberSourceLoad g 0 Λ.val f := by
  have h := cutoffGroundSourceZeroEnergy_weak e he g hg hs Λ (se01OneTest 0 f)
  change (fiberFormData g 0 (some Λ)).form (onePhononEnergyLift 0 f)
      (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0) -
    (e : ℂ)*⟪energyEmbedding 0 (onePhononEnergyLift 0 f),
      energyEmbedding 0 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0)⟫_ℂ =
    cutoffFiberSourceLoad g 0 Λ.val (onePhononEnergyLift 0 f) at h
  rw [←cutoffGroundSource_one_high_decomposition] at h
  simp only [map_add,inner_add_right] at h
  rw [se01_cutoffForm_one_one,se01_cutoffForm_one_high,se01_one_physical_pair,
    onePhonon_high_physical_orthogonal,se01_cutoffSource_one] at h
  simpa only [add_zero] using h

theorem cutoffGroundSource_high_equation_test (Λ : GW.Operators.PositiveCutoff) (w : HighEnergySpace 0 2) :
    (fiberFormData g 0 (some Λ)).form (w : EnergySpace 0)
        (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0) -
      (e : ℂ)*⟪energyEmbedding 0 (w : EnergySpace 0),
        energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0)⟫_ℂ =
      -⟪w,cutoffTwoSectorCoupling g 0 Λ (cutoffGroundSourceOneEnergy e he g hg hs Λ)⟫_ℂ := by
  have h := cutoffGroundSourceZeroEnergy_weak e he g hg hs Λ (se01HighTest 0 w)
  change (fiberFormData g 0 (some Λ)).form (w : EnergySpace 0)
      (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0) -
    (e : ℂ)*⟪energyEmbedding 0 (w : EnergySpace 0),
      energyEmbedding 0 (cutoffGroundSourceZeroEnergy e he g hg hs Λ : EnergySpace 0)⟫_ℂ =
    cutoffFiberSourceLoad g 0 Λ.val (w : EnergySpace 0) at h
  rw [←cutoffGroundSource_one_high_decomposition] at h
  simp only [map_add,inner_add_right] at h
  have hm := (inner_eq_zero_symm (𝕜 := ℂ)).mpr
    (onePhonon_high_physical_orthogonal 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) w)
  rw [se01_cutoffForm_high_one,hm,se01_cutoffSource_high] at h
  simp only [zero_add] at h
  linear_combination h

end Froehlich
