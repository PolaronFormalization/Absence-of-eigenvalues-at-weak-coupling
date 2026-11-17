import Froehlich.Nodes.SE01SourceProjection
import Froehlich.Nodes.SP03BlockForm
import Froehlich.Nodes.FC07ProjectedCore

/-! Full-domain one/high sector equations for the actual singular source.
The high-sector identity uses physical mass j†j, not the energy identity. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def se01OneTest (P : GW.Space) (f : OneParticleEnergySpace P) : HighEnergySpace P 1 :=
  ⟨onePhononEnergyLift P f,by
    apply (highEnergy_mem_iff P 1 _).mpr
    apply energyEmbedding_injective P
    rw [energyHighProjection_intertwines,onePhononEnergyLift_physical]
    apply lp.ext
    funext n
    rw [highSectorProjection_apply]
    by_cases hn : 1 ≤ n
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn,oneParticleInclusion_apply,
        lp.single_apply_ne _ _ _ (show n ≠ 1 by omega)]⟩

def se01HighTest (P : GW.Space) (w : HighEnergySpace P 2) : HighEnergySpace P 1 :=
  ⟨(w : EnergySpace P),by
    apply (highEnergy_mem_iff P 1 _).mpr
    apply energyEmbedding_injective P
    rw [energyHighProjection_intertwines]
    exact (highSector_mem_iff 1 _).mp
      (highSector_mem_of_succ 1 _ (highEnergyEmbedding P 2 w).property)⟩

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem groundSource_zero_join :
    onePhononEnergyJoin 0 0 (groundSourceOneEnergy e he g hg hs)
      (groundSourceHighEnergy e he g hg hs) = (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) := by
  simpa only [onePhononEnergyJoin,zero_smul,zero_add] using groundSource_one_high_decomposition e he g hg hs

theorem groundSource_one_equation (f : OneParticleEnergySpace 0) :
    ⟪f,(1-(e : ℂ) • onePhononMassOperator 0) (groundSourceOneEnergy e he g hg hs) +
      (twoSectorCoupling g 0).adjoint (groundSourceHighEnergy e he g hg hs)⟫_ℂ =
      isolatedFiberSourceLoad g 0 f := by
  have h := groundSourceZeroEnergy_weak e he g hg hs (se01OneTest 0 f)
  change (fiberFormData g 0 none).form (onePhononEnergyLift 0 f)
      (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) -
    (e : ℂ)*⟪energyEmbedding 0 (onePhononEnergyLift 0 f),
      energyEmbedding 0 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0)⟫_ℂ =
    fiberSourceLoad g 0 (onePhononEnergyLift 0 f) at h
  rw [←groundSource_zero_join,onePhononBlockForm_one_row,fiberSourceLoad_onePhonon] at h
  simpa only [map_zero,zero_add] using h

theorem groundSource_high_equation_test (w : HighEnergySpace 0 2) :
    ⟪w,twoSectorCoupling g 0 (groundSourceOneEnergy e he g hg hs) +
      twoSectorOperator g 0 e (groundSourceHighEnergy e he g hg hs)⟫_ℂ = 0 := by
  have h := groundSourceZeroEnergy_weak e he g hg hs (se01HighTest 0 w)
  change (fiberFormData g 0 none).form (w : EnergySpace 0)
      (groundSourceZeroEnergy e he g hg hs : EnergySpace 0) -
    (e : ℂ)*⟪energyEmbedding 0 (w : EnergySpace 0),
      energyEmbedding 0 (groundSourceZeroEnergy e he g hg hs : EnergySpace 0)⟫_ℂ =
    fiberSourceLoad g 0 (w : EnergySpace 0) at h
  rw [←groundSource_zero_join,onePhononBlockForm_high_row,fiberSourceLoad_high_two] at h
  exact h

theorem groundSource_high_equation :
    twoSectorCoupling g 0 (groundSourceOneEnergy e he g hg hs) +
      twoSectorOperator g 0 e (groundSourceHighEnergy e he g hg hs) = 0 := by
  apply ext_inner_left ℂ
  intro w
  rw [inner_zero_right]
  exact groundSource_high_equation_test e he g hg hs w

theorem twoSectorOperator_ground_shift (g e : ℝ) (P : GW.Space) :
    twoSectorOperator g P e = twoSectorOperator g P (e+1) +
      (highEnergyEmbedding P 2).adjoint.comp (highEnergyEmbedding P 2) := by
  unfold twoSectorOperator sourceOperator
  simp only [Complex.ofReal_add,Complex.ofReal_one,add_smul,one_smul]
  abel

theorem groundSource_high_shifted_equation :
    twoSectorOperator g 0 (e+1) (groundSourceHighEnergy e he g hg hs) +
      (highEnergyEmbedding 0 2).adjoint (highEnergyEmbedding 0 2 (groundSourceHighEnergy e he g hg hs)) =
      -(twoSectorCoupling g 0 (groundSourceOneEnergy e he g hg hs)) := by
  have h := groundSource_high_equation e he g hg hs
  rw [twoSectorOperator_ground_shift,add_apply,ContinuousLinearMap.comp_apply] at h
  exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans h)

end Froehlich
