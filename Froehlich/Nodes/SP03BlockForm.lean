import Froehlich.Nodes.SP03OneParticleColumns
import Froehlich.Nodes.SP03BlockSolution

/-! The true high-sector row of the full form in vacuum/one/high coordinates. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def onePhononEnergyJoin (P : GW.Space) (c : ℂ)
    (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) : EnergySpace P :=
  c • vacuumEnergyLift P + onePhononEnergyLift P f + (u : EnergySpace P)

theorem twoSectorOperator_physical_spec (g lam : ℝ) (P : GW.Space)
    (w u : HighEnergySpace P 2) :
    ⟪w,twoSectorOperator g P lam u⟫_ℂ = (fiberFormData g P none).form w u -
      (lam : ℂ)*⟪energyEmbedding P (w : EnergySpace P),energyEmbedding P (u : EnergySpace P)⟫_ℂ := by
  have h := twoSectorOperator_spec g P lam w u
  change ⟪w,twoSectorOperator g P lam u⟫_ℂ = (fiberFormData g P none).form w u -
    (lam : ℂ)*⟪energyEmbedding P (w : EnergySpace P),energyEmbedding P (u : EnergySpace P)⟫_ℂ at h
  exact h

theorem onePhononBlockForm_high_row (g lam : ℝ) (P : GW.Space)
    (w : HighEnergySpace P 2) (c : ℂ) (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) :
    (fiberFormData g P none).form (w : EnergySpace P) (onePhononEnergyJoin P c f u) -
      (lam : ℂ)*⟪energyEmbedding P (w : EnergySpace P),energyEmbedding P (onePhononEnergyJoin P c f u)⟫_ℂ =
      ⟪w,twoSectorCoupling g P f + twoSectorOperator g P lam u⟫_ℂ := by
  have hm : ⟪energyEmbedding P (w : EnergySpace P),energyEmbedding P (onePhononEnergyLift P f)⟫_ℂ = 0 :=
    (inner_eq_zero_symm (𝕜 := ℂ)).mpr (onePhonon_high_physical_orthogonal P f w)
  rw [inner_add_right,twoSectorOperator_physical_spec]
  simp only [onePhononEnergyJoin,map_add,map_smulₛₗ,inner_add_right,inner_smul_right,
    vacuumEnergyLift_embedding,fiberForm_high_two_vacuum,high_two_vacuum_physical_orthogonal,
    fiberForm_high_onePhonon,hm,smul_zero,mul_zero,zero_add,add_zero,RingHom.id_apply]
  ring

theorem onePhononBlockForm_vacuum_row (g lam : ℝ) (P : GW.Space)
    (c : ℂ) (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) :
    (fiberFormData g P none).form (vacuumEnergyLift P) (onePhononEnergyJoin P c f u) -
      (lam : ℂ)*⟪GW.Fock.vacuum,energyEmbedding P (onePhononEnergyJoin P c f u)⟫_ℂ =
      ((‖P‖^2-lam : ℝ) : ℂ)*c + onePhononSourceLinear g P f := by
  have hm : ⟪GW.Fock.vacuum,energyEmbedding P (onePhononEnergyLift P f)⟫_ℂ = 0 :=
    (inner_eq_zero_symm (𝕜 := ℂ)).mpr (onePhonon_vacuum_physical_orthogonal P f)
  have hh : ⟪GW.Fock.vacuum,energyEmbedding P (u : EnergySpace P)⟫_ℂ = 0 :=
    (inner_eq_zero_symm (𝕜 := ℂ)).mpr (high_two_vacuum_physical_orthogonal P u)
  simp only [onePhononEnergyJoin,map_add,map_smulₛₗ,inner_add_right,inner_smul_right,
    vacuumEnergyLift_embedding,vacuum_inner_self,fiberForm_vacuum_diagonal,
    fiberForm_vacuum_high_two,fiberForm_vacuum_onePhonon,hm,hh,
    smul_eq_mul,RingHom.id_apply,Complex.ofReal_sub,Complex.ofReal_pow,mul_one,mul_zero,add_zero]
  ring

theorem onePhononBlockForm_one_row (g lam : ℝ) (P : GW.Space)
    (h : OneParticleEnergySpace P) (c : ℂ) (f : OneParticleEnergySpace P) (u : HighEnergySpace P 2) :
    (fiberFormData g P none).form (onePhononEnergyLift P h) (onePhononEnergyJoin P c f u) -
      (lam : ℂ)*⟪energyEmbedding P (onePhononEnergyLift P h),energyEmbedding P (onePhononEnergyJoin P c f u)⟫_ℂ =
      ⟪h,(onePhononSourceLinear g P).adjoint c +
        (1-(lam : ℂ) • onePhononMassOperator P) f + (twoSectorCoupling g P).adjoint u⟫_ℂ := by
  have hL : ⟪h,(onePhononSourceLinear g P).adjoint c⟫_ℂ = isolatedFiberSourceLoad g P h * c := by
    rw [(onePhononSourceLinear g P).adjoint_inner_right]
    simp [RCLike.inner_apply',onePhononSourceLinear_apply,Complex.star_def,mul_comm]
  have hM : ⟪h,onePhononMassOperator P f⟫_ℂ =
      ⟪oneParticleEnergyEmbedding P h,oneParticleEnergyEmbedding P f⟫_ℂ := by
    rw [onePhononMassOperator,ContinuousLinearMap.comp_apply,
      (oneParticleEnergyEmbedding P).adjoint_inner_right]
  have hphys : ⟪energyEmbedding P (onePhononEnergyLift P h),energyEmbedding P (onePhononEnergyLift P f)⟫_ℂ =
      ⟪oneParticleEnergyEmbedding P h,oneParticleEnergyEmbedding P f⟫_ℂ := by
    rw [onePhononEnergyLift_physical,onePhononEnergyLift_physical,
      oneParticleInclusion_pairing,oneParticleExtraction_inclusion]
  rw [inner_add_right,inner_add_right,hL]
  simp only [onePhononEnergyJoin,map_add,map_smulₛₗ,inner_add_right,inner_smul_right,
    vacuumEnergyLift_embedding,fiberForm_onePhonon_vacuum,fiberForm_onePhonon,
    fiberForm_onePhonon_high,onePhonon_vacuum_physical_orthogonal,
    onePhonon_high_physical_orthogonal,hphys,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,ContinuousLinearMap.smul_apply,inner_sub_right,hM,
    RingHom.id_apply,smul_eq_mul,mul_zero,zero_add,add_zero]
  ring

/-- The three actual test sectors span the full original energy domain. -/
theorem onePhononBlockForm_test_ext (g lam : ℝ) (P : GW.Space) (u q : EnergySpace P)
    (hv : (fiberFormData g P none).form (vacuumEnergyLift P) u -
      (lam : ℂ)*⟪GW.Fock.vacuum,energyEmbedding P u⟫_ℂ = ⟪vacuumEnergyLift P,q⟫_ℂ)
    (h1 : ∀ f : OneParticleEnergySpace P,
      (fiberFormData g P none).form (onePhononEnergyLift P f) u -
        (lam : ℂ)*⟪energyEmbedding P (onePhononEnergyLift P f),energyEmbedding P u⟫_ℂ =
          ⟪onePhononEnergyLift P f,q⟫_ℂ)
    (h2 : ∀ w : HighEnergySpace P 2,
      (fiberFormData g P none).form (w : EnergySpace P) u -
        (lam : ℂ)*⟪energyEmbedding P (w : EnergySpace P),energyEmbedding P u⟫_ℂ =
          ⟪(w : EnergySpace P),q⟫_ℂ) :
    vacuumEnergyOperator g P lam u = q := by
  apply ext_inner_left ℂ
  intro w
  rw [vacuumEnergyOperator_spec]
  have hh1 := h1 (oneParticleEnergyProjection P w)
  have hh2 := h2 (highEnergyProject P 2 w)
  have hw := energy_vacuum_one_high_decomposition P w
  rw [← hw]
  simp only [map_add,map_smulₛₗ,inner_add_left,inner_smul_left,
    vacuumEnergyLift_embedding,LinearMap.add_apply,LinearMap.smul_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,RingHom.id_apply,smul_eq_mul]
  linear_combination (starRingEnd ℂ (vacuumCoefficient (energyEmbedding P w))) * hv + hh1 + hh2

end Froehlich
