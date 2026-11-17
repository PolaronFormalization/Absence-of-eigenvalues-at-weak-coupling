import Froehlich.Nodes.SP01Block
import Froehlich.Nodes.SP01VacuumScalar

/-! The literal full singular form in the bounded scalar/nonvacuum
coordinates. Every test vector remains in the actual complete energy domain. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem nonvacuumOperator_physical_spec (g : ℝ) (P : GW.Space) (lam : ℝ)
    (w u : HighEnergySpace P 1) :
    ⟪w,nonvacuumOperator g P lam u⟫_ℂ = (fiberFormData g P none).form w u -
      (lam : ℂ)*⟪energyEmbedding P (w : EnergySpace P),energyEmbedding P (u : EnergySpace P)⟫_ℂ := by
  have h := nonvacuumOperator_spec g P lam w u
  have hi : ⟪highEnergyEmbedding P 1 w,highEnergyEmbedding P 1 u⟫_ℂ =
      ⟪energyEmbedding P (w : EnergySpace P),energyEmbedding P (u : EnergySpace P)⟫_ℂ := by
    change ⟪(highEnergyEmbedding P 1 w : GW.Fock.Carrier),
      (highEnergyEmbedding P 1 u : GW.Fock.Carrier)⟫_ℂ = _
    rw [highEnergyEmbedding_apply,highEnergyEmbedding_apply]
  rw [hi] at h
  exact h

theorem vacuumBlockForm_high_row (g : ℝ) (P : GW.Space) (lam : ℝ)
    (w : HighEnergySpace P 1) (z : ℂ × HighEnergySpace P 1) :
    (fiberFormData g P none).form (w : EnergySpace P) (vacuumEnergyJoin P z) -
      (lam : ℂ)*⟪energyEmbedding P (w : EnergySpace P),energyEmbedding P (vacuumEnergyJoin P z)⟫_ℂ =
      ⟪w,vacuumBlockB g P z.1 + nonvacuumOperator g P lam z.2⟫_ℂ := by
  rw [inner_add_right,nonvacuumOperator_physical_spec]
  simp only [vacuumEnergyJoin_apply,map_add,map_smulₛₗ,inner_add_right,inner_smul_right,
    vacuumEnergyLift_embedding,highEnergyEmbedding_vacuum_orthogonal,fiberForm_high_vacuum_column,
    vacuumBlockB,ContinuousLinearMap.toSpanSingleton_apply,RingHom.id_apply]
  rw [loadRiesz_spec]
  ring

theorem vacuumBlockForm_vacuum_row (g : ℝ) (P : GW.Space) (lam : ℝ)
    (z : ℂ × HighEnergySpace P 1) :
    (fiberFormData g P none).form (vacuumEnergyLift P) (vacuumEnergyJoin P z) -
      (lam : ℂ)*⟪GW.Fock.vacuum,energyEmbedding P (vacuumEnergyJoin P z)⟫_ℂ =
      vacuumBlockA P lam z.1 + vacuumBlockC g P z.2 := by
  have hvh : (fiberFormData g P none).form (vacuumEnergyLift P) (z.2 : EnergySpace P) =
      vacuumBlockC g P z.2 := by
    rw [(fiberFormData g P none).hermitian,fiberForm_high_vacuum_column,loadRiesz_spec]
    exact (inner_conj_symm (𝕜 := ℂ) (loadRiesz (highFiberSourceLoad g P 1)) z.2)
  have hv0 : ⟪GW.Fock.vacuum,energyEmbedding P (z.2 : EnergySpace P)⟫_ℂ = 0 :=
    (inner_eq_zero_symm (𝕜 := ℂ)).mpr (highEnergyEmbedding_vacuum_orthogonal P z.2)
  simp only [vacuumEnergyJoin_apply,map_add,map_smulₛₗ,inner_add_right,inner_smul_right,
    vacuumEnergyLift_embedding,vacuum_inner_self,hv0,hvh,fiberForm_vacuum_diagonal,
    vacuumBlockA,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
    Complex.ofReal_sub,Complex.ofReal_pow,RingHom.id_apply]
  ring

theorem vacuumBlockForm_identity (g : ℝ) (P : GW.Space) (lam : ℝ)
    (w z : ℂ × HighEnergySpace P 1) :
    (fiberFormData g P none).form (vacuumEnergyJoin P w) (vacuumEnergyJoin P z) -
      (lam : ℂ)*⟪energyEmbedding P (vacuumEnergyJoin P w),energyEmbedding P (vacuumEnergyJoin P z)⟫_ℂ =
      ⟪w.1,(vacuumBlockOperator g P lam z).1⟫_ℂ +
        ⟪w.2,(vacuumBlockOperator g P lam z).2⟫_ℂ := by
  have hv := vacuumBlockForm_vacuum_row g P lam z
  have hh := vacuumBlockForm_high_row g P lam w.2 z
  rw [vacuumEnergyJoin_apply]
  simp only [map_add,map_smulₛₗ,inner_add_left,inner_smul_left,vacuumEnergyLift_embedding,
    vacuumBlockOperator,blockOperator_apply,RCLike.inner_apply']
  change (starRingEnd ℂ) w.1 * (fiberFormData g P none).form (vacuumEnergyLift P)
      (vacuumEnergyJoin P z) + (fiberFormData g P none).form (w.2 : EnergySpace P)
      (vacuumEnergyJoin P z) - (lam : ℂ)*((starRingEnd ℂ) w.1 *
        ⟪GW.Fock.vacuum,energyEmbedding P (vacuumEnergyJoin P z)⟫_ℂ +
        ⟪energyEmbedding P (w.2 : EnergySpace P),energyEmbedding P (vacuumEnergyJoin P z)⟫_ℂ) =
      (starRingEnd ℂ) w.1 * (vacuumBlockA P lam z.1 + vacuumBlockC g P z.2) +
        ⟪w.2,vacuumBlockB g P z.1 + nonvacuumOperator g P lam z.2⟫_ℂ
  linear_combination (starRingEnd ℂ w.1) * hv + hh

end Froehlich
