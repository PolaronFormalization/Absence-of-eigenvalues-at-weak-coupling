import Froehlich.Nodes.SE02CutoffFixedFields
import Froehlich.Nodes.PT03ScalarStepOne
import Froehlich.Nodes.PT03ScalarSymmetry
import Froehlich.Nodes.PT02ProjectionConvention

/-! Finite-cutoff lambda cancellation from TWO fixed-source vector fields.
Testing their common vector identity by h_k is pointwise linear algebra;
there is no parameter-dependent AE specialization. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

private theorem se02_high_vacuum (z : HighSectorSpace 1) :
    ⟪GW.Fock.vacuum,(z : GW.Fock.Carrier)⟫_ℂ = 0 := by
  have h := congrArg (fun u : GW.Fock.Carrier => u 0) ((highSector_mem_iff 1 z).mp z.property)
  have hz : (z : GW.Fock.Carrier) 0 = 0 := by
    simpa only [highSectorProjection_apply,show ¬1 ≤ (0 : ℕ) by omega,ite_false] using h.symm
  have hzC : ((z : GW.Fock.Carrier) 0 : ℂ) = (0 : ℂ) := by
    exact hz
  rw [←vacuumInclusion_one,vacuumInclusion_pairing]
  change inner ℂ (1 : ℂ) ((z : GW.Fock.Carrier) 0 : ℂ) = 0
  rw [hzC,inner_zero_right]

private theorem se02_fixed_scalar (v : ℝ) (f : ℂ)
    (hk z a r x y b : GW.Fock.Carrier)
    (hh : ⟪hk,GW.Fock.vacuum⟫_ℂ = 0) (hr : ⟪GW.Fock.vacuum,r⟫_ℂ = 0)
    (hsource : a = (v : ℂ) • z) (hsplit : a = f • GW.Fock.vacuum+r)
    (hpair : ⟪b,y⟫_ℂ = ⟪hk,r-(v : ℂ) • x⟫_ℂ) :
    (v : ℂ)*(⟪GW.Fock.vacuum-hk,z⟫_ℂ+⟪hk,x⟫_ℂ) = f-⟪b,y⟫_ℂ := by
  have hfirst : (v : ℂ)*⟪GW.Fock.vacuum-hk,z⟫_ℂ = f-⟪hk,r⟫_ℂ := by
    calc
      _ = ⟪GW.Fock.vacuum-hk,a⟫_ℂ := by rw [hsource,inner_smul_right]
      _ = _ := by
        rw [hsplit,inner_add_right,inner_smul_right,inner_sub_left,inner_sub_left,
          vacuum_inner_self,hh,hr]
        ring
  have hsecond := hpair
  rw [inner_sub_right,inner_smul_right] at hsecond
  rw [mul_add,hfirst,hsecond]
  ring

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
  (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem se02_cutoff_X_source_high (Λ : GW.Operators.PositiveCutoff) :
    cutoffAuxiliaryX e he Λ g hg hs 0 (cutoffThresholdSourceVector e he g hg hs Λ 0) =
      (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier) := by
  calc
    _ = cutoffAuxiliaryX e he Λ g hg hs 0
        (highSectorProjection 2 (cutoffThresholdSourceVector e he g hg hs Λ 0)) :=
      (cutoffAuxiliaryX_project e he g hg hs Λ 0 _).symm
    _ = cutoffAuxiliaryX e he Λ g hg hs 0
        (energyEmbedding 0 (cutoffGroundSourceHighEnergy e he g hg hs Λ : EnergySpace 0)) :=
      congrArg (cutoffAuxiliaryX e he Λ g hg hs 0) (cutoffGroundSourceHighEnergy_physical e he g hg hs Λ).symm
    _ = _ := (se02CutoffXHighVector_physical e he g hg hs Λ).symm

theorem se02_cutoff_lambda_physical (Λ : GW.Operators.PositiveCutoff) (k : GW.Space) :
    cutoffThresholdKernelJ e he g hg hs Λ 0 k 0 =
      ⟪GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ k,
        cutoffAuxiliaryZ e k he Λ g hg hs (GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ 0)⟫_ℂ +
      ⟪cutoffThresholdSourceVector e he g hg hs Λ k,(se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier)⟫_ℂ := by
  simp only [cutoffThresholdKernelJ,zero_add,add_zero]
  rw [se02_cutoff_X_source_high]

theorem se02_cutoff_lambda_cancellation (Λ : GW.Operators.PositiveCutoff) :
    ∀ᵐ k ∂volume, (cutoffFormFactor g Λ.val k : ℂ)*cutoffThresholdKernelJ e he g hg hs Λ 0 k 0 =
      oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) k -
        oneToHighAdjoint (cutoffFormFactorL2 g Λ.val Λ.property) (se02CutoffXHighVector e he g hg hs Λ) k := by
  filter_upwards [se02_cutoff_fixed_field_set e he g hg hs Λ] with k hk
  obtain ⟨hsource,hhigh,hsplit,hsector,hadjoint⟩ := hk
  have hhv : ⟪cutoffThresholdSourceVector e he g hg hs Λ k,GW.Fock.vacuum⟫_ℂ = 0 :=
    highEnergyEmbedding_vacuum_orthogonal (-k) (cutoffGroundSourceEnergy e k he g hg hs Λ)
  have hrv := se02_high_vacuum
    (⟨annihilationField (se02CutoffHighNumber e he g hg hs Λ) k,hsector⟩ : HighSectorSpace 1)
  have hpair : ⟪oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property),
      annihilationField (se02CutoffXHighNumber e he g hg hs Λ) k⟫_ℂ =
      ⟪cutoffThresholdSourceVector e he g hg hs Λ k,
        annihilationField (se02CutoffHighNumber e he g hg hs Λ) k -
          (cutoffFormFactor g Λ.val k : ℂ) • (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier)⟫_ℂ := by
    rw [hhigh]
    have h := pt03_cutoffExtendedResolvent_pairing 1 e k he Λ g hg hs
      (oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property))
      (annihilationField (se02CutoffHighNumber e he g hg hs Λ) k -
        (cutoffFormFactor g Λ.val k : ℂ) • (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier))
    change ⟪_,cutoffAuxiliaryY e k he Λ g hg hs _⟫_ℂ =
      ⟪cutoffAuxiliaryY e k he Λ g hg hs (oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property)),_⟫_ℂ at h
    rw [cutoffThresholdSourceVector_eq_Y] at h
    exact h
  have h := se02_fixed_scalar (cutoffFormFactor g Λ.val k)
    (oneParticleEnergyEmbedding 0 (cutoffGroundSourceOneEnergy e he g hg hs Λ) k)
    (cutoffThresholdSourceVector e he g hg hs Λ k)
    (cutoffAuxiliaryZ e k he Λ g hg hs (GW.Fock.vacuum-cutoffThresholdSourceVector e he g hg hs Λ 0))
    (annihilationField (cutoffGroundSourceNumber e 0 he g hg hs Λ) k)
    (annihilationField (se02CutoffHighNumber e he g hg hs Λ) k)
    (se02CutoffXHighVector e he g hg hs Λ : GW.Fock.Carrier)
    (annihilationField (se02CutoffXHighNumber e he g hg hs Λ) k)
    (oneParticleInclusion (cutoffFormFactorL2 g Λ.val Λ.property)) hhv hrv hsource hsplit hpair
  rw [←se02_cutoff_lambda_physical,←hadjoint] at h
  exact h

end Froehlich
