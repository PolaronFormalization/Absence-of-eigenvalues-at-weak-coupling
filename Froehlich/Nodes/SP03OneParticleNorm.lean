import Froehlich.Nodes.SP03Coupling

/-! Exact isolated one-particle energy normalization, needed to identify
its free form without changing the source graph norm. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich

theorem onePhononEnergyLift_norm_sq (P : GW.Space) (f : OneParticleEnergySpace P) :
    ‖onePhononEnergyLift P f‖^2 = ‖f‖^2 + ‖oneParticleEnergyEmbedding P f‖^2 := by
  let g := isolatedToInherited P f
  let f0 : GW.OnePhonon := GW.Spaces.WeightedL2.coordinates f
  let g0 : GW.OnePhonon := GW.Spaces.WeightedL2.coordinates g
  let v : GW.OnePhonon := oneParticleEnergyEmbedding P f
  have hf := GW.Spaces.WeightedL2.weighted_embed_ae
    (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P) f
  have hg := GW.Spaces.WeightedL2.weighted_embed_ae
    (oneParticleInheritedWeight_measurable P) (oneParticleInheritedWeight_ge_one P) g
  change (fun k => (oneParticleEnergyWeight P k : ℂ)*v k) =ᵐ[volume] f0 at hf
  change (fun k => (oneParticleInheritedWeight P k : ℂ)*oneParticleInheritedEmbedding P g k) =ᵐ[volume] g0 at hg
  have he : oneParticleInheritedEmbedding P g = v := isolatedToInherited_intertwines P f
  rw [he] at hg
  have hw (k : GW.Space) : oneParticleInheritedWeight P k ^ 2 = oneParticleEnergyWeight P k ^ 2+1 := by
    unfold oneParticleInheritedWeight oneParticleEnergyWeight
    rw [Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    ring
  have hpoint : (fun k => ‖g0 k‖^2) =ᵐ[volume] (fun k => ‖f0 k‖^2+‖v k‖^2) := by
    filter_upwards [hf,hg] with k hfk hgk
    rw [← hfk,← hgk]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    rw [hw]
    ring
  have hfint := (Lp.memLp f0).integrable_norm_pow (p := 2) (by norm_num)
  have hvint := (Lp.memLp v).integrable_norm_pow (p := 2) (by norm_num)
  have hn : ‖g0‖^2 = ‖f0‖^2+‖v‖^2 := by
    rw [GW.Analysis.l2_norm_sq (𝕜 := ℂ) g0,GW.Analysis.l2_norm_sq (𝕜 := ℂ) f0,
      GW.Analysis.l2_norm_sq (𝕜 := ℂ) v]
    exact (integral_congr_ae hpoint).trans (integral_add hfint hvint)
  have hfn : ‖f0‖ = ‖f‖ := GW.Spaces.WeightedL2.coordinates.norm_map f
  have hgn : ‖g0‖ = ‖g‖ := GW.Spaces.WeightedL2.coordinates.norm_map g
  rw [hfn,hgn] at hn
  change ‖oneParticleInheritedFockLift P g‖^2 = _
  rw [oneParticleInheritedFockLift_norm]
  exact hn

theorem freeFiberForm_onePhonon_diagonal (P : GW.Space) (f : OneParticleEnergySpace P) :
    freeFiberForm P (onePhononEnergyLift P f) (onePhononEnergyLift P f) = (‖f‖^2 : ℂ) := by
  have h : ‖onePhononEnergyLift P f‖^2 - ‖energyEmbedding P (onePhononEnergyLift P f)‖^2 = ‖f‖^2 := by
    rw [onePhononEnergyLift_norm_sq,onePhononEnergyLift_physical,oneParticleInclusion_norm]
    ring
  rw [freeFiberForm_apply,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  have hc := congrArg (algebraMap ℝ ℂ) h
  simpa only [map_sub,map_pow,Complex.coe_algebraMap] using hc


theorem freeFiberForm_onePhonon (P : GW.Space) (f h : OneParticleEnergySpace P) :
    freeFiberForm P (onePhononEnergyLift P f) (onePhononEnergyLift P h) = ⟪f,h⟫_ℂ := by
  let L := onePhononEnergyLift P
  let J := (energyEmbedding P).comp L
  let b : GW.Operators.AlgebraicForm (OneParticleEnergySpace P) :=
    GW.Operators.embeddingForm L - GW.Operators.embeddingForm J - innerₛₗ ℂ
  have hb : ∀ u v, b u v = star (b v u) := by
    intro u v
    change ⟪L u,L v⟫_ℂ - ⟪J u,J v⟫_ℂ - ⟪u,v⟫_ℂ =
      star (⟪L v,L u⟫_ℂ - ⟪J v,J u⟫_ℂ - ⟪v,u⟫_ℂ)
    simp only [star_sub,Complex.star_def,inner_conj_symm]
  have hd : ∀ u, ‖b u u‖ ≤ (0 : ℝ)*‖u‖^2 := by
    intro u
    change ‖freeFiberForm P (onePhononEnergyLift P u) (onePhononEnergyLift P u) - ⟪u,u⟫_ℂ‖ ≤ _
    rw [freeFiberForm_onePhonon_diagonal,inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow]
    simp only [← RCLike.algebraMap_eq_ofReal,Complex.coe_algebraMap,Complex.ofReal_pow,sub_self,norm_zero,zero_mul,le_refl]
  have hbound := GW.Operators.hermitian_mixed_bound b hb (show (0 : ℝ) ≤ 0 by norm_num) hd f h
  have hz : b f h = 0 := norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hbound) (norm_nonneg _))
  change freeFiberForm P (onePhononEnergyLift P f) (onePhononEnergyLift P h) - ⟪f,h⟫_ℂ = 0 at hz
  exact sub_eq_zero.mp hz

end Froehlich
