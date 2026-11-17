import Froehlich.Nodes.SP03SchurForm
import Froehlich.Nodes.LD01
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/-! The genuine vacuum-source operator is an absolutely convergent product
integral. The singular coefficient is used only through its weighted load. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem pt03_isolatedSource_integral (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    Integrable (fun k => (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*(fiberFormFactor g k : ℂ)) volume ∧
    isolatedFiberSourceLoad g P f =
      ∫ k, (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*(fiberFormFactor g k : ℂ) := by
  exact ⟨weightedSource_pairing_integrable (oneParticleEnergyWeight P)
      (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P)
      (fun k => (fiberFormFactor g k : ℂ)) (fiberSource_quotient_memLp g P) f,
    weightedSourceLoad_integral (oneParticleEnergyWeight P)
      (oneParticleEnergyWeight_measurable P) (oneParticleEnergyWeight_ge_one P)
      (fun k => (fiberFormFactor g k : ℂ)) (fiberSource_quotient_memLp g P) f⟩

theorem onePhononSourceLinear_integral (g : ℝ) (P : GW.Space) (f : OneParticleEnergySpace P) :
    Integrable (fun k => (fiberFormFactor g k : ℂ)*oneParticleEnergyEmbedding P f k) volume ∧
    onePhononSourceLinear g P f = ∫ k, (fiberFormFactor g k : ℂ)*oneParticleEnergyEmbedding P f k := by
  have h := pt03_isolatedSource_integral g P f
  have hv : AEStronglyMeasurable (fun k : GW.Space => (fiberFormFactor g k : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp (fiberFormFactor_measurable g)).aestronglyMeasurable
  constructor
  · apply h.1.norm.mono' (hv.mul (Lp.aestronglyMeasurable (oneParticleEnergyEmbedding P f)))
    exact Filter.Eventually.of_forall (fun k => by
      simp only [Pi.mul_apply,norm_mul,Complex.norm_conj]
      exact le_of_eq (mul_comm _ _))
  · rw [onePhononSourceLinear_apply,h.2,Complex.star_def,←integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun k => by
      simp only [map_mul,Complex.conj_conj,Complex.conj_ofReal]
      ring)

theorem onePhononSourceOperator_product_integral (g : ℝ) (P : GW.Space)
    (f h : OneParticleEnergySpace P) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1)*(fiberFormFactor g x.1 : ℂ)*
        (fiberFormFactor g x.2 : ℂ)*oneParticleEnergyEmbedding P h x.2) (volume.prod volume) ∧
    ⟪f,onePhononSourceOperator g P h⟫_ℂ =
      ∫ x : GW.Space × GW.Space,
        (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1)*(fiberFormFactor g x.1 : ℂ)*
          (fiberFormFactor g x.2 : ℂ)*oneParticleEnergyEmbedding P h x.2 ∂volume.prod volume := by
  have hf := pt03_isolatedSource_integral g P f
  have hh := onePhononSourceLinear_integral g P h
  have hrow : (fun x : GW.Space × GW.Space =>
      ((starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1)*(fiberFormFactor g x.1 : ℂ))*
        ((fiberFormFactor g x.2 : ℂ)*oneParticleEnergyEmbedding P h x.2)) =ᵐ[volume.prod volume]
      (fun x => (starRingEnd ℂ) (oneParticleEnergyEmbedding P f x.1)*(fiberFormFactor g x.1 : ℂ)*
        (fiberFormFactor g x.2 : ℂ)*oneParticleEnergyEmbedding P h x.2) :=
    Filter.Eventually.of_forall (fun x => by ring)
  constructor
  · exact (hf.1.mul_prod hh.1).congr hrow
  · have hstar : (starRingEnd ℂ) (onePhononSourceLinear g P f) = isolatedFiberSourceLoad g P f := by
      rw [onePhononSourceLinear_apply]
      simp only [starRingEnd_apply,star_star]
    rw [onePhononSourceOperator,ContinuousLinearMap.comp_apply,
      (onePhononSourceLinear g P).adjoint_inner_right,RCLike.inner_apply',hstar,hf.2,hh.2]
    have hprod := integral_prod_mul (μ := (volume : Measure GW.Space)) (ν := (volume : Measure GW.Space))
      (fun k : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding P f k)*(fiberFormFactor g k : ℂ))
      (fun k : GW.Space => (fiberFormFactor g k : ℂ)*oneParticleEnergyEmbedding P h k)
    exact hprod.symm.trans (integral_congr_ae hrow)

end Froehlich
