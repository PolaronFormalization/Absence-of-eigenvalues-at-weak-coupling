import Froehlich.Nodes.OP02SourcePairings
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

theorem kernelConstant_product_integral (f h : OneParticleEnergySpace 0) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelConstant e he g hg hs P : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2)
      (volume.prod volume) ∧
    (∫ x : GW.Space × GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelConstant e he g hg hs P : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2 ∂volume.prod volume) =
      (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) (translatedLinearSource g P f)*translatedLinearSource g P h := by
  let A := fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*(fiberFormFactor g (q+P) : ℂ)
  let B := fun q : GW.Space => (fiberFormFactor g (q+P) : ℂ)*oneParticleEnergyEmbedding 0 h q
  let c := (kernelConstant e he g hg hs P : ℂ)
  have hA := translatedLinearSource_star_integral g P f
  have hB := translatedLinearSource_integrable g P h
  have hi := (hA.1.mul_prod hB).const_mul c
  have hp : (fun x : GW.Space × GW.Space => c*(A x.1*B x.2)) =ᵐ[volume.prod volume]
      (fun x => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelConstant e he g hg hs P : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2) :=
    Eventually.of_forall (fun x => by dsimp [A,B,c]; ring)
  refine ⟨hi.congr hp,?_⟩
  calc
    _ = ∫ x : GW.Space × GW.Space,c*(A x.1*B x.2) ∂volume.prod volume := (integral_congr_ae hp).symm
    _ = c*(∫ x : GW.Space × GW.Space,A x.1*B x.2 ∂volume.prod volume) := integral_const_mul _ _
    _ = c*((∫ q : GW.Space,A q)*(∫ r : GW.Space,B r)) := congrArg (fun z : ℂ => c*z)
      (integral_prod_mul (μ := (volume : Measure GW.Space)) (ν := (volume : Measure GW.Space)) A B)
    _ = _ := (congrArg (fun z : ℂ => c*z)
      (congrArg₂ (fun a b : ℂ => a*b) hA.2.symm (translatedLinearSource_integral g P h).symm)).trans
        (mul_assoc _ _ _).symm

theorem kernelPsi_left_product_integral (f h : OneParticleEnergySpace 0) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelPsi e he g hg hs P x.1 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2)
      (volume.prod volume) ∧
    (∫ x : GW.Space × GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelPsi e he g hg hs P x.1 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2 ∂volume.prod volume) =
      ⟪oneParticleRadialMap f,thresholdKernelSourceVector e he g hg hs P hP⟫_ℂ*translatedLinearSource g P h := by
  let A := fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*
    (fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ)
  let B := fun q : GW.Space => (fiberFormFactor g (q+P) : ℂ)*oneParticleEnergyEmbedding 0 h q
  have hA := radial_inner_kernelSource_integral e he g hg hs P hP f
  have hB := translatedLinearSource_integrable g P h
  have hp : (fun x : GW.Space × GW.Space => A x.1*B x.2) =ᵐ[volume.prod volume]
      (fun x => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelPsi e he g hg hs P x.1 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2) :=
    Eventually.of_forall (fun x => by dsimp [A,B]; ring)
  refine ⟨(hA.1.mul_prod hB).congr hp,?_⟩
  calc
    _ = ∫ x : GW.Space × GW.Space,A x.1*B x.2 ∂volume.prod volume := (integral_congr_ae hp).symm
    _ = (∫ q : GW.Space,A q)*(∫ r : GW.Space,B r) := integral_prod_mul _ _
    _ = _ := congrArg₂ (fun a b : ℂ => a*b) hA.2.symm (translatedLinearSource_integral g P h).symm

theorem kernelPsi_right_product_integral (f h : OneParticleEnergySpace 0) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelPsi e he g hg hs P x.2 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2)
      (volume.prod volume) ∧
    (∫ x : GW.Space × GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelPsi e he g hg hs P x.2 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2 ∂volume.prod volume) =
      (starRingEnd ℂ) (translatedLinearSource g P f)*⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap h⟫_ℂ := by
  let A := fun q : GW.Space => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f q)*(fiberFormFactor g (q+P) : ℂ)
  let B := fun q : GW.Space => (fiberFormFactor g (q+P) : ℂ)*(kernelPsi e he g hg hs P q : ℂ)*oneParticleEnergyEmbedding 0 h q
  have hA := translatedLinearSource_star_integral g P f
  have hB := kernelSource_inner_radial_integral e he g hg hs P hP h
  have hp : (fun x : GW.Space × GW.Space => A x.1*B x.2) =ᵐ[volume.prod volume]
      (fun x => (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        (kernelPsi e he g hg hs P x.2 : ℂ)*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2) :=
    Eventually.of_forall (fun x => by dsimp [A,B]; ring)
  refine ⟨(hA.1.mul_prod hB.1).congr hp,?_⟩
  calc
    _ = ∫ x : GW.Space × GW.Space,A x.1*B x.2 ∂volume.prod volume := (integral_congr_ae hp).symm
    _ = (∫ q : GW.Space,A q)*(∫ r : GW.Space,B r) := integral_prod_mul _ _
    _ = _ := congrArg₂ (fun a b : ℂ => a*b) hA.2.symm hB.2.symm

end Froehlich
