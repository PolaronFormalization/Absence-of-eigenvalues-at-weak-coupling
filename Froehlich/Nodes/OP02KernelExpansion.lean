import Froehlich.Nodes.OP02ProductFactorization

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich
variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

theorem translatedKernel_integral_expansion (f h : OneParticleEnergySpace 0) :
    Integrable (fun x : GW.Space × GW.Space =>
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        thresholdKernelC e he g hg hs P x.1 x.2*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2)
      (volume.prod volume) ∧
    (∫ x : GW.Space × GW.Space,
      (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
        thresholdKernelC e he g hg hs P x.1 x.2*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2 ∂volume.prod volume) =
      (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) (translatedLinearSource g P f)*translatedLinearSource g P h+
      ⟪oneParticleRadialMap f,thresholdKernelSourceVector e he g hg hs P hP⟫_ℂ*translatedLinearSource g P h+
      (starRingEnd ℂ) (translatedLinearSource g P f)*⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap h⟫_ℂ+
      ((g^2 : ℝ) : ℂ)*⟪oneParticleRadialMap f,thresholdIntegralOperator e he g hg hs P hP (oneParticleRadialMap h)⟫_ℂ := by
  let I := fun (A : GW.Space → GW.Space → ℂ) (x : GW.Space × GW.Space) =>
    (starRingEnd ℂ) (oneParticleEnergyEmbedding 0 f x.1)*(fiberFormFactor g (x.1+P) : ℂ)*
      A x.1 x.2*(fiberFormFactor g (x.2+P) : ℂ)*oneParticleEnergyEmbedding 0 h x.2
  let Ic := I (fun _ _ => (kernelConstant e he g hg hs P : ℂ))
  let Iq := I (fun q _ => (kernelPsi e he g hg hs P q : ℂ))
  let Ir := I (fun _ r => (kernelPsi e he g hg hs P r : ℂ))
  let IF := I (fun q r => (remainderKernel e he g hg hs P q r : ℂ))
  let IC := I (thresholdKernelC e he g hg hs P)
  have hc := kernelConstant_product_integral e he g hg hs P f h
  have hq := kernelPsi_left_product_integral e he g hg hs P hP f h
  have hr := kernelPsi_right_product_integral e he g hg hs P hP f h
  have hF := radialRemainder_inner_integral e he g hg hs P hP f h
  have hsum : IC = ((Ic+Iq)+Ir)+IF := by
    funext x
    simp only [IC,Ic,Iq,Ir,IF,I,Pi.add_apply,thresholdKernelC_decomposition,Complex.ofReal_add]
    ring
  have hci : Integrable Ic (volume.prod volume) := hc.1
  have hqi : Integrable Iq (volume.prod volume) := hq.1
  have hri : Integrable Ir (volume.prod volume) := hr.1
  have hFi : Integrable IF (volume.prod volume) := hF.1
  have hInt : Integrable IC (volume.prod volume) := by
    rw [hsum]
    exact ((hci.add hqi).add hri).add hFi
  refine ⟨hInt,?_⟩
  have h1 : (∫ x : GW.Space × GW.Space,((Ic x+Iq x)+Ir x)+IF x ∂volume.prod volume) =
      (∫ x : GW.Space × GW.Space,(Ic x+Iq x)+Ir x ∂volume.prod volume)+
        (∫ x : GW.Space × GW.Space,IF x ∂volume.prod volume) := by
    simpa only [Pi.add_apply,Pi.add_def] using! integral_add ((hci.add hqi).add hri) hFi
  have h2 : (∫ x : GW.Space × GW.Space,(Ic x+Iq x)+Ir x ∂volume.prod volume) =
      (∫ x : GW.Space × GW.Space,Ic x+Iq x ∂volume.prod volume)+
        (∫ x : GW.Space × GW.Space,Ir x ∂volume.prod volume) := by
    simpa only [Pi.add_apply,Pi.add_def] using! integral_add (hci.add hqi) hri
  have h3 : (∫ x : GW.Space × GW.Space,Ic x+Iq x ∂volume.prod volume) =
      (∫ x : GW.Space × GW.Space,Ic x ∂volume.prod volume)+
        (∫ x : GW.Space × GW.Space,Iq x ∂volume.prod volume) := by
    simpa only [Pi.add_apply,Pi.add_def] using! integral_add hci hqi
  have hStart : (∫ x : GW.Space × GW.Space,IC x ∂volume.prod volume) =
      (∫ x : GW.Space × GW.Space,((Ic x+Iq x)+Ir x)+IF x ∂volume.prod volume) := by
    apply congrArg (fun A : (GW.Space × GW.Space) → ℂ => ∫ x,A x ∂volume.prod volume)
    simpa only [Pi.add_def] using hsum
  have hSplit : (∫ x, IC x ∂volume.prod volume) =
      (∫ x, Ic x ∂volume.prod volume)+(∫ x, Iq x ∂volume.prod volume)+
        (∫ x, Ir x ∂volume.prod volume)+(∫ x, IF x ∂volume.prod volume) :=
    hStart.trans (h1.trans (congrArg₂ (fun a b : ℂ => a+b)
      (h2.trans (congrArg₂ (fun a b : ℂ => a+b) h3 rfl)) rfl))
  exact hSplit.trans (congrArg₂ (fun a b : ℂ => a+b)
    (congrArg₂ (fun a b : ℂ => a+b)
      (congrArg₂ (fun a b : ℂ => a+b) hc.2 hq.2) hr.2) hF.2.symm)

end Froehlich
