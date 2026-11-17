import Froehlich.Nodes.OP02KernelExpansion
import Froehlich.Nodes.OP02DiagonalForm
import Froehlich.Nodes.PT03FormTranslated
import Froehlich.Nodes.OP01BoundedOperator

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

private theorem op02_complex_diagonal_join (d b L : ℂ) (c : ℝ) :
    d+(c : ℂ)*(starRingEnd ℂ) L*L+(starRingEnd ℂ) b*L+(starRingEnd ℂ) L*b =
      d+((c*‖L‖^2 : ℝ) : ℂ)+((2*((starRingEnd ℂ) L*b).re : ℝ) : ℂ) := by
  have hc : (c : ℂ)*(starRingEnd ℂ) L*L = ((c*‖L‖^2 : ℝ) : ℂ) := by
    rw [mul_assoc]
    have hn : (starRingEnd ℂ) L*L = ((‖L‖^2 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_pow] using Complex.conj_mul' L
    rw [hn,Complex.ofReal_mul]
  have hb : (starRingEnd ℂ) b*L+(starRingEnd ℂ) L*b = ((2*((starRingEnd ℂ) L*b).re : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im] <;> ring
  calc
    _ = d+((c : ℂ)*(starRingEnd ℂ) L*L)+((starRingEnd ℂ) b*L+(starRingEnd ℂ) L*b) := by ring
    _ = _ := by rw [hc,hb]

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

theorem translatedThresholdForm_unnormalized (f : OneParticleEnergySpace 0) :
    translatedThresholdForm e he g hquarter heLower hquadratic P hP f f =
      ⟪oneParticleRadialMap f,thresholdBoundedOperator e he g hg hs CD hCD hquad P hP (oneParticleRadialMap f)⟫_ℂ+
      ((kernelConstant e he g hg hs P*‖translatedLinearSource g P f‖^2 : ℝ) : ℂ)+
      ((2*((starRingEnd ℂ) (translatedLinearSource g P f)*
        ⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap f⟫_ℂ).re : ℝ) : ℂ) := by
  let u := oneParticleRadialMap f
  let b := thresholdKernelSourceVector e he g hg hs P hP
  let L := translatedLinearSource g P f
  let D := thresholdDiagonalOperator e he g hg hs CD hCD hquad
  let K := thresholdIntegralOperator e he g hg hs P hP
  let B := thresholdBoundedOperator e he g hg hs CD hCD hquad P hP
  have hPT := translatedThresholdForm_kernel_formula e he g hg hs hquarter heLower hquadratic P hP f f
  have hDiag := radialDiagonal_inner_integral e he g hg hs CD hCD hquad f f
  have hKernel := translatedKernel_integral_expansion e he g hg hs P hP f f
  have hB : ⟪u,B u⟫_ℂ = ⟪u,D u⟫_ℂ+((g^2 : ℝ) : ℂ)*⟪u,K u⟫_ℂ := by
    change ⟪u,(D+((g^2 : ℝ) : ℂ) • K) u⟫_ℂ = _
    simp only [add_apply,smul_apply,inner_add_right,inner_smul_right]
  have hRaw : translatedThresholdForm e he g hquarter heLower hquadratic P hP f f =
      ⟪u,B u⟫_ℂ+(kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) L*L+
        ⟪u,b⟫_ℂ*L+(starRingEnd ℂ) L*⟪b,u⟫_ℂ := by
    have h := hPT.2.2.trans (congrArg₂ (fun a b : ℂ => a+b) hDiag.2.symm hKernel.2)
    calc
      _ = ⟪u,D u⟫_ℂ+((kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) L*L+
          ⟪u,b⟫_ℂ*L+(starRingEnd ℂ) L*⟪b,u⟫_ℂ+((g^2 : ℝ) : ℂ)*⟪u,K u⟫_ℂ) := h
      _ = (⟪u,D u⟫_ℂ+((g^2 : ℝ) : ℂ)*⟪u,K u⟫_ℂ)+
          (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) L*L+
          ⟪u,b⟫_ℂ*L+(starRingEnd ℂ) L*⟪b,u⟫_ℂ := by ring
      _ = _ := congrArg (fun z : ℂ => z+(kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) L*L+
        ⟪u,b⟫_ℂ*L+(starRingEnd ℂ) L*⟪b,u⟫_ℂ) hB.symm
  have hstar : ⟪u,b⟫_ℂ = (starRingEnd ℂ) ⟪b,u⟫_ℂ := (inner_conj_symm u b).symm
  have hRaw' := hRaw.trans (congrArg (fun z : ℂ => ⟪u,B u⟫_ℂ+
    (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) L*L+z*L+(starRingEnd ℂ) L*⟪b,u⟫_ℂ) hstar)
  exact hRaw'.trans (op02_complex_diagonal_join ⟪u,B u⟫_ℂ ⟪b,u⟫_ℂ L (kernelConstant e he g hg hs P))

theorem translatedThresholdForm_unnormalized_real (f : OneParticleEnergySpace 0) :
    (translatedThresholdForm e he g hquarter heLower hquadratic P hP f f).re =
      (⟪oneParticleRadialMap f,thresholdBoundedOperator e he g hg hs CD hCD hquad P hP (oneParticleRadialMap f)⟫_ℂ).re+
      kernelConstant e he g hg hs P*‖translatedLinearSource g P f‖^2+
      2*((starRingEnd ℂ) (translatedLinearSource g P f)*
        ⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap f⟫_ℂ).re := by
  have h := congrArg Complex.re
    (translatedThresholdForm_unnormalized e he g hg hs CD hCD hquad hquarter heLower hquadratic P hP f)
  simpa only [Complex.add_re,Complex.ofReal_re] using h

end Froehlich
