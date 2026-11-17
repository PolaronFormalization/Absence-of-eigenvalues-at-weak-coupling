import Froehlich.Nodes.OP02DiagonalIdentity

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8) (P : GW.Space) (hP : ‖P‖ ≤ 1/4)

/-- Direct mixed decomposition from the absolutely integrable kernel pieces. -/
theorem translatedThresholdForm_polarized (f h : OneParticleEnergySpace 0) :
    translatedThresholdForm e he g hquarter heLower hquadratic P hP f h =
      ⟪oneParticleRadialMap f,thresholdBoundedOperator e he g hg hs CD hCD hquad P hP (oneParticleRadialMap h)⟫_ℂ+
      (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) (translatedLinearSource g P f)*translatedLinearSource g P h+
      (starRingEnd ℂ) (translatedLinearSource g P f)*
        ⟪thresholdKernelSourceVector e he g hg hs P hP,oneParticleRadialMap h⟫_ℂ+
      ⟪oneParticleRadialMap f,thresholdKernelSourceVector e he g hg hs P hP⟫_ℂ*translatedLinearSource g P h := by
  let u := oneParticleRadialMap f
  let v := oneParticleRadialMap h
  let b := thresholdKernelSourceVector e he g hg hs P hP
  let Lf := translatedLinearSource g P f
  let Lh := translatedLinearSource g P h
  let D := thresholdDiagonalOperator e he g hg hs CD hCD hquad
  let K := thresholdIntegralOperator e he g hg hs P hP
  let B := thresholdBoundedOperator e he g hg hs CD hCD hquad P hP
  have hPT := translatedThresholdForm_kernel_formula e he g hg hs hquarter heLower hquadratic P hP f h
  have hDiag := radialDiagonal_inner_integral e he g hg hs CD hCD hquad f h
  have hKernel := translatedKernel_integral_expansion e he g hg hs P hP f h
  have hB : ⟪u,B v⟫_ℂ = ⟪u,D v⟫_ℂ+((g^2 : ℝ) : ℂ)*⟪u,K v⟫_ℂ := by
    change ⟪u,(D+((g^2 : ℝ) : ℂ) • K) v⟫_ℂ = _
    simp only [add_apply,smul_apply,inner_add_right,inner_smul_right]
  have h := hPT.2.2.trans (congrArg₂ (fun a b : ℂ => a+b) hDiag.2.symm hKernel.2)
  calc
    _ = ⟪u,D v⟫_ℂ+((kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) Lf*Lh+
        ⟪u,b⟫_ℂ*Lh+(starRingEnd ℂ) Lf*⟪b,v⟫_ℂ+((g^2 : ℝ) : ℂ)*⟪u,K v⟫_ℂ) := h
    _ = (⟪u,D v⟫_ℂ+((g^2 : ℝ) : ℂ)*⟪u,K v⟫_ℂ)+
        (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) Lf*Lh+
        (starRingEnd ℂ) Lf*⟪b,v⟫_ℂ+⟪u,b⟫_ℂ*Lh := by ring
    _ = _ := congrArg (fun z : ℂ => z+
      (kernelConstant e he g hg hs P : ℂ)*(starRingEnd ℂ) Lf*Lh+
      (starRingEnd ℂ) Lf*⟪b,v⟫_ℂ+⟪u,b⟫_ℂ*Lh) hB.symm

end Froehlich
