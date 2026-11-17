import Froehlich.Nodes.OP03
import Froehlich.Nodes.SE03
import Froehlich.Nodes.OP01Inverse

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

/-- The zero-momentum square uses a finite scalar functional, never a t0 vector. -/
theorem po02_complete_square (B : GW.OnePhonon →L[ℂ] GW.OnePhonon)
    (b x u : GW.OnePhonon) (a : ℂ) (c : ℝ)
    (hB : B.adjoint = B) (hBx : B x = b) (hc : ⟪b,x⟫_ℂ = (c : ℂ)) :
    ⟪u,B u⟫_ℂ+(c : ℂ)*(starRingEnd ℂ) a*a+
        (starRingEnd ℂ) a*⟪b,u⟫_ℂ+⟪u,b⟫_ℂ*a =
      ⟪u+a • x,B (u+a • x)⟫_ℂ := by
  have hxu : ⟪x,B u⟫_ℂ = ⟪b,u⟫_ℂ := by
    have h := B.adjoint_inner_left u x
    rw [hB,hBx] at h
    exact h.symm
  have hxb : ⟪x,b⟫_ℂ = (c : ℂ) := by
    have h : ⟪x,b⟫_ℂ = (starRingEnd ℂ) ⟪b,x⟫_ℂ := (inner_conj_symm x b).symm
    rw [hc,Complex.conj_ofReal] at h
    exact h
  simp only [map_add,map_smul,inner_add_left,inner_add_right,
    inner_smul_left,inner_smul_right,hBx,hxu,hxb]
  ring

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (CD : ℝ) (hCD : 0 ≤ CD)
    (hquad : ∀ q : GW.Space, |auxiliarySelfEnergy e q he g hg hs-e| ≤ CD*g^2*‖q‖^2)
    (hquarter : |g| ≤ 1/4) (heLower : -sectorEnergyConstant*|g|^2 ≤ e)
    (hquadratic : sectorQuadraticConstant*|g|^2 ≤ 1/8)
    (hN : ‖thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)-1‖ ≤ 1/2)
    (hSat : SE03FixedReference CD e he g hg hs hCD hquad)

include hquarter heLower hquadratic hN hSat in
theorem translatedThresholdForm_zero_square (f : OneParticleEnergySpace 0) :
    translatedThresholdForm e he g hquarter heLower hquadratic 0 (by simp) f f =
      ⟪oneParticleRadialMap f+translatedLinearSource g 0 f •
          thresholdBoundedInverse e he g hg hs CD hCD hquad 0 (by simp)
            (thresholdKernelSourceVector e he g hg hs 0 (by simp)),
        thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)
          (oneParticleRadialMap f+translatedLinearSource g 0 f •
            thresholdBoundedInverse e he g hg hs CD hCD hquad 0 (by simp)
              (thresholdKernelSourceVector e he g hg hs 0 (by simp)))⟫_ℂ := by
  let B := thresholdBoundedOperator e he g hg hs CD hCD hquad 0 (by simp)
  let R := thresholdBoundedInverse e he g hg hs CD hCD hquad 0 (by simp)
  let b := thresholdKernelSourceVector e he g hg hs 0 (by simp)
  have hBx : B (R b) = b := by
    have hI := (thresholdBoundedInverse_spec e he g hg hs CD hCD hquad 0 (by simp) hN).2.1
    exact congrArg (fun T : GW.OnePhonon →L[ℂ] GW.OnePhonon => T b) hI
  exact (translatedThresholdForm_polarized e he g hg hs CD hCD hquad
    hquarter heLower hquadratic 0 (by simp) f f).trans
      (po02_complete_square B b (R b) (oneParticleRadialMap f) (translatedLinearSource g 0 f)
        (kernelConstant e he g hg hs 0)
        (thresholdBoundedOperator_selfadjoint e he g hg hs CD hCD hquad 0 (by simp)) hBx hSat)

include hquarter heLower hquadratic hN hSat in
theorem translatedThresholdForm_zero_nonnegative (f : OneParticleEnergySpace 0) :
    0 ≤ (translatedThresholdForm e he g hquarter heLower hquadratic 0 (by simp) f f).re := by
  rw [translatedThresholdForm_zero_square e he g hg hs CD hCD hquad hquarter heLower hquadratic hN hSat]
  exact (by positivity : (0 : ℝ) ≤ ‖oneParticleRadialMap f+translatedLinearSource g 0 f •
    thresholdBoundedInverse e he g hg hs CD hCD hquad 0 (by simp)
      (thresholdKernelSourceVector e he g hg hs 0 (by simp))‖^2/2).trans
    (thresholdBoundedOperator_quadratic_lower e he g hg hs CD hCD hquad 0 (by simp) hN _)

end Froehlich
