import Froehlich.Nodes.UV01EnergyInverse

/-! Fixed common graph coordinates on bounded momentum sets. Both source
and target are the original high energy spaces, with true inverse changes. -/
noncomputable section
namespace Froehlich

def highEnergyCoordinateChange (P Q : GW.Space) (n : ℕ) :
    HighEnergySpace Q n →L[ℂ] HighEnergySpace P n :=
  ((energyCoordinateChange P Q).comp (HighEnergySpace Q n).subtypeL).codRestrict _ (by
    intro u
    apply (highEnergy_mem_iff P n _).mpr
    apply energyEmbedding_injective P
    change energyEmbedding P (energyHighProjection P n (energyCoordinateChange P Q u)) =
      energyEmbedding P (energyCoordinateChange P Q u)
    rw [energyHighProjection_intertwines,energyCoordinateChange_intertwines,
      ← energyHighProjection_intertwines,(highEnergy_mem_iff Q n u).mp u.property])

theorem highEnergyCoordinateChange_physical (P Q : GW.Space) (n : ℕ) (u : HighEnergySpace Q n) :
    highEnergyEmbedding P n (highEnergyCoordinateChange P Q n u) = highEnergyEmbedding Q n u := by
  apply Subtype.ext
  exact energyCoordinateChange_intertwines P Q u

theorem highEnergyCoordinateChange_cancel (P Q : GW.Space) (n : ℕ) (u : HighEnergySpace P n) :
    highEnergyCoordinateChange P Q n (highEnergyCoordinateChange Q P n u) = u := by
  apply Subtype.ext
  apply energyEmbedding_injective P
  change energyEmbedding P (energyCoordinateChange P Q (energyCoordinateChange Q P u)) = energyEmbedding P u
  rw [energyCoordinateChange_intertwines,energyCoordinateChange_intertwines]

theorem highEnergyCoordinateChange_norm_le (P Q : GW.Space) (n : ℕ) :
    ‖highEnergyCoordinateChange P Q n‖ ≤ momentumChangeConstant P Q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  change ‖energyCoordinateChange P Q (u : EnergySpace Q)‖ ≤ _
  exact ((energyCoordinateChange P Q).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (energyCoordinateChange_norm_le P Q) (norm_nonneg u))

theorem highEnergyCoordinateChange_norm_sq (p0 p : GW.Space) (n : ℕ) (R : ℝ)
    (hR : 0 ≤ R) (hdist : ‖p0-p‖ ≤ R) :
    ‖highEnergyCoordinateChange (-p0) (-p) n‖^2 ≤ 2*(1+R^2) := by
  have h := (sq_le_sq₀ (norm_nonneg (highEnergyCoordinateChange (-p0) (-p) n))
    (Real.sqrt_nonneg _)).mpr (highEnergyCoordinateChange_norm_le (-p0) (-p) n)
  unfold momentumChangeConstant at h
  rw [Real.sq_sqrt (by positivity)] at h
  have he : -p0 - -p = -(p0-p) := by module
  rw [he,norm_neg] at h
  have hd := (sq_le_sq₀ (norm_nonneg (p0-p)) hR).mpr hdist
  linarith

variable (n : ℕ) (e : ℝ) (p0 p : GW.Space) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hsmall : auxiliaryResolventConstant * |g| ≤ 1/2)

def cutoffCommonEnergyInverse (Λ : GW.Operators.PositiveCutoff) :
    HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n :=
  (highEnergyCoordinateChange (-p0) (-p) n).comp
    ((cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ).comp
      (highEnergyCoordinateChange (-p0) (-p) n).adjoint)

def singularCommonEnergyInverse : HighEnergySpace (-p0) n →L[ℂ] HighEnergySpace (-p0) n :=
  (highEnergyCoordinateChange (-p0) (-p) n).comp
    ((auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall).comp
      (highEnergyCoordinateChange (-p0) (-p) n).adjoint)

theorem cutoffCommonEnergyInverse_error (Λ : GW.Operators.PositiveCutoff) (hΛ : 1 ≤ Λ.val)
    (R : ℝ) (hR : 0 ≤ R) (hdist : ‖p0-p‖ ≤ R) :
    ‖cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ -
      singularCommonEnergyInverse n e p0 p hn he g hg hsmall‖ ≤
      72*(1+R^2)*lyHighConstant * |g| / Real.sqrt Λ.val := by
  let B := highEnergyCoordinateChange (-p0) (-p) n
  let D := cutoffAuxiliaryEnergyInverse n e p hn he g hg hsmall Λ - auxiliaryCompressedEnergyInverse n e p hn he g hg hsmall
  have hd : cutoffCommonEnergyInverse n e p0 p hn he g hg hsmall Λ -
      singularCommonEnergyInverse n e p0 p hn he g hg hsmall = B.comp (D.comp B.adjoint) := by
    apply ContinuousLinearMap.ext
    intro u
    change B _-B _ = B (_-_)
    exact (B.map_sub _ _).symm
  have hp : ‖B‖*‖B.adjoint‖ ≤ 2*(1+R^2) := by
    rw [ContinuousLinearMap.adjoint.norm_map B,← pow_two]
    exact highEnergyCoordinateChange_norm_sq p0 p n R hR hdist
  have hD := cutoffAuxiliaryEnergyInverse_error n e p hn he g hg hsmall Λ hΛ
  rw [hd]
  calc
    _ ≤ ‖B‖*‖D.comp B.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖B‖*(‖D‖*‖B.adjoint‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg B)
    _ = (‖B‖*‖B.adjoint‖)*‖D‖ := by ring
    _ ≤ (2*(1+R^2))*‖D‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg D)
    _ ≤ (2*(1+R^2))*(36*lyHighConstant * |g| / Real.sqrt Λ.val) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

end Froehlich
