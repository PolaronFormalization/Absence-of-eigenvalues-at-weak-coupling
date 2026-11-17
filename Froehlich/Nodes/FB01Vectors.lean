import Froehlich.Nodes.FB01FormFactors

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Froehlich

def lyDirection (j : Fin 3) (k : GW.Space) : ℂ := ((k j / ‖k‖ : ℝ) : ℂ)

theorem lyDirection_measurable (j : Fin 3) : Measurable (lyDirection j) :=
  Complex.continuous_ofReal.measurable.comp
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) j).measurable.div measurable_norm)

theorem lyDirection_bound (j : Fin 3) (k : GW.Space) : ‖lyDirection j k‖ ≤ 1 := by
  simp only [lyDirection, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (norm_nonneg k)]
  by_cases hk : ‖k‖ = 0
  · simp only [hk, div_zero, zero_le_one]
  · have hp : 0 < ‖k‖ := lt_of_le_of_ne (norm_nonneg k) (Ne.symm hk)
    apply (div_le_one hp).mpr
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le k j

def lyVectorCoefficient (Λ : ℝ) (j : Fin 3) (k : GW.Space) : ℂ :=
  if ‖k‖ ≤ Λ then lyDirection j k else 0

theorem lyVectorCoefficient_measurable (Λ : ℝ) (j : Fin 3) :
    Measurable (lyVectorCoefficient Λ j) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const)
    (lyDirection_measurable j) measurable_const

theorem lyVectorCoefficient_bound (Λ : ℝ) (j : Fin 3) (k : GW.Space) :
    ‖lyVectorCoefficient Λ j k‖ ≤ 1 := by
  unfold lyVectorCoefficient
  split_ifs
  · exact lyDirection_bound j k
  · simp

def lyVectorL2 (g L Λ : ℝ) (hL : 0 < L) (j : Fin 3) : GW.OnePhonon :=
  GW.Analysis.boundedMultiplier (lyVectorCoefficient Λ j) (lyVectorCoefficient_measurable Λ j)
    (Eventually.of_forall (lyVectorCoefficient_bound Λ j)) (lyRadialTailL2 g L hL)

def lyVectorFunction (g L Λ : ℝ) (j : Fin 3) (k : GW.Space) : ℂ :=
  if L < ‖k‖ ∧ ‖k‖ ≤ Λ then ((g * k j / ‖k‖^3 : ℝ) : ℂ) else 0

theorem lyVectorL2_ae (g L Λ : ℝ) (hL : 0 < L) (j : Fin 3) :
    lyVectorL2 g L Λ hL j =ᵐ[volume] lyVectorFunction g L Λ j := by
  have ha := GW.Analysis.boundedMultiplier_ae (lyVectorCoefficient Λ j)
    (lyVectorCoefficient_measurable Λ j)
    (Eventually.of_forall (lyVectorCoefficient_bound Λ j)) (lyRadialTailL2 g L hL)
  filter_upwards [ha, lyRadialTailL2_ae g L hL] with k hk hb
  change lyVectorL2 g L Λ hL j k = _
  have he : lyVectorL2 g L Λ hL j k = lyVectorCoefficient Λ j k • lyRadialTail g L k :=
    hk.symm.trans (congrArg (lyVectorCoefficient Λ j k • ·) hb)
  rw [he]
  by_cases hlo : L < ‖k‖ <;> by_cases hhi : ‖k‖ ≤ Λ
  · have hin : L < ‖k‖ ∧ ‖k‖ ≤ Λ := ⟨hlo,hhi⟩
    simp only [lyVectorCoefficient, if_pos hhi, lyDirection, lyRadialTail, if_pos hlo,
      lyVectorFunction, if_pos hin, smul_eq_mul, ← Complex.ofReal_mul]
    congr 1
    have hn : ‖k‖ ≠ 0 := ne_of_gt (hL.trans hlo)
    field_simp [hn]
    <;> ring
  · simp [lyVectorCoefficient, lyRadialTail, lyVectorFunction, hlo, hhi]
  · simp [lyVectorCoefficient, lyRadialTail, lyVectorFunction, hlo, hhi]
  · simp [lyVectorCoefficient, lyRadialTail, lyVectorFunction, hlo, hhi]

theorem lyVectorL2_norm_le (g L Λ : ℝ) (hL : 0 < L) (j : Fin 3) :
    ‖lyVectorL2 g L Λ hL j‖ ≤ ‖lyRadialTailL2 g L hL‖ := by
  let T : GW.OnePhonon →L[ℂ] GW.OnePhonon :=
    GW.Analysis.boundedMultiplier (lyVectorCoefficient Λ j) (lyVectorCoefficient_measurable Λ j)
      (Eventually.of_forall (lyVectorCoefficient_bound Λ j))
  have hT : ‖T‖ ≤ 1 := GW.Analysis.boundedMultiplier_opNorm_le _ _ zero_le_one _
  have hb : ‖T‖ * ‖lyRadialTailL2 g L hL‖ ≤ ‖lyRadialTailL2 g L hL‖ := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hT (norm_nonneg (lyRadialTailL2 g L hL)))
  exact (T.le_opNorm (lyRadialTailL2 g L hL)).trans hb

theorem lyVectorL2_norm_sq (g L Λ : ℝ) (hL : 0 < L) (j : Fin 3) :
    ‖lyVectorL2 g L Λ hL j‖^2 ≤ 14 * GW.Model.unitBallVolume * g^2 / L :=
  ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (lyVectorL2_norm_le g L Λ hL j)).trans
    (lyRadialTailL2_norm_sq g L hL)

theorem lyVectorL2_bounded_support (g L Λ : ℝ) (hL : 0 < L) (j : Fin 3) :
    ∀ᵐ k ∂(volume : Measure GW.Space), Λ < ‖k‖ → lyVectorL2 g L Λ hL j k = 0 := by
  filter_upwards [lyVectorL2_ae g L Λ hL j] with k hk
  intro hout
  rw [hk]
  simp only [lyVectorFunction, show ¬(L < ‖k‖ ∧ ‖k‖ ≤ Λ) from fun h => (not_le.mpr hout) h.2,
    if_false]

theorem lyVectorL2_sum_norm_sq (g L Λ : ℝ) (hL : 0 < L) :
    (∑ j : Fin 3, ‖lyVectorL2 g L Λ hL j‖^2) ≤
      42 * GW.Model.unitBallVolume * g^2 / L := by
  calc
    _ ≤ ∑ _j : Fin 3, (14 * GW.Model.unitBallVolume * g^2 / L) :=
      Finset.sum_le_sum (fun j _ => lyVectorL2_norm_sq g L Λ hL j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Froehlich
