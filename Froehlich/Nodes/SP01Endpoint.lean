import Froehlich.Nodes.SP01Completion

/-! The left endpoint sign follows from the actual full-form lower bound
on the nonzero Schur vector. No vacuum operator-domain premise is used. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem vacuumSchurFunction_lowerEndpoint (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (hminus : -1 < nonvacuumThreshold g) (hsmall : sectorEnergyConstant*|g|^2 < 1) :
    0 < vacuumSchurFunction g P hg ⟨-1,hminus⟩ := by
  let lam : Set.Iio (nonvacuumThreshold g) := ⟨-1,hminus⟩
  let u := vacuumSchurVectorEnergy g P hg lam
  have hb := fiberForm_global_lower g P u hg
  have hn : 0 < ‖energyEmbedding P u‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (vacuumSchurVector_embedding_ne_zero g P hg lam))
  have hi : (⟪energyEmbedding P u,energyEmbedding P u⟫_ℂ).re =
      ‖energyEmbedding P u‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) (energyEmbedding P u)).symm
  have hc := congrArg Complex.re (vacuumSchurVector_completion g P hg lam)
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hc
  change ((fiberFormData g P none).form u u).re -
      (-1)* (⟪energyEmbedding P u,energyEmbedding P u⟫_ℂ).re =
      vacuumSchurFunction g P hg lam at hc
  rw [hi] at hc
  have hp : 0 < (1-sectorEnergyConstant*|g|^2)*‖energyEmbedding P u‖^2 :=
    mul_pos (sub_pos.mpr hsmall) hn
  change 0 < vacuumSchurFunction g P hg lam
  nlinarith

end Froehlich
