import Froehlich.Nodes.FB02SourceEstimates
import Froehlich.Nodes.FB02Zero

/-! Fixed source constants, chosen before any momentum, coupling or ground energy. -/
noncomputable section
namespace Froehlich

def phiMixedConstant : ℝ := 2*max 1 lySmallConstant
def weakResolventConstant : ℝ := 3*phiMixedConstant
def dispersionConstant : ℝ := 16*phiMixedConstant^2

theorem phiMixedConstant_pos : 0 < phiMixedConstant :=
  mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left _ _))

theorem singularInteraction_diagonal_small (g : ℝ) (P : GW.Space) (u : EnergySpace P)
    (hg1 : |g| ≤ 1) :
    ‖singularInteraction g P u u‖ ≤ (max 1 lySmallConstant * |g|)*‖u‖^2 := by
  by_cases hg : g = 0
  · subst g
    rw [singularInteraction_zero_coupling]
    simp
  have hs : 0 < |g| := abs_pos.mpr hg
  have h := singular_liebYamazaki_small g P u |g| hs hg1 le_rfl
  have hr : lySmallConstant*g^2/|g| = lySmallConstant*|g| := by
    rw [← sq_abs g]
    field_simp [ne_of_gt hs]
    <;> ring
  rw [hr] at h
  have hE := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) lySmallConstant)
    (mul_nonneg (abs_nonneg g) (freeEnergy_nonneg P (energyEmbedding P u)))
  have hU := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) lySmallConstant)
    (mul_nonneg (abs_nonneg g) (sq_nonneg ‖energyEmbedding P u‖))
  have he : freeEnergy P (energyEmbedding P u) + ‖energyEmbedding P u‖^2 = ‖u‖^2 := by
    linarith [energyEmbedding_norm_identity P u]
  calc
    _ ≤ |g| *freeEnergy P (energyEmbedding P u) +
        lySmallConstant*|g| *‖energyEmbedding P u‖^2 := h
    _ ≤ max 1 lySmallConstant*(|g| *freeEnergy P (energyEmbedding P u)) +
        max 1 lySmallConstant*(|g| *‖energyEmbedding P u‖^2) := by
      simpa only [one_mul, mul_assoc] using add_le_add hE hU
    _ = (max 1 lySmallConstant*|g|)*
        (freeEnergy P (energyEmbedding P u)+‖energyEmbedding P u‖^2) := by ring
    _ = _ := by rw [he]

theorem singularInteraction_mixed_small (g : ℝ) (P : GW.Space) (w u : EnergySpace P)
    (hg1 : |g| ≤ 1) :
    ‖singularInteraction g P w u‖ ≤ phiMixedConstant*|g| *‖w‖*‖u‖ := by
  have h := diagonal_to_mixed_bound (GW.Operators.boundedFormAlgebraic (singularInteraction g P))
    (singularInteraction_hermitian g P)
    (mul_nonneg (zero_le_one.trans (le_max_left _ _)) (abs_nonneg g))
    (fun x => singularInteraction_diagonal_small g P x hg1) w u
  exact h.trans_eq (by unfold phiMixedConstant; ring)

end Froehlich
