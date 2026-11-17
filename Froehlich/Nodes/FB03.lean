import Froehlich.Nodes.FB02

/-! FB03 (`lem:sectorbounds`): the prescribed coupling-independent constants
and uniform bounds for the actual fiber form. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

def sectorEnergyConstant : ℝ := 2*lySmallConstant
def sectorLinearConstant : ℝ := 1+lySmallConstant
def sectorQuadraticConstant : ℝ := 4*lySmallConstant
def nonvacuumThreshold (g : ℝ) : ℝ := 1-sectorLinearConstant*|g|

theorem sectorEnergyConstant_pos : 0 < sectorEnergyConstant :=
  mul_pos (by norm_num) lySmallConstant_pos

theorem fiberForm_global_lower (g : ℝ) (P : GW.Space) (u : EnergySpace P)
    (hg : |g| ≤ 1/4) :
    -(sectorEnergyConstant*|g|^2)*‖energyEmbedding P u‖^2 ≤
      ((fiberFormData g P none).form u u).re := by
  have hb := singular_liebYamazaki_small g P u (1/2 : ℝ) (by norm_num) (by norm_num)
    (hg.trans (by norm_num : (1/4 : ℝ) ≤ 1/2))
  have hl := neg_le_of_abs_le ((Complex.abs_re_le_norm (singularInteraction g P u u)).trans hb)
  have hn := freeEnergy_nonneg P (energyEmbedding P u)
  rw [fiberFormData_singular_apply,Complex.add_re,freeFiberForm_physical_energy]
  dsimp only [sectorEnergyConstant]
  rw [sq_abs]
  nlinarith

theorem fiberForm_linear_lower (g : ℝ) (P : GW.Space) (u : EnergySpace P)
    (hg : |g| ≤ 1/4) :
    (1-|g|)*freeEnergy P (energyEmbedding P u) -
      lySmallConstant * |g| * ‖energyEmbedding P u‖^2 ≤ ((fiberFormData g P none).form u u).re := by
  by_cases hz : g = 0
  · subst g
    rw [fiberFormData_singular_apply,singularInteraction_zero_coupling]
    simp only [abs_zero,sub_zero,mul_zero,zero_mul,ContinuousLinearMap.zero_apply,add_zero,one_mul]
    exact (freeFiberForm_physical_energy P u).ge
  have hs : 0 < |g| := abs_pos.mpr hz
  have hb := singular_liebYamazaki_small g P u |g| hs
    (hg.trans (by norm_num : (1/4 : ℝ) ≤ 1)) le_rfl
  have hratio : lySmallConstant*g^2/|g| = lySmallConstant * |g| := by
    rw [← sq_abs g]
    field_simp [ne_of_gt hs]
    <;> ring
  rw [hratio] at hb
  have hl := neg_le_of_abs_le ((Complex.abs_re_le_norm (singularInteraction g P u u)).trans hb)
  rw [fiberFormData_singular_apply,Complex.add_re,freeFiberForm_physical_energy]
  nlinarith

end Froehlich
