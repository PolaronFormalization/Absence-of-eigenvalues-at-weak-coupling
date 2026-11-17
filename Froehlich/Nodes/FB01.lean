import Froehlich.Nodes.FB01LiebYamazakiExtension
import Froehlich.Nodes.FB01TailSharp

/-! FB01's source statements with their prescribed parameter ranges.
The implementation lemmas permit wider ranges; these exports retain the TeX hypotheses. -/
noncomputable section
namespace Froehlich

def lySmallConstant : ℝ := 2*lyRemainderConstant

theorem lySmallConstant_pos : 0 < lySmallConstant :=
  mul_pos (by norm_num) lyRemainderConstant_pos

theorem finiteCutoff_liebYamazaki (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (x : EnergySpace P) (theta : ℝ) (ht : 0 < theta) (_ht1 : theta ≤ 1) :
    ‖cutoffInteractionForm g Λ hΛ P x x‖ ≤ theta * freeEnergy P (energyEmbedding P x) +
      lyRemainderConstant*(g^2/theta+g^4/theta^3)*‖energyEmbedding P x‖^2 :=
  liebYamazaki_cutoff g Λ hΛ P x theta ht

theorem finiteCutoff_liebYamazaki_small (g Λ : ℝ) (hΛ : 0 < Λ) (P : GW.Space)
    (x : EnergySpace P) (theta : ℝ) (ht : 0 < theta) (_ht1 : theta ≤ 1) (hg : |g| ≤ theta) :
    ‖cutoffInteractionForm g Λ hΛ P x x‖ ≤ theta * freeEnergy P (energyEmbedding P x) +
      (lySmallConstant*g^2/theta)*‖energyEmbedding P x‖^2 :=
  liebYamazaki_cutoff_small g Λ hΛ P x theta ht hg

theorem finiteCutoff_tail (g L Λ : ℝ) (hL : 1 ≤ L) (hLΛ : L ≤ Λ)
    (P : GW.Space) (x : EnergySpace P) :
    ‖cutoffInteractionForm g Λ ((zero_lt_one.trans_le hL).trans_le hLΛ) P x x -
      cutoffInteractionForm g L (zero_lt_one.trans_le hL) P x x‖ ≤
      lyHighConstant*|g|/Real.sqrt L * energyKineticNorm P x *
        ‖GW.Fock.shiftedNumberPower GW.Fock.Sector (1/2)
          (GW.Fock.shiftedNumberInput GW.Fock.Sector (1/2) (by positivity)
            (numberFormRootInput (energyNumberCoordinates P x)))‖ :=
  lyHighForm_energy_sharp_actual g L Λ (zero_lt_one.trans_le hL) hLΛ P x

end Froehlich
