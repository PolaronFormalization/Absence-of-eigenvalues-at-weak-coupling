import Froehlich.Nodes.FB02MixedError
import Froehlich.Nodes.FB01

/-! FB02A's estimates with exactly the source parameter ranges. -/
noncomputable section
namespace Froehlich

theorem singular_liebYamazaki (g : ℝ) (P : GW.Space) (u : EnergySpace P)
    (theta : ℝ) (ht : 0 < theta) (_ht1 : theta ≤ 1) :
    ‖singularInteraction g P u u‖ ≤ theta * freeEnergy P (energyEmbedding P u) +
      lyRemainderConstant*(g^2/theta+g^4/theta^3)*‖energyEmbedding P u‖^2 :=
  liebYamazaki_singular g P u theta ht

theorem singular_liebYamazaki_small (g : ℝ) (P : GW.Space) (u : EnergySpace P)
    (theta : ℝ) (ht : 0 < theta) (_ht1 : theta ≤ 1) (hg : |g| ≤ theta) :
    ‖singularInteraction g P u u‖ ≤ theta * freeEnergy P (energyEmbedding P u) +
      (lySmallConstant*g^2/theta)*‖energyEmbedding P u‖^2 :=
  liebYamazaki_singular_small g P u theta ht hg

theorem singular_cutoff_error (g Λ : ℝ) (hΛ : 1 ≤ Λ) (P : GW.Space) (w u : EnergySpace P) :
    ‖(singularInteraction g P - cutoffInteractionForm g Λ (zero_lt_one.trans_le hΛ) P) w u‖ ≤
      (lyHighConstant*|g|/Real.sqrt Λ)*‖w‖*‖u‖ :=
  singularInteraction_mixed_error g Λ (zero_lt_one.trans_le hΛ) P w u

end Froehlich
