import Froehlich.Nodes.PT01CoreWeakInverse
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Pointwise inversion of the genuine energy-valued weak residual, with
one almost-everywhere set and the literal physical cutoff resolvent. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem cutoff_fixedWeakField_physical_ae (m : ℕ) (e : ℝ) (p0 : GW.Space)
    (hm : m ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Lambda : GW.Operators.PositiveCutoff)
    (K : Set GW.Space) (q : GW.Space → GW.Space)
    (U : Lp (HighEnergySpace (-p0) m) 2 ((volume : Measure GW.Space).restrict K))
    (F : Lp (HighSectorSpace m) 2 ((volume : Measure GW.Space).restrict K))
    (hEq : ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      cutoffCommonFormOperator m e p0 (q k) hm he g Lambda (U k)=(highEnergyEmbedding (-p0) m).adjoint (F k)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      highEnergyEmbedding (-p0) m (U k)=cutoffAuxiliaryResolvent m e (q k) he Lambda g hg hs (F k) := by
  filter_upwards [hEq] with k hk
  exact cutoff_fixedWeakSolution_physical m e p0 (q k) hm he g hg hs Lambda (U k) (F k) hk

theorem cutoff_fixedWeakField_Lp (m : ℕ) (e : ℝ) (p0 : GW.Space)
    (hm : m ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (Lambda : GW.Operators.PositiveCutoff)
    (K : Set GW.Space) (q : GW.Space → GW.Space)
    (U : Lp (HighEnergySpace (-p0) m) 2 ((volume : Measure GW.Space).restrict K))
    (F G : Lp (HighSectorSpace m) 2 ((volume : Measure GW.Space).restrict K))
    (hEq : ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      cutoffCommonFormOperator m e p0 (q k) hm he g Lambda (U k)=(highEnergyEmbedding (-p0) m).adjoint (F k))
    (hG : G =ᵐ[(volume : Measure GW.Space).restrict K]
      (fun k => cutoffAuxiliaryResolvent m e (q k) he Lambda g hg hs (F k))) :
    (highEnergyEmbedding (-p0) m).compLp U=G := by
  apply Lp.ext
  filter_upwards [(highEnergyEmbedding (-p0) m).coeFn_compLp U,
    cutoff_fixedWeakField_physical_ae m e p0 hm he g hg hs Lambda K q U F hEq,hG] with k hj hu hgk
  rw [hj,hu,hgk]

end Froehlich
