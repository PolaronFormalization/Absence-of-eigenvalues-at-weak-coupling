import Froehlich.Nodes.RS02SourceJetsRemainder
import Froehlich.Nodes.CA02FixedEnergyDerivative

set_option autoImplicit false

/-! Native L2-norm source Taylor remainders, with the explicit integrable
AN02 majorant already established, and genuine coordinate derivatives. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Froehlich

def auxiliarySourceJetChartL2 (is : List (Fin 3)) (g e : ℝ) (q : Fin 3 → ℝ)
    (he : e ≤ 0) : GW.OnePhonon :=
  auxiliarySourceJetL2 is g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he

theorem auxiliarySourceJetChartL2_ae (is : List (Fin 3)) (g e : ℝ) (q : Fin 3 → ℝ) (he : e ≤ 0) :
    (auxiliarySourceJetChartL2 is g e q he : GW.Space → ℂ) =ᵐ[volume]
      auxiliarySourceJetChartFunction is g e q :=
  auxiliarySourceJetL2_ae is g e ((EuclideanSpace.equiv (Fin 3) ℝ).symm q) he

theorem auxiliarySourceJetChartL2_coordinate_remainder (is : List (Fin 3))
    (g e : ℝ) (he : e ≤ 0) (q : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) (ht : |t-q i| ≤ 1) :
    ‖auxiliarySourceJetChartL2 is g e (Function.update q i t) he-
      auxiliarySourceJetChartL2 is g e q he-
      (t-q i) • auxiliarySourceJetChartL2 (i::is) g e q he‖ ≤
      (sourceJetRemainderCoefficient is.length*‖t-q i‖^2)*‖auxiliarySourceJetChartL2 [] g e q he‖ := by
  let u := auxiliarySourceJetChartL2 is g e (Function.update q i t) he
  let v := auxiliarySourceJetChartL2 is g e q he
  let w := auxiliarySourceJetChartL2 (i::is) g e q he
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [auxiliarySourceJetChartL2_ae is g e (Function.update q i t) he,
    auxiliarySourceJetChartL2_ae is g e q he,auxiliarySourceJetChartL2_ae (i::is) g e q he,
    auxiliarySourceJetChartL2_ae [] g e q he,
    Lp.coeFn_sub (u-v) ((t-q i) • w),Lp.coeFn_sub u v,Lp.coeFn_smul (t-q i) w]
      with k hu hv hw hbase hsub hsub' hsmul
  change ‖(u-v-(t-q i) • w) k‖ ≤ _
  rw [hsub]
  change ‖(u-v) k-((t-q i) • w) k‖ ≤ _
  rw [hsub',hsmul]
  change ‖u k-v k-(t-q i) • w k‖ ≤ _
  rw [hu,hv,hw,hbase]
  simpa only [Real.norm_eq_abs] using
    auxiliarySourceJetChartFunction_coordinate_remainder is g e he q i t ht k

theorem auxiliarySourceJetChartL2_hasDerivAt_update (is : List (Fin 3))
    (g e : ℝ) (he : e ≤ 0) (q : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => auxiliarySourceJetChartL2 is g e (Function.update q i t) he)
      (auxiliarySourceJetChartL2 (i::is) g e q he) (q i) := by
  apply hasDerivAt_of_eventually_quadratic_remainder _ _ _
    (sourceJetRemainderCoefficient is.length*‖auxiliarySourceJetChartL2 [] g e q he‖)
  have hnear : ∀ᶠ t : ℝ in 𝓝 (q i), ‖t-q i‖ < 1 :=
    (continuousAt_id.sub continuousAt_const).norm.tendsto.eventually_lt_const (by simp)
  filter_upwards [hnear] with t ht
  have h := auxiliarySourceJetChartL2_coordinate_remainder is g e he q i t
    (by simpa only [Real.norm_eq_abs] using ht.le)
  calc
    _ ≤ (sourceJetRemainderCoefficient is.length*‖t-q i‖^2)*‖auxiliarySourceJetChartL2 [] g e q he‖ := by
      simpa only [Function.update_eq_self] using! h
    _ = _ := by ring

end Froehlich
