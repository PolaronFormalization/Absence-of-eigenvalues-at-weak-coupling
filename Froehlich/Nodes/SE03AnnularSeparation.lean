import Froehlich.Nodes.SE03AnnularTest
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal Classical
namespace Froehlich

/-- Testing the annular difference against itself in the actual L2 space. -/
theorem se03_annular_separation (M : ℝ) (d t : GW.OnePhonon) (a : ℂ)
    (htest : ∀ z : GW.OnePhonon, (∀ᵐ q ∂volume, q ∉ se03Annulus M → z q = 0) →
      ⟪z,d⟫_ℂ = ⟪z,t⟫_ℂ*a) :
    ∀ᵐ q ∂volume, q ∈ se03Annulus M → d q = a*t q := by
  have hA : MeasurableSet (se03Annulus M) :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  let x := d-a • t
  have hmem : MemLp ((se03Annulus M).indicator (fun q => x q)) 2 volume :=
    (Lp.memLp x).indicator hA.nullMeasurableSet
  let z : GW.OnePhonon := hmem.toLp ((se03Annulus M).indicator (fun q => x q))
  have hz : z =ᵐ[volume] (se03Annulus M).indicator (fun q => x q) := hmem.coeFn_toLp
  have hzsupport : ∀ᵐ q ∂volume, q ∉ se03Annulus M → z q = 0 := by
    filter_upwards [hz] with q hq hn
    rw [hq,Set.indicator_of_notMem hn]
  have hx : ⟪z,x⟫_ℂ = 0 := by
    change ⟪z,d-a • t⟫_ℂ = 0
    rw [inner_sub_right,inner_smul_right,htest z hzsupport]
    ring
  have hinner : ⟪z,x⟫_ℂ = ⟪z,z⟫_ℂ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hz] with q hq
    by_cases hqin : q ∈ se03Annulus M
    · rw [Set.indicator_of_mem hqin] at hq
      rw [hq]
    · rw [Set.indicator_of_notMem hqin] at hq
      rw [hq]
      simp only [inner_zero_left]
  have hz0 : z = 0 := inner_self_eq_zero.mp (hinner.symm.trans hx)
  filter_upwards [hz,Lp.coeFn_sub d (a • t),Lp.coeFn_smul a t,
    Lp.coeFn_zero ℂ 2 (volume : Measure GW.Space)] with q hq hsub hsmul hzeroLp hqin
  have hzero : z q = 0 := by rw [hz0]; exact hzeroLp
  rw [hzero,Set.indicator_of_mem hqin] at hq
  change 0 = (d-a • t) q at hq
  rw [hsub,Pi.sub_apply,hsmul,Pi.smul_apply,smul_eq_mul] at hq
  exact sub_eq_zero.mp hq.symm

end Froehlich
