import Froehlich.Nodes.SP01Endpoint
import Mathlib.Topology.Order.IntermediateValue

/-! Existence on the closed source interval, strict exclusion of its left
endpoint, and uniqueness on the whole coercive interval. -/
noncomputable section
namespace Froehlich

theorem vacuumSchurFunction_existsUnique_root (g : ℝ) (P : GW.Space) (hg : |g| ≤ 1/4)
    (hminus : -1 < nonvacuumThreshold g) (hP : ‖P‖^2 < nonvacuumThreshold g)
    (hsmall : sectorEnergyConstant*|g|^2 < 1) :
    ∃ e : Set.Iio (nonvacuumThreshold g), -1 < (e : ℝ) ∧ (e : ℝ) ≤ ‖P‖^2 ∧
      vacuumSchurFunction g P hg e = 0 ∧
      ∀ a, vacuumSchurFunction g P hg a = 0 → a = e := by
  let K := Set.Icc (-1 : ℝ) (‖P‖^2)
  have hab : (-1 : ℝ) ≤ ‖P‖^2 := by nlinarith [sq_nonneg ‖P‖]
  let a : K := ⟨-1,le_rfl,hab⟩
  let b : K := ⟨‖P‖^2,hab,le_rfl⟩
  let embed : K → Set.Iio (nonvacuumThreshold g) :=
    fun x => ⟨x,lt_of_le_of_lt x.property.2 hP⟩
  have hembed : Continuous embed := by
    change Continuous (fun x : K => (⟨(x : ℝ),lt_of_le_of_lt x.property.2 hP⟩ :
      Set.Iio (nonvacuumThreshold g)))
    exact (continuous_subtype_val : Continuous (fun x : K => (x : ℝ))).subtype_mk
      (fun x : K => (lt_of_le_of_lt x.property.2 hP : (x : ℝ) < nonvacuumThreshold g))
  let f : K → ℝ := fun x => vacuumSchurFunction g P hg (embed x)
  have hf : Continuous f := (vacuumSchurFunction_continuous g P hg).comp hembed
  have ha : 0 < f a := vacuumSchurFunction_lowerEndpoint g P hg hminus hsmall
  have hb : f b ≤ 0 := vacuumSchurFunction_upperEndpoint g P hg hP
  letI : PreconnectedSpace K := Subtype.preconnectedSpace isPreconnected_Icc
  obtain ⟨x,hx⟩ := intermediate_value_univ₂ (a := a) (b := b)
    (f := fun _ : K => (0 : ℝ)) (g := f) continuous_const hf ha.le hb
  have hroot : vacuumSchurFunction g P hg (embed x) = 0 := hx.symm
  have hne : (x : ℝ) ≠ -1 := by
    intro h
    have he : embed x = (⟨-1,hminus⟩ : Set.Iio (nonvacuumThreshold g)) := Subtype.ext h
    rw [he] at hroot
    exact (ne_of_gt (vacuumSchurFunction_lowerEndpoint g P hg hminus hsmall)) hroot
  refine ⟨embed x,?_,x.property.2,hroot,?_⟩
  · exact lt_of_le_of_ne x.property.1 (Ne.symm hne)
  · intro y hy
    exact vacuumSchurFunction_root_unique g P hg y (embed x) hy hroot

end Froehlich
