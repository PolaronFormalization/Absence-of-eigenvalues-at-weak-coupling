import Froehlich.Nodes.UV02NumberInverse
import Froehlich.Nodes.GW06Compression

/-! The same free shifted inverse on each actual closed high sector.
No new compressed free operator or graph library is introduced. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (P : GW.Space) (c : ℝ) (hc : 1 ≤ c) (n : ℕ)

theorem freeShiftInverse_preserves_high (f : HighSectorSpace n) :
    freeShiftInverse P c hc (f : GW.Fock.Carrier) ∈ HighSectorSpace n := by
  apply (highSector_mem_iff n _).mpr
  apply lp.ext
  funext m
  rw [highSectorProjection_apply]
  split_ifs with hnm
  · rfl
  · have hf : (f : GW.Fock.Carrier) m=0 := by
      have h := congrArg (fun v : GW.Fock.Carrier => v m) ((highSector_mem_iff n f).mp f.property)
      rw [highSectorProjection_apply,if_neg hnm] at h
      exact h.symm
    apply Eq.symm
    apply (physicalSector m).injective
    apply Lp.ext
    rw [map_zero]
    have hw := freeShiftInverse_weighted_ae P c hc (f : GW.Fock.Carrier) m
    rw [hf,map_zero] at hw
    filter_upwards [hw,Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure m)] with K hw hz
    have hW : (freeShiftWeight P c m K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (ne_of_gt (zero_lt_one.trans_le (freeShiftWeight_lower P c hc m K)))
    have hm : physicalSector m (freeShiftInverse P c hc (f : GW.Fock.Carrier) m) K=0 :=
      (mul_eq_zero.mp (hw.trans hz)).resolve_left hW
    exact hm.trans hz.symm

def freeShiftHighInverse : HighSectorSpace n →L[ℂ] HighSectorSpace n :=
  ((freeShiftInverse P c hc).comp (HighSectorSpace n).subtypeL).codRestrict _
    (freeShiftInverse_preserves_high P c hc n)

@[simp] theorem freeShiftHighInverse_val (f : HighSectorSpace n) :
    (freeShiftHighInverse P c hc n f : GW.Fock.Carrier)=freeShiftInverse P c hc (f : GW.Fock.Carrier) := rfl

def freeShiftHighEnergyInverse : HighSectorSpace n →L[ℂ] HighEnergySpace P n :=
  ((freeShiftEnergyInverse P c hc).comp (HighSectorSpace n).subtypeL).codRestrict _ (by
    intro f
    apply (highEnergy_mem_iff P n _).mpr
    apply energyEmbedding_injective P
    rw [energyHighProjection_intertwines]
    change highSectorProjection n (energyEmbedding P (freeShiftEnergyInverse P c hc (f : GW.Fock.Carrier)))=
      energyEmbedding P (freeShiftEnergyInverse P c hc (f : GW.Fock.Carrier))
    rw [freeShiftEnergyInverse_physical]
    exact (highSector_mem_iff n _).mp (freeShiftInverse_preserves_high P c hc n f))

theorem freeShiftHighEnergyInverse_physical (f : HighSectorSpace n) :
    highEnergyEmbedding P n (freeShiftHighEnergyInverse P c hc n f)=freeShiftHighInverse P c hc n f := by
  apply Subtype.ext
  exact freeShiftEnergyInverse_physical P c hc f

theorem freeShiftHighEnergyInverse_norm_le (f : HighSectorSpace n) :
    ‖freeShiftHighEnergyInverse P c hc n f‖ ≤ (Real.sqrt c)⁻¹*‖f‖ :=
  freeShiftEnergyInverse_norm_le P c hc f

end Froehlich
