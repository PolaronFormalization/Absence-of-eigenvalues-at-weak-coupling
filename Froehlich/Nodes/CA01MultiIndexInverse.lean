import Froehlich.Nodes.CA01MultiIndexConstants
import Froehlich.Nodes.CA01InverseFamily

/-! Exact nonzero multi-index recurrence for the chosen bounded inverse.
All operators use the same complex-linear endomorphism carrier, with its
native real normed algebra structure for parameter differentiation. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
open scoped BoundedEndReal
variable {d : ℕ} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem actualInverseFamily_coordinateMultiPartial
    (M R : (Fin d → ℝ) → E →L[ℂ] E)
    (alpha : Fin d → ℕ) (halpha : alpha ≠ 0)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hM : ContDiffOn ℝ (∑ k, alpha k : ℕ) M S)
    (hinv : ∀ p ∈ S, M p * R p = 1 ∧ R p * M p = 1)
    (q : Fin d → ℝ) (hq : q ∈ S) :
    coordinateMultiPartial alpha R q = -R q *
      ∑ beta ∈ (multiIndexBox alpha).erase 0, multiIndexBinomial alpha beta •
        (coordinateMultiPartial beta M q *
          coordinateMultiPartial (fun k => alpha k-beta k) R q) := by
  have hR : ContDiffOn ℝ (∑ k, alpha k : ℕ) R S := by
    intro p hp
    have hi : ∀ᶠ r in 𝓝 p, M r * R r = 1 ∧ R r * M r = 1 := by
      filter_upwards [hS.mem_nhds hp] with r hr
      exact hinv r hr
    exact (actualInverseFamily_contDiffAt M R p _
      ((hM p hp).contDiffAt (hS.mem_nhds hp)) hi).contDiffWithinAt
  have hzero : coordinateMultiPartial alpha (fun p => M p * R p) q = 0 := by
    calc
      _ = coordinateMultiPartial alpha (fun _ => (1 : E →L[ℂ] E)) q :=
        coordinateBlocksPartial_congr_of_isOpen _ _ _ S hS (fun p hp => (hinv p hp).1) hq
      _ = 0 := coordinateMultiPartial_const alpha halpha 1 q
  have hprod := coordinateMultiPartial_realBilinear alpha
    (ContinuousLinearMap.mul ℝ (E →L[ℂ] E)) M R S hS hM hR q hq
  change coordinateMultiPartial alpha (fun p => M p * R p) q =
    ∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
      (coordinateMultiPartial beta M q * coordinateMultiPartial (fun k => alpha k-beta k) R q) at hprod
  have hsum : (∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
      (coordinateMultiPartial beta M q * coordinateMultiPartial (fun k => alpha k-beta k) R q)) = 0 :=
    hprod.symm.trans hzero
  rw [multiIndexBox_sum_split_zero] at hsum
  simp only [multiIndexBinomial_zero,coordinateMultiPartial_zero,one_smul,Pi.zero_apply,Nat.sub_zero] at hsum
  have hterm : M q * coordinateMultiPartial alpha R q =
      -(∑ beta ∈ (multiIndexBox alpha).erase 0, multiIndexBinomial alpha beta •
        (coordinateMultiPartial beta M q * coordinateMultiPartial (fun k => alpha k-beta k) R q)) :=
    eq_neg_iff_add_eq_zero.mpr hsum
  calc
    coordinateMultiPartial alpha R q = R q * (M q * coordinateMultiPartial alpha R q) := by
      rw [← mul_assoc,(hinv q hq).2,one_mul]
    _ = R q * -(∑ beta ∈ (multiIndexBox alpha).erase 0, multiIndexBinomial alpha beta •
        (coordinateMultiPartial beta M q * coordinateMultiPartial (fun k => alpha k-beta k) R q)) :=
      congrArg (fun z => R q * z) hterm
    _ = _ := by rw [mul_neg,neg_mul]

end Froehlich
