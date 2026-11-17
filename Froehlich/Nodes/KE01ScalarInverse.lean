import Froehlich.Nodes.CA01MultiIndexConstants

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace Froehlich

/-- The exact source inverse recurrence specialized to a nonvanishing real
scalar, proved from the accepted binomial product rule on its open domain. -/
theorem ke01_scalarInverse_multiPartial {d : ℕ} (D : (Fin d → ℝ) → ℝ)
    (alpha : Fin d → ℕ) (ha : alpha ≠ 0)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hD : ContDiffOn ℝ (∑ i,alpha i : ℕ) D S)
    (hn : ∀ x ∈ S,D x ≠ 0) (x : Fin d → ℝ) (hx : x ∈ S) :
    coordinateMultiPartial alpha (fun y => (D y)⁻¹) x = -(D x)⁻¹ *
      ∑ beta ∈ (multiIndexBox alpha).erase 0, multiIndexBinomial alpha beta •
        (coordinateMultiPartial beta D x *
          coordinateMultiPartial (fun i => alpha i-beta i) (fun y => (D y)⁻¹) x) := by
  have hI : ContDiffOn ℝ (∑ i,alpha i : ℕ) (fun y => (D y)⁻¹) S := hD.inv hn
  have hz : coordinateMultiPartial alpha (fun y => D y*(D y)⁻¹) x = 0 := by
    calc
      _ = coordinateMultiPartial alpha (fun _ => (1 : ℝ)) x :=
        coordinateBlocksPartial_congr_of_isOpen _ _ _ S hS
          (fun y hy => mul_inv_cancel₀ (hn y hy)) hx
      _ = 0 := coordinateMultiPartial_const alpha ha 1 x
  have hp := coordinateMultiPartial_realBilinear alpha (ContinuousLinearMap.mul ℝ ℝ)
    D (fun y => (D y)⁻¹) S hS hD hI x hx
  change coordinateMultiPartial alpha (fun y => D y*(D y)⁻¹) x =
    ∑ beta ∈ multiIndexBox alpha, multiIndexBinomial alpha beta •
      (coordinateMultiPartial beta D x *
        coordinateMultiPartial (fun i => alpha i-beta i) (fun y => (D y)⁻¹) x) at hp
  have hs := hp.symm.trans hz
  rw [multiIndexBox_sum_split_zero] at hs
  simp only [multiIndexBinomial_zero,coordinateMultiPartial_zero,one_smul,Pi.zero_apply,Nat.sub_zero] at hs
  have he := congrArg (fun z : ℝ => (D x)⁻¹*z) hs
  rw [mul_add,←mul_assoc,inv_mul_cancel₀ (hn x hx),one_mul,mul_zero] at he
  rw [neg_mul]
  exact eq_neg_iff_add_eq_zero.mpr he

end Froehlich
