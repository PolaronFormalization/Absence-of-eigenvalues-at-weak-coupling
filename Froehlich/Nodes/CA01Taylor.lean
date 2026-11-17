import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The source's exact one-half Banach-valued quadratic remainder, with
smoothness required only locally along the indicated segment. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Interval
namespace Froehlich
variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def secondTaylorIntegrand (f : D → F) (p h : D) (t : ℝ) : F :=
  (1-t) • iteratedFDeriv ℝ 2 f (p+t • h) (fun _ : Fin 2 => h)

theorem secondTaylorIntegrand_intervalIntegrable (f : D → F) (p h : D)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (p+t • h)) :
    IntervalIntegrable (secondTaylorIntegrand f p h) volume 0 1 := by
  have hline : Continuous (fun t : ℝ => p+t • h) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hsecond : ContinuousOn
      (fun t : ℝ => iteratedFDeriv ℝ 2 f (p+t • h) (fun _ : Fin 2 => h)) (Set.Icc 0 1) := by
    intro t ht
    have hc : ContinuousAt (iteratedFDeriv ℝ 2 f) (p+t • h) :=
      ((hf t ht).iteratedFDeriv_right (i := 2) (m := 0) (by norm_num)).continuousAt
    have hcomp : ContinuousAt (fun s : ℝ => iteratedFDeriv ℝ 2 f (p+s • h)) t :=
      ContinuousAt.comp' (f := fun s : ℝ => p+s • h) (x := t) hc hline.continuousAt
    exact hcomp.continuousWithinAt.eval_const (fun _ : Fin 2 => h)
  have hg : ContinuousOn (secondTaylorIntegrand f p h) (Set.Icc 0 1) :=
    (continuous_const.sub continuous_id).continuousOn.smul hsecond
  exact (show ContinuousOn (secondTaylorIntegrand f p h) (Set.uIcc (0 : ℝ) 1) by
    simpa only [Set.uIcc_of_le zero_le_one] using hg).intervalIntegrable

theorem secondTaylor_remainder_eq_integral (f : D → F) (p h : D)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (p+t • h)) :
    f (p+h) - f p - fderiv ℝ f p h = ∫ t in (0 : ℝ)..1, secondTaylorIntegrand f p h t := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (x := p) (y := h) hf
  have he : f (p+h) = f p + fderiv ℝ f p h + ∫ t in (0 : ℝ)..1, secondTaylorIntegrand f p h t := by
    simpa only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.factorial_zero,Nat.factorial_one,
      Nat.cast_one,inv_one,one_smul,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,
      pow_one,zero_add,secondTaylorIntegrand] using ht
  rw [he]
  abel

theorem norm_secondTaylor_remainder (f : D → F) (p h : D) (L : ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (p+t • h))
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ 2 f (p+t • h)‖ ≤ L) :
    ‖f (p+h) - f p - fderiv ℝ f p h‖ ≤ L * ‖h‖^2 / 2 := by
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖secondTaylorIntegrand f p h t‖ ≤ (1-t) * (L * ‖h‖^2) := by
    have hmult : ‖iteratedFDeriv ℝ 2 f (p+t • h) (fun _ : Fin 2 => h)‖ ≤
        ‖iteratedFDeriv ℝ 2 f (p+t • h)‖ * ‖h‖^2 := by
      simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
        (iteratedFDeriv ℝ 2 f (p+t • h)).le_opNorm (fun _ : Fin 2 => h)
    have hmult' := hmult.trans (mul_le_mul_of_nonneg_right (hL t ht) (sq_nonneg ‖h‖))
    change ‖(1-t) • iteratedFDeriv ℝ 2 f (p+t • h) (fun _ : Fin 2 => h)‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact mul_le_mul_of_nonneg_left hmult' (sub_nonneg.mpr ht.2)
  have hg : Continuous (fun t : ℝ => (1-t) * (L * ‖h‖^2)) :=
    (continuous_const.sub continuous_id).mul continuous_const
  have hi : ‖∫ t in (0 : ℝ)..1, secondTaylorIntegrand f p h t‖ ≤
      ∫ t in (0 : ℝ)..1, (1-t) * (L * ‖h‖^2) :=
    intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall (fun t ht => hbound t ⟨ht.1.le,ht.2⟩)) (hg.intervalIntegrable 0 1)
  have hweight : (∫ t in (0 : ℝ)..1, (1-t) * (L * ‖h‖^2)) = L * ‖h‖^2 / 2 := by
    rw [intervalIntegral.integral_mul_const]
    have hlin : (∫ t in (0 : ℝ)..1, (1-t : ℝ)) = (1/2 : ℝ) := by
      have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
      have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 1 := continuous_id.intervalIntegrable 0 1
      have he : (∫ t in (0 : ℝ)..1, (1-t : ℝ)) =
          (∫ _t in (0 : ℝ)..1, (1 : ℝ)) - ∫ t in (0 : ℝ)..1, t :=
        intervalIntegral.integral_sub hc hid
      exact he.trans (by norm_num)
    rw [hlin]
    ring
  rw [secondTaylor_remainder_eq_integral f p h hf]
  exact hi.trans_eq hweight

end Froehlich
