import Froehlich.Nodes.CA01GeneralRemainder

/-! Exact second-order remainder using actual derivatives on the segment only. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology Interval
namespace Froehlich
variable {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_remainder_of_actual_secondDerivative
    (f : D → F) (DF : D → D →L[ℝ] F)
    (D2 : D → D →L[ℝ] D →L[ℝ] F) (p h : D) (L : ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt f (DF (p+t • h)) (p+t • h))
    (hDF : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasFDerivAt DF (D2 (p+t • h)) (p+t • h))
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D2 (p+t • h)‖ ≤ L) :
    ‖f (p+h) - f p - DF p h‖ ≤ L * ‖h‖^2 / 2 := by
  let G : ℝ → F := fun t => DF (p+t • h) h - DF p h
  have hc : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((normDerivative_alongLine_apply DF (D2 (p+t • h)) p h t
      (hDF t ht)).continuousAt.sub continuousAt_const).continuousWithinAt
  have hint : IntervalIntegrable G volume 0 1 :=
    hc.intervalIntegrable_of_Icc zero_le_one
  have he : (∫ t in (0 : ℝ)..1, G t) = f (p+h) - f p - DF p h := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => f (p+s • h) - f p - s • DF p h) (G t) t := by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using ht
      have hder := ((normDerivative_alongLine f (DF (p+t • h)) p h t
        (hf t ht')).sub_const (f p)).sub ((hasDerivAt_id t).smul_const (DF p h))
      convert hder using 1 <;>
        first | (funext s; rfl) | (simp only [G,one_smul,id_eq])
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
    simpa only [one_smul,zero_smul,add_zero,sub_self,sub_zero] using hFTC
  have hg : Continuous (fun t : ℝ => t * (L * ‖h‖^2)) := continuous_id.mul continuous_const
  have hb : ‖∫ t in (0 : ℝ)..1, G t‖ ≤ ∫ t in (0 : ℝ)..1, t * (L * ‖h‖^2) :=
    intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall (fun t ht => by
        have hinc := norm_firstDerivative_segment_increment DF D2 p h L hDF hL t ⟨ht.1.le,ht.2⟩
        change ‖DF (p+t • h) h - DF p h‖ ≤ _
        convert hinc using 1 <;> ring)) (hg.intervalIntegrable 0 1)
  have hw : (∫ t in (0 : ℝ)..1, t * (L * ‖h‖^2)) = L * ‖h‖^2 / 2 := by
    rw [intervalIntegral.integral_mul_const]
    norm_num
    <;> ring
  rw [he] at hb
  exact hb.trans_eq hw

theorem norm_remainder_of_second_fderiv
    (f : D → F) (p h : D) (L : ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f (p+t • h))
    (hdf : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ (fderiv ℝ f) (p+t • h))
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖fderiv ℝ (fderiv ℝ f) (p+t • h)‖ ≤ L) :
    ‖f (p+h) - f p - fderiv ℝ f p h‖ ≤ L * ‖h‖^2 / 2 :=
  norm_remainder_of_actual_secondDerivative f (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f)) p h L
    (fun t ht => (hf t ht).hasFDerivAt) (fun t ht => (hdf t ht).hasFDerivAt) hL

end Froehlich
