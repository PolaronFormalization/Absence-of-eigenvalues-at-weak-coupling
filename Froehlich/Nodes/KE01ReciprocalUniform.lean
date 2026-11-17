import Froehlich.Nodes.KE01ReciprocalBounds
import Froehlich.Nodes.KE01CanonicalNormLocalUpper

set_option autoImplicit false
noncomputable section
namespace Froehlich

theorem kernelInverseDenominator_derivatives_common : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (alpha : Fin 3 → ℕ)
      (ha : (∑ i,alpha i) ≤ 3) (q : Fin 3 → ℝ),
      ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm q‖ ≤ 1/4 →
      ‖coordinateMultiPartial alpha (fun y => (kernelDenominatorCoordinates e y)⁻¹) q‖ ≤ C := by
  classical
  have heach (a : Fin 3 → ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (q : Fin 3 → ℝ),
        (∑ i,a i) ≤ 3 → ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm q‖ ≤ 1/4 →
        ‖coordinateMultiPartial a (fun y => (kernelDenominatorCoordinates e y)⁻¹) q‖ ≤ C := by
    by_cases ha : (∑ i,a i) ≤ 3
    · obtain ⟨C,hC,hB⟩ := kernelInverseDenominator_derivatives_uniform a ha
      exact ⟨C,hC,fun e he q _ hq => hB e he q hq⟩
    · exact ⟨1,one_pos,fun _ _ _ h => False.elim (ha h)⟩
  choose K hK hB using heach
  let S := multiIndexBox (fun _ : Fin 3 => 3)
  have hsum : 0 ≤ ∑ a ∈ S,K a := Finset.sum_nonneg (fun a _ => (hK a).le)
  refine ⟨(∑ a ∈ S,K a)+1,by linarith,?_⟩
  intro e he a ha q hq
  have ham : a ∈ S := (mem_multiIndexBox _ a).mpr (fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans ha)
  exact (hB a e he q ha hq).trans ((Finset.single_le_sum (fun b _ => (hK b).le) ham).trans
    (le_add_of_nonneg_right zero_le_one))

theorem kernelInverseDenominator_iterated_common : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (k : ℕ) (hk : k ≤ 3) (q : Fin 3 → ℝ),
      ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm q‖ ≤ 1/4 →
      ‖iteratedFDeriv ℝ k (fun y => (kernelDenominatorCoordinates e y)⁻¹) q‖ ≤ C := by
  obtain ⟨C,hC,hBound⟩ := kernelInverseDenominator_derivatives_common
  refine ⟨27*C,by positivity,?_⟩
  intro e he k hk q hq
  have hD : ContDiff ℝ 3 (kernelDenominatorCoordinates e) :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff)
  have hn : kernelDenominatorCoordinates e q ≠ 0 :=
    ne_of_gt (ke01_denominator_pos e he _ (by linarith))
  have hI : ContDiffAt ℝ k (fun y => (kernelDenominatorCoordinates e y)⁻¹) q :=
    (hD.contDiffAt.inv hn).of_le (by exact_mod_cast hk)
  have hN := iteratedFDeriv_norm_le_canonical_at k (fun y => (kernelDenominatorCoordinates e y)⁻¹)
    q hI C hC.le (fun a ha => hBound e he a (by omega) q hq)
  refine hN.trans ?_
  have hp : (3 : ℝ)^k ≤ 27 := by interval_cases k <;> norm_num
  exact mul_le_mul_of_nonneg_right hp hC.le

end Froehlich
