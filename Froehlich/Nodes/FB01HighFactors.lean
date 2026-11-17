import Froehlich.Nodes.FB01Vectors
import Froehlich.Nodes.FC07Commutators

/-! The exact high-cutoff form factor is the sum of its three momentum
components. The real coupling keeps its sign throughout. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Froehlich

theorem lyVectorL2_support_nat (g L Λ : ℝ) (hL : 0 < L) (S : ℕ)
    (hS : max 1 Λ ≤ (S : ℝ)) (j : Fin 3) :
    ∀ᵐ k ∂(volume : Measure GW.Space), (S : ℝ) < ‖k‖ → lyVectorL2 g L Λ hL j k = 0 := by
  filter_upwards [lyVectorL2_bounded_support g L Λ hL j] with k hk
  intro hout
  have hΛS : Λ ≤ (S : ℝ) := (le_max_right 1 Λ).trans hS
  exact hk (hΛS.trans_lt hout)

theorem lyVector_momentum_sum (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ) (k : GW.Space) :
    (∑ j : Fin 3, (k j : ℂ) * lyVectorFunction g L Λ j k) =
      (cutoffFormFactor g Λ k : ℂ) - (cutoffFormFactor g L k : ℂ) := by
  by_cases hlo : ‖k‖ ≤ L
  · have hhi : ‖k‖ ≤ Λ := hlo.trans hLΛ
    simp only [lyVectorFunction, show ¬(L < ‖k‖ ∧ ‖k‖ ≤ Λ) from fun h => (not_lt.mpr hlo) h.1,
      if_false,mul_zero,Finset.sum_const_zero,cutoffFormFactor,if_pos hlo,if_pos hhi,sub_self]
  · by_cases hhi : ‖k‖ ≤ Λ
    · have hin : L < ‖k‖ ∧ ‖k‖ ≤ Λ := ⟨lt_of_not_ge hlo,hhi⟩
      have hnorm : ‖k‖ ≠ 0 := ne_of_gt (hL.trans hin.1)
      have halgebra : (∑ j : Fin 3, k j * (g * k j / ‖k‖^3)) = g / ‖k‖ := by
        calc
          _ = (g / ‖k‖^3) * ∑ j : Fin 3, (k j)^2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = (g / ‖k‖^3) * ‖k‖^2 := by rw [← EuclideanSpace.real_norm_sq_eq]
          _ = _ := by field_simp [hnorm] <;> ring
      simp only [lyVectorFunction,if_pos hin,cutoffFormFactor,if_pos hhi,if_neg hlo,
        Complex.ofReal_zero,sub_zero,fiberFormFactor,← Complex.ofReal_mul,← Complex.ofReal_sum]
      exact congrArg (fun x : ℝ => (x : ℂ)) halgebra
    · have hin : ¬(L < ‖k‖ ∧ ‖k‖ ≤ Λ) := fun h => hhi h.2
      simp only [lyVectorFunction,if_neg hin,mul_zero,Finset.sum_const_zero,
        cutoffFormFactor,if_neg hhi,if_neg hlo,Complex.ofReal_zero,sub_self]

theorem lyVector_momentumSmearing_sum (g L Λ : ℝ) (hL : 0 < L) (hLΛ : L ≤ Λ)
    (S : ℕ) (hS : max 1 Λ ≤ (S : ℝ)) :
    (∑ j : Fin 3, momentumSmearing j S (lyVectorL2 g L Λ hL j)) =
      cutoffFormFactorL2 g Λ (hL.trans_le hLΛ) - cutoffFormFactorL2 g L hL := by
  apply Lp.ext
  have hsum := GW.Fock.finite_lp_sum_ae (volume : Measure GW.Space) Finset.univ
    (fun j : Fin 3 => momentumSmearing j S (lyVectorL2 g L Λ hL j))
  have hsmear (j : Fin 3) := momentumSmearing_ae j S (lyVectorL2 g L Λ hL j)
    (lyVectorL2_support_nat g L Λ hL S hS j)
  filter_upwards [hsum,ae_all_iff.mpr hsmear,ae_all_iff.mpr (lyVectorL2_ae g L Λ hL),
    Lp.coeFn_sub (cutoffFormFactorL2 g Λ (hL.trans_le hLΛ)) (cutoffFormFactorL2 g L hL),
    cutoffFormFactorL2_ae g Λ (hL.trans_le hLΛ),cutoffFormFactorL2_ae g L hL]
    with k hsum hsmear hvec hsub hΛ hLo
  simp only [Pi.sub_apply] at hsub
  rw [hsum,hsub,hΛ,hLo]
  calc
    _ = ∑ j : Fin 3, (k j : ℂ) * lyVectorFunction g L Λ j k := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hsmear j,hvec j]
    _ = _ := lyVector_momentum_sum g L Λ hL hLΛ k

end Froehlich
