import Froehlich.Nodes.KE01ReciprocalUniform
import Froehlich.Nodes.KE01AffineCoordinates
import Froehlich.Nodes.KE01CanonicalNormLocalChain

set_option autoImplicit false
noncomputable section
namespace Froehlich

theorem kernelDenominatorNine_iterated_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (k : ℕ) (hk : k ≤ 3)
      (x : Fin 9 → ℝ), ‖kernelCoordinateBlock 0 x‖ ≤ 1/4 →
      ‖iteratedFDeriv ℝ k (fun y : Fin 9 → ℝ =>
        (((1+e-‖kernelCoordinateBlock 0 y‖^2)⁻¹ : ℝ) : ℂ)) x‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := kernelInverseDenominator_iterated_common
  let L := kernelInputCoordinates 0
  let A := (1+‖L‖)^3
  let M := 1+‖Complex.ofRealCLM‖
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨C*A*M,by positivity,?_⟩
  intro e he k hk x hx
  let F := fun y : Fin 3 → ℝ => (kernelDenominatorCoordinates e y)⁻¹
  have hq : ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (L x)‖ ≤ 1/4 := by
    simpa only [kernelCoordinateBlock_eq,L] using hx
  have hD : ContDiff ℝ 3 (kernelDenominatorCoordinates e) :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff)
  have hn : kernelDenominatorCoordinates e (L x) ≠ 0 :=
    ne_of_gt (ke01_denominator_pos e he _ (by linarith))
  have hF : ContDiffAt ℝ k F (L x) := (hD.contDiffAt.inv hn).of_le (by exact_mod_cast hk)
  have hpre := iteratedFDeriv_comp_linear_norm_le_at L F k x hF
  have hp : ‖L‖^k ≤ A := by
    dsimp [A]
    interval_cases k <;> norm_num <;>
      nlinarith [norm_nonneg L,sq_nonneg ‖L‖,pow_nonneg (norm_nonneg L) 3]
  have hFN : ‖iteratedFDeriv ℝ k F (L x)‖ ≤ C := hB e he k hk (L x) hq
  have hpreN : ‖iteratedFDeriv ℝ k (F ∘ L) x‖ ≤ C*A :=
    hpre.trans (mul_le_mul hFN hp (pow_nonneg (norm_nonneg L) k) hC.le)
  have hpost := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
    (x := x) (hF.comp x L.contDiff.contDiffAt) (n := k) le_rfl
  have hf : (fun y => ((F (L y)) : ℂ)) = (fun y : Fin 9 → ℝ =>
      (((1+e-‖kernelCoordinateBlock 0 y‖^2)⁻¹ : ℝ) : ℂ)) := by
    funext y
    dsimp [F,kernelDenominatorCoordinates]
    rw [kernelCoordinateBlock_eq]
  have hpost' : ‖iteratedFDeriv ℝ k (fun y : Fin 9 → ℝ =>
      (((1+e-‖kernelCoordinateBlock 0 y‖^2)⁻¹ : ℝ) : ℂ)) x‖ ≤
      ‖Complex.ofRealCLM‖*‖iteratedFDeriv ℝ k (F ∘ L) x‖ := by
    simpa only [Function.comp_def,hf] using! hpost
  refine hpost'.trans ((mul_le_mul_of_nonneg_left hpreN (norm_nonneg Complex.ofRealCLM)).trans ?_)
  have hNM : ‖Complex.ofRealCLM‖ ≤ M := by dsimp [M]; linarith
  simpa only [mul_comm,mul_left_comm,mul_assoc] using
    mul_le_mul_of_nonneg_right hNM (mul_nonneg hC.le hA.le)

end Froehlich
