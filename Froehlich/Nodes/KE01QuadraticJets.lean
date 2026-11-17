import Froehlich.Nodes.KE01Denominator
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
namespace Froehlich

private theorem ke01_linearJets_bound {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : D →L[ℝ] V) (x : D)
    (hx : ‖L x‖ ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => L y) x‖ ≤ 1+‖L‖ := by
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hx.trans (le_add_of_nonneg_right (norm_nonneg L))
  | succ k =>
    have hd : fderiv ℝ (fun y => L y) = fun _ => L := funext (fun y => L.fderiv)
    rw [←norm_iteratedFDeriv_fderiv,hd]
    cases k with
    | zero => simp only [norm_iteratedFDeriv_zero]; linarith
    | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; positivity

def kernelDenominatorCoordinates (e : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  1+e-‖(EuclideanSpace.equiv (Fin 3) ℝ).symm x‖^2

def kernelQuadraticJetBound (k : ℕ) : ℝ :=
  1+‖innerSL ℝ (E := GW.Space)‖ * ∑ i ∈ Finset.range (k+1),
    (k.choose i : ℝ)*(1+‖(EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap‖)^2

theorem kernelQuadraticJetBound_nonnegative (k : ℕ) : 0 ≤ kernelQuadraticJetBound k := by
  unfold kernelQuadraticJetBound
  positivity

/-- Native bilinear Leibniz bounds for the actual quadratic denominator.
The chart is linear, so its higher jets vanish identically. -/
theorem kernelDenominatorCoordinates_iterated_bound (k : ℕ) (e : ℝ)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (x : Fin 3 → ℝ)
    (hx : ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm x‖ ≤ 1/4) :
    ‖iteratedFDeriv ℝ k (kernelDenominatorCoordinates e) x‖ ≤ kernelQuadraticJetBound k := by
  let L := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap
  let B := innerSL ℝ (E := GW.Space)
  let A := 1+‖L‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL (i : ℕ) : ‖iteratedFDeriv ℝ i (fun y => L y) x‖ ≤ A :=
    ke01_linearJets_bound L x (hx.trans (by norm_num)) i
  have hb := B.norm_iteratedFDeriv_le_of_bilinear
    (L.contDiff : ContDiff ℝ k (fun y => L y)) L.contDiff x le_rfl
  have hprod : ‖iteratedFDeriv ℝ k (fun y => B (L y) (L y)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*A^2 := by
    refine hb.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_)) (norm_nonneg B))
    have hmul := mul_le_mul (hL i) (hL (k-i))
      (norm_nonneg (iteratedFDeriv ℝ (k-i) (fun y => L y) x)) hA
    nlinarith [(Nat.cast_nonneg (k.choose i) : (0 : ℝ) ≤ (k.choose i : ℝ))]
  have hc : ‖iteratedFDeriv ℝ k (fun _ : Fin 3 → ℝ => 1+e) x‖ ≤ 1 := by
    cases k with
    | zero => simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs]; rw [abs_of_nonneg (by linarith [he.1])]; linarith [he.2]
    | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; norm_num
  have hfun : kernelDenominatorCoordinates e = (fun y => (1+e)-B (L y) (L y)) := by
    funext y
    change (1+e)-‖(EuclideanSpace.equiv (Fin 3) ℝ).symm y‖^2 = (1+e)-inner ℝ (L y) (L y)
    rw [real_inner_self_eq_norm_sq]
    exact congrArg (fun z : GW.Space => 1+e-‖z‖^2)
      (rfl : (EuclideanSpace.equiv (Fin 3) ℝ).symm y = L y)
  have hbreg : ContDiff ℝ k (fun y => B (L y) (L y)) := by
    simpa only [B,innerSL_apply_apply] using L.contDiff.inner (𝕜 := ℝ) L.contDiff
  have hsub : iteratedFDeriv ℝ k (kernelDenominatorCoordinates e) x =
      iteratedFDeriv ℝ k (fun _ : Fin 3 → ℝ => 1+e) x-
        iteratedFDeriv ℝ k (fun y => B (L y) (L y)) x := by
    rw [hfun]
    simpa only [Pi.sub_apply] using!
      (iteratedFDeriv_sub_apply (contDiffAt_const : ContDiffAt ℝ k (fun _ : Fin 3 → ℝ => 1+e) x) hbreg.contDiffAt)
  rw [hsub]
  exact (norm_sub_le _ _).trans (by simpa only [kernelQuadraticJetBound,A,B,L] using add_le_add hc hprod)

end Froehlich
