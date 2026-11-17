import Froehlich.Nodes.FA02
import Mathlib.Analysis.Normed.Ring.Units

/-! SP00: the actual coercive source resolvent, on its parameter set. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def sourceOperator (T₀ : V →L[ℂ] V) (j : V →L[ℂ] H) (lam : ℝ) : V →L[ℂ] V :=
  T₀ - (lam : ℂ) • (j.adjoint.comp j)

theorem sourceOperator_selfadjoint (T₀ : V →L[ℂ] V) (j : V →L[ℂ] H)
    (hT₀ : T₀.adjoint = T₀) (lam : ℝ) :
    (sourceOperator T₀ j lam).adjoint = sourceOperator T₀ j lam := by
  simp only [sourceOperator, map_sub, map_smulₛₗ,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    Complex.conj_ofReal, hT₀]

/-- This is precisely pointwise coercivity; no inverse is postulated. -/
structure SourceCoercivity (T₀ : V →L[ℂ] V) (j : V →L[ℂ] H) (I : Set ℝ) where
  lower : I → ℝ
  positive : ∀ lam, 0 < lower lam
  bound : ∀ lam u, lower lam * ‖u‖ ^ 2 ≤ (⟪u,sourceOperator T₀ j lam u⟫_ℂ).re

variable (T₀ : V →L[ℂ] V) (j : V →L[ℂ] H) (I : Set ℝ)
  (hT₀ : T₀.adjoint = T₀) (h : SourceCoercivity T₀ j I)

def sourceInverse (lam : I) : V →L[ℂ] V :=
  coerciveEnergyInverse (sourceOperator T₀ j lam)
    (sourceOperator_selfadjoint T₀ j hT₀ lam) (h.positive lam) (h.bound lam)

theorem sourceInverse_left (lam : I) :
    sourceInverse T₀ j I hT₀ h lam * sourceOperator T₀ j lam = 1 :=
  coerciveEnergyInverse_left _ _ _ _

theorem sourceInverse_right (lam : I) :
    sourceOperator T₀ j lam * sourceInverse T₀ j I hT₀ h lam = 1 :=
  coerciveEnergyInverse_right _ _ _ _

theorem sourceInverse_selfadjoint (lam : I) :
    (sourceInverse T₀ j I hT₀ h lam).adjoint = sourceInverse T₀ j I hT₀ h lam :=
  inverse_selfadjoint _ _ (sourceOperator_selfadjoint T₀ j hT₀ lam)
    (sourceInverse_left T₀ j I hT₀ h lam) (sourceInverse_right T₀ j I hT₀ h lam)

theorem sourceInverse_nonnegative (lam : I) (z : V) :
    0 ≤ (⟪z,sourceInverse T₀ j I hT₀ h lam z⟫_ℂ).re := by
  apply inverse_nonnegative _ _ (sourceOperator_selfadjoint T₀ j hT₀ lam)
  · intro z
    exact congrArg (fun A : V →L[ℂ] V => A z) (sourceInverse_right T₀ j I hT₀ h lam)
  · intro u
    exact le_trans (mul_nonneg (h.positive lam).le (sq_nonneg _)) (h.bound lam u)

theorem sourceInverse_real (lam : I) (z : V) :
    (⟪z,sourceInverse T₀ j I hT₀ h lam z⟫_ℂ).im = 0 := by
  have he : ⟪sourceInverse T₀ j I hT₀ h lam z,z⟫_ℂ =
      ⟪z,sourceInverse T₀ j I hT₀ h lam z⟫_ℂ := by
    simpa only [sourceInverse_selfadjoint] using
      (sourceInverse T₀ j I hT₀ h lam).adjoint_inner_left z z
  have hc := congrArg Complex.im he
  rw [← inner_conj_symm (sourceInverse T₀ j I hT₀ h lam z) z] at hc
  simp only [Complex.conj_im] at hc
  linarith

theorem sourceOperator_quadratic (lam : ℝ) (u : V) :
    (⟪u,sourceOperator T₀ j lam u⟫_ℂ).re =
      (⟪u,T₀ u⟫_ℂ).re - lam * ‖j u‖ ^ 2 := by
  simp only [sourceOperator, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_sub_right, inner_smul_right, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hJJ : (⟪u,(j.adjoint.comp j) u⟫_ℂ).re = ‖j u‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (j.apply_norm_sq_eq_inner_adjoint_right u).symm
  rw [hJJ]

theorem sourceInverse_monotone (z : V) :
    Monotone (fun lam : I => (⟪z,sourceInverse T₀ j I hT₀ h lam z⟫_ℂ).re) := by
  intro a b hab
  apply inverse_order (sourceOperator T₀ j b) (sourceOperator T₀ j a)
    (sourceInverse T₀ j I hT₀ h b) (sourceInverse T₀ j I hT₀ h a)
    (sourceOperator_selfadjoint T₀ j hT₀ b) (sourceOperator_selfadjoint T₀ j hT₀ a)
  · intro u
    exact congrArg (fun A : V →L[ℂ] V => A u) (sourceInverse_right T₀ j I hT₀ h b)
  · intro u
    exact congrArg (fun A : V →L[ℂ] V => A u) (sourceInverse_right T₀ j I hT₀ h a)
  · intro u
    exact (mul_nonneg (h.positive b).le (sq_nonneg _)).trans (h.bound b u)
  · intro u
    exact (mul_nonneg (h.positive a).le (sq_nonneg _)).trans (h.bound a u)
  · intro u
    rw [sourceOperator_quadratic, sourceOperator_quadratic]
    have hab' : (a : ℝ) ≤ (b : ℝ) := hab
    exact sub_le_sub_left (mul_le_mul_of_nonneg_right hab' (sq_nonneg ‖j u‖)) _

/-- A unit records the two already-proved inverse equations; it adds no
invertibility premise and defines nothing outside I. -/
def sourceUnit (lam : I) : (V →L[ℂ] V)ˣ where
  val := sourceOperator T₀ j lam
  inv := sourceInverse T₀ j I hT₀ h lam
  val_inv := sourceInverse_right T₀ j I hT₀ h lam
  inv_val := sourceInverse_left T₀ j I hT₀ h lam

theorem sourceInverse_eq_ringInverse (lam : I) :
    sourceInverse T₀ j I hT₀ h lam = Ring.inverse (sourceOperator T₀ j lam) :=
  (Ring.inverse_unit (sourceUnit T₀ j I hT₀ h lam)).symm

theorem sourceInverse_continuous : Continuous (sourceInverse T₀ j I hT₀ h) := by
  have hf : Continuous (fun lam : I => sourceOperator T₀ j (lam : ℝ)) :=
    continuous_const.sub ((Complex.continuous_ofReal.comp continuous_subtype_val).smul continuous_const)
  apply continuous_iff_continuousAt.mpr
  intro lam
  have hci : ContinuousAt Ring.inverse (sourceOperator T₀ j (lam : ℝ)) :=
    NormedRing.inverse_continuousAt (sourceUnit T₀ j I hT₀ h lam)
  have hc : ContinuousAt (fun x : I => Ring.inverse (sourceOperator T₀ j (x : ℝ))) lam :=
    ContinuousAt.comp' (f := fun x : I => sourceOperator T₀ j (x : ℝ))
      (x := lam) hci (hf.continuousAt (x := lam))
  have he : sourceInverse T₀ j I hT₀ h =
      (fun x : I => Ring.inverse (sourceOperator T₀ j (x : ℝ))) :=
    funext (sourceInverse_eq_ringInverse T₀ j I hT₀ h)
  rw [he]
  exact hc

def sourceScalar (z : V) (lam : I) : ℝ :=
  (⟪z,sourceInverse T₀ j I hT₀ h lam z⟫_ℂ).re

theorem sourceScalar_continuous (z : V) : Continuous (sourceScalar T₀ j I hT₀ h z) := by
  exact Complex.continuous_re.comp
    (continuous_const.inner ((sourceInverse_continuous T₀ j I hT₀ h).clm_apply continuous_const))

def sourceFunction (c : ℝ) (z : V) (lam : I) : ℝ :=
  c - (lam : ℝ) - sourceScalar T₀ j I hT₀ h z lam

theorem sourceFunction_continuous (c : ℝ) (z : V) :
    Continuous (sourceFunction T₀ j I hT₀ h c z) :=
  (continuous_const.sub continuous_subtype_val).sub (sourceScalar_continuous T₀ j I hT₀ h z)

theorem sourceFunction_decrease (c : ℝ) (z : V) (a b : I) (hab : a < b) :
    sourceFunction T₀ j I hT₀ h c z b ≤
      sourceFunction T₀ j I hT₀ h c z a - ((b : ℝ) - (a : ℝ)) := by
  have hm := sourceInverse_monotone T₀ j I hT₀ h z hab.le
  change (⟪z,sourceInverse T₀ j I hT₀ h a z⟫_ℂ).re ≤
    (⟪z,sourceInverse T₀ j I hT₀ h b z⟫_ℂ).re at hm
  dsimp [sourceFunction, sourceScalar]
  linarith

end Froehlich
