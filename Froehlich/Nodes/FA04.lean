import Froehlich.Nodes.FA01
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! FA04: bounded Schur elimination. The product norm here is used only
for bounded maps; the component Hilbert form is treated separately. -/
noncomputable section
namespace Froehlich
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def blockOperator (A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (B : E →L[ℂ] F) (D : F →L[ℂ] F) : (E × F) →L[ℂ] (E × F) :=
  ((A.comp (.fst ℂ E F)) + C.comp (.snd ℂ E F)).prod
    ((B.comp (.fst ℂ E F)) + D.comp (.snd ℂ E F))

def schurComplement (A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (B : E →L[ℂ] F) (Di : F →L[ℂ] F) : E →L[ℂ] E :=
  A - C.comp (Di.comp B)

def schurSolveX (C : F →L[ℂ] E) (Di : F →L[ℂ] F) (Si : E →L[ℂ] E) :
    (E × F) →L[ℂ] E :=
  Si.comp ((.fst ℂ E F) - C.comp (Di.comp (.snd ℂ E F)))

def schurInverse (C : F →L[ℂ] E) (B : E →L[ℂ] F)
    (Di : F →L[ℂ] F) (Si : E →L[ℂ] E) : (E × F) →L[ℂ] (E × F) :=
  (schurSolveX C Di Si).prod
    (Di.comp ((.snd ℂ E F) - B.comp (schurSolveX C Di Si)))

@[simp] theorem blockOperator_apply (A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (B : E →L[ℂ] F) (D : F →L[ℂ] F) (u : E × F) :
    blockOperator A C B D u = (A u.1 + C u.2, B u.1 + D u.2) := rfl

@[simp] theorem schurComplement_apply (A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (B : E →L[ℂ] F) (Di : F →L[ℂ] F) (u : E) :
    schurComplement A C B Di u = A u - C (Di (B u)) := rfl

theorem blockOperator_schurInverse (A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (B : E →L[ℂ] F) (D Di : F →L[ℂ] F) (Si : E →L[ℂ] E)
    (hD : ∀ y, D (Di y) = y)
    (hS : ∀ x, schurComplement A C B Di (Si x) = x) :
    (blockOperator A C B D).comp (schurInverse C B Di Si) = .id ℂ (E × F) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Prod.ext
  · let x := Si (f.1 - C (Di f.2))
    have hx := hS (f.1 - C (Di f.2))
    change A x - C (Di (B x)) = f.1 - C (Di f.2) at hx
    change A x + C (Di (f.2 - B x)) = f.1
    rw [map_sub, map_sub]
    calc
      A x + (C (Di f.2) - C (Di (B x))) =
          (A x - C (Di (B x))) + C (Di f.2) := by module
      _ = f.1 := by rw [hx]; module
  · change B (Si (f.1 - C (Di f.2))) +
      D (Di (f.2 - B (Si (f.1 - C (Di f.2))))) = f.2
    rw [hD]
    module

theorem schurInverse_blockOperator (A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (B : E →L[ℂ] F) (D Di : F →L[ℂ] F) (Si : E →L[ℂ] E)
    (hD : ∀ y, Di (D y) = y)
    (hS : ∀ x, Si (schurComplement A C B Di x) = x) :
    (schurInverse C B Di Si).comp (blockOperator A C B D) = .id ℂ (E × F) := by
  apply ContinuousLinearMap.ext
  intro f
  have he : A f.1 + C f.2 - C (Di (B f.1 + D f.2)) =
      schurComplement A C B Di f.1 := by
    rw [map_add, hD, map_add, schurComplement_apply]
    module
  have hx : Si (A f.1 + C f.2 - C (Di (B f.1 + D f.2))) = f.1 := by
    rw [he, hS]
  apply Prod.ext
  · exact hx
  · change Di (B f.1 + D f.2 - B (Si (A f.1 + C f.2 - C (Di (B f.1 + D f.2))))) = f.2
    rw [hx]
    have hy : B f.1 + D f.2 - B f.1 = D f.2 := by module
    rw [hy, hD]

theorem blockOperator_schurFactorization (A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (B : E →L[ℂ] F) (D Di : F →L[ℂ] F)
    (hD : ∀ y, D (Di y) = y) (hDi : ∀ y, Di (D y) = y) :
    blockOperator A C B D =
      (blockOperator (.id ℂ E) (C.comp Di) 0 (.id ℂ F)).comp
        ((blockOperator (schurComplement A C B Di) 0 0 D).comp
          (blockOperator (.id ℂ E) 0 (Di.comp B) (.id ℂ F))) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Prod.ext <;>
    simp only [ContinuousLinearMap.comp_apply, blockOperator_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
      zero_add, add_zero, map_add, hD, hDi, schurComplement_apply] <;> module

theorem blockOperator_kernel_iff (A : E →L[ℂ] E) (C : F →L[ℂ] E)
    (B : E →L[ℂ] F) (D Di : F →L[ℂ] F)
    (hD : ∀ y, D (Di y) = y) (hDi : ∀ y, Di (D y) = y) (u : E × F) :
    blockOperator A C B D u = 0 ↔
      schurComplement A C B Di u.1 = 0 ∧ u.2 = -Di (B u.1) := by
  constructor
  · intro h
    have h₀ : A u.1 + C u.2 = 0 := congrArg Prod.fst h
    have h₁ : B u.1 + D u.2 = 0 := congrArg Prod.snd h
    have hd : D u.2 = -B u.1 :=
      (eq_neg_iff_add_eq_zero).mpr (by simpa only [add_comm] using h₁)
    have hy : u.2 = -Di (B u.1) := by
      rw [← hDi u.2, hd, map_neg]
    refine ⟨?_, hy⟩
    simpa only [hy, map_neg, sub_eq_add_neg, schurComplement_apply] using h₀
  · rintro ⟨hs, hy⟩
    apply Prod.ext
    · change A u.1 + C u.2 = 0
      simpa only [schurComplement_apply, hy, map_neg, sub_eq_add_neg] using hs
    · change B u.1 + D u.2 = 0
      rw [hy, map_neg, hD]
      exact add_neg_cancel _

section HilbertForm
open scoped InnerProductSpace
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The component sum is the inner product on the Hilbert direct sum.
The bounded inverse algebra above is invariant under its equivalent product norm. -/
def blockQuadratic (A : V →L[ℂ] V) (B : V →L[ℂ] W) (D : W →L[ℂ] W)
    (u : V × W) : ℝ :=
  (⟪u.1, A u.1⟫_ℂ + ⟪u.1, B.adjoint u.2⟫_ℂ +
    ⟪u.2, B u.1⟫_ℂ + ⟪u.2, D u.2⟫_ℂ).re

theorem schur_completion_square (A : V →L[ℂ] V) (B : V →L[ℂ] W)
    (D Di : W →L[ℂ] W) (hD : D.adjoint = D)
    (hDDi : ∀ y, D (Di y) = y) (x : V) (y : W) :
    ⟪x, A x⟫_ℂ + ⟪x, B.adjoint y⟫_ℂ + ⟪y, B x⟫_ℂ + ⟪y, D y⟫_ℂ =
      ⟪x, schurComplement A B.adjoint B Di x⟫_ℂ +
        ⟪y + Di (B x), D (y + Di (B x))⟫_ℂ := by
  have hadj (v w : W) : ⟪v, D w⟫_ℂ = ⟪D v, w⟫_ℂ := by
    rw [← D.adjoint_inner_left, hD]
  have hc : ⟪Di (B x), D y⟫_ℂ = ⟪B x, y⟫_ℂ := by rw [hadj, hDDi]
  have hd : ⟪Di (B x), B x⟫_ℂ = ⟪B x, Di (B x)⟫_ℂ := by
    simpa only [hDDi] using hadj (Di (B x)) (Di (B x))
  simp only [schurComplement_apply, map_add, inner_sub_right,
    inner_add_left, inner_add_right, B.adjoint_inner_right, hDDi]
  rw [hc, hd]
  ring

theorem blockQuadratic_nonnegative (A : V →L[ℂ] V) (B : V →L[ℂ] W)
    (D Di : W →L[ℂ] W) (hD : D.adjoint = D)
    (hDDi : ∀ y, D (Di y) = y)
    (hpD : ∀ y, 0 ≤ (⟪y, D y⟫_ℂ).re)
    (hpS : ∀ x, 0 ≤ (⟪x, schurComplement A B.adjoint B Di x⟫_ℂ).re)
    (u : V × W) : 0 ≤ blockQuadratic A B D u := by
  unfold blockQuadratic
  rw [schur_completion_square A B D Di hD hDDi, Complex.add_re]
  exact add_nonneg (hpS u.1) (hpD (u.2 + Di (B u.1)))
/-- Explicit bounded change from the product norm to the Hilbert direct sum. -/
def hilbertProductOperator (T : (V × W) →L[ℂ] (V × W)) :
    WithLp 2 (V × W) →L[ℂ] WithLp 2 (V × W) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ V W).symm.toContinuousLinearMap.comp
    (T.comp (WithLp.prodContinuousLinearEquiv 2 ℂ V W).toContinuousLinearMap)

theorem hilbertProductOperator_comp (T S : (V × W) →L[ℂ] (V × W)) :
    hilbertProductOperator (T.comp S) =
      (hilbertProductOperator T).comp (hilbertProductOperator S) := by
  apply ContinuousLinearMap.ext
  intro u
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ V W
  change e.symm (T (S (e u))) = e.symm (T (e (e.symm (S (e u)))))
  rw [e.apply_symm_apply]

theorem hilbertProductOperator_id :
    hilbertProductOperator (.id ℂ (V × W)) = .id ℂ (WithLp 2 (V × W)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact (WithLp.prodContinuousLinearEquiv 2 ℂ V W).symm_apply_apply u

theorem hilbertProductOperator_inner (A : V →L[ℂ] V) (B : V →L[ℂ] W)
    (D : W →L[ℂ] W) (u : WithLp 2 (V × W)) :
    (⟪u, hilbertProductOperator (blockOperator A B.adjoint B D) u⟫_ℂ).re =
      blockQuadratic A B D (WithLp.ofLp u) := by
  rw [WithLp.prod_inner_apply]
  change (⟪(WithLp.ofLp u).1, A (WithLp.ofLp u).1 + B.adjoint (WithLp.ofLp u).2⟫_ℂ +
    ⟪(WithLp.ofLp u).2, B (WithLp.ofLp u).1 + D (WithLp.ofLp u).2⟫_ℂ).re = _
  simp only [inner_add_right, blockQuadratic]
  ring

theorem hilbertBlock_nonnegative (A : V →L[ℂ] V) (B : V →L[ℂ] W)
    (D Di : W →L[ℂ] W) (hD : D.adjoint = D)
    (hDDi : ∀ y, D (Di y) = y)
    (hpD : ∀ y, 0 ≤ (⟪y, D y⟫_ℂ).re)
    (hpS : ∀ x, 0 ≤ (⟪x, schurComplement A B.adjoint B Di x⟫_ℂ).re)
    (u : WithLp 2 (V × W)) :
    0 ≤ (⟪u, hilbertProductOperator (blockOperator A B.adjoint B D) u⟫_ℂ).re := by
  rw [hilbertProductOperator_inner]
  exact blockQuadratic_nonnegative A B D Di hD hDDi hpD hpS (WithLp.ofLp u)

end HilbertForm
end Froehlich
