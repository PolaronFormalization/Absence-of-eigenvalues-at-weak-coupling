import Froehlich.Nodes.BA02

/-! BA03: retained polarization supplies the mixed estimate, even with the
stronger constant C. Completeness is the existing bounded-map completeness. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem diagonal_to_mixed_bound (a : GW.Operators.AlgebraicForm V)
    (ha : ∀ w u, a w u = star (a u w)) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ u, ‖a u u‖ ≤ C * ‖u‖ ^ 2) (w u : V) :
    ‖a w u‖ ≤ 2 * C * ‖w‖ * ‖u‖ := by
  have h := GW.Operators.hermitian_mixed_bound a ha hC hd w u
  have hp : 0 ≤ C * ‖w‖ * ‖u‖ := by positivity
  linarith

def boundedFormOfDiagonal (a : GW.Operators.AlgebraicForm V)
    (ha : ∀ w u, a w u = star (a u w)) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ u, ‖a u u‖ ≤ C * ‖u‖ ^ 2) : GW.Analysis.BoundedForm V :=
  GW.Operators.boundedAlgebraicForm a hC (GW.Operators.hermitian_mixed_bound a ha hC hd)

@[simp] theorem boundedFormOfDiagonal_apply (a : GW.Operators.AlgebraicForm V)
    (ha : ∀ w u, a w u = star (a u w)) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ u, ‖a u u‖ ≤ C * ‖u‖ ^ 2) (w u : V) :
    boundedFormOfDiagonal a ha hC hd w u = a w u := rfl

example : CompleteSpace (GW.Analysis.BoundedForm V) := inferInstance

/-- The mixed norm topology is exactly the retained nested operator norm. -/
theorem boundedForm_norm_le_iff (a : GW.Analysis.BoundedForm V) {C : ℝ} (hC : 0 ≤ C) :
    ‖a‖ ≤ C ↔ ∀ w u, ‖a w u‖ ≤ C * ‖w‖ * ‖u‖ :=
  GW.Analysis.form_norm_le_iff a hC

open Filter
open scoped Topology

theorem boundedForm_eval_tendsto {ι : Type*} {l : Filter ι}
    {as : ι → GW.Analysis.BoundedForm V} {a : GW.Analysis.BoundedForm V}
    (h : Tendsto as l (𝓝 a)) (w u : V) :
    Tendsto (fun i => as i w u) l (𝓝 (a w u)) := by
  have h₁ : Tendsto (fun i => as i w) l (𝓝 (a w)) :=
    ((ContinuousLinearMap.apply' (V →L[ℂ] ℂ) (starRingEnd ℂ) w).continuous.tendsto a).comp h
  exact ((ContinuousLinearMap.apply ℂ ℂ u).continuous.tendsto (a w)).comp h₁

theorem boundedForm_limit_hermitian {ι : Type*} {l : Filter ι} [l.NeBot]
    {as : ι → GW.Analysis.BoundedForm V} {a : GW.Analysis.BoundedForm V}
    (h : Tendsto as l (𝓝 a))
    (hs : ∀ i w u, as i w u = star (as i u w)) :
    ∀ w u, a w u = star (a u w) := by
  intro w u
  apply tendsto_nhds_unique (boundedForm_eval_tendsto h w u)
  simpa only [← hs] using (boundedForm_eval_tendsto h u w).star

theorem boundedForm_limit_entry_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    {as : ι → GW.Analysis.BoundedForm V} {a : GW.Analysis.BoundedForm V}
    (h : Tendsto as l (𝓝 a)) (w u : V) (hz : ∀ i, as i w u = 0) : a w u = 0 := by
  have he := boundedForm_eval_tendsto h w u
  simp only [hz] at he
  exact tendsto_nhds_unique he tendsto_const_nhds

theorem boundedForm_limit_diagonal_bound {ι : Type*} {l : Filter ι} [l.NeBot]
    {as : ι → GW.Analysis.BoundedForm V} {a : GW.Analysis.BoundedForm V}
    (h : Tendsto as l (𝓝 a)) {C : ℝ}
    (hb : ∀ i u, ‖as i u u‖ ≤ C * ‖u‖ ^ 2) (u : V) :
    ‖a u u‖ ≤ C * ‖u‖ ^ 2 :=
  le_of_tendsto (boundedForm_eval_tendsto h u u).norm (Eventually.of_forall (fun i => hb i u))

theorem boundedForm_limit_diagonal_re_lower {ι : Type*} {l : Filter ι} [l.NeBot]
    {as : ι → GW.Analysis.BoundedForm V} {a : GW.Analysis.BoundedForm V}
    (h : Tendsto as l (𝓝 a)) {C : ℝ}
    (hb : ∀ i u, C * ‖u‖ ^ 2 ≤ (as i u u).re) (u : V) :
    C * ‖u‖ ^ 2 ≤ (a u u).re :=
  ge_of_tendsto ((Complex.continuous_re.tendsto (a u u)).comp (boundedForm_eval_tendsto h u u))
    (Eventually.of_forall (fun i => hb i u))

theorem boundedForm_cauchy_limit (as : ℕ → GW.Analysis.BoundedForm V)
    (h : CauchySeq as) : ∃ a, Tendsto as atTop (𝓝 a) :=
  cauchySeq_tendsto_of_complete h
end Froehlich
