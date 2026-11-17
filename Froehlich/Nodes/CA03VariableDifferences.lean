import Froehlich.Nodes.CA03ActualMixed
import Mathlib.Algebra.BigOperators.Fin

/-! Source CA03 in separate vector variables. The mixed derivative is the
actual native iterated derivative restricted to precisely the selected
variable slots. The derivative-start version counts its initial order. -/
noncomputable section
namespace Froehlich
variable {ι D X V : Type*} [DecidableEq ι]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem listDirections_eq_get (v : ι → D) (A : List ι) (k : Fin A.length) :
    listDirections v A k = v (A.get k) := by
  induction A with
  | nil => exact Fin.elim0 k
  | cons i A ih =>
    refine Fin.cases rfl (fun j => ?_) k
    exact ih j

theorem prod_norm_listDirections (h : ι → D) (A : List ι) :
    (∏ k, ‖listDirections h A k‖) = (A.map (fun i => ‖h i‖)).prod := by
  induction A with
  | nil => simp only [List.length_nil,Fin.prod_univ_zero,List.map_nil,List.prod_nil]
  | cons i A ih =>
    simp only [List.length_cons,Fin.prod_univ_succ,listDirections,Fin.cons_zero,Fin.cons_succ,
      List.map_cons,List.prod_cons,ih]

def selectedMixedFDeriv (L : ι → D →L[ℝ] X) (F : X → V) (A : List ι) (x : X) :
    ContinuousMultilinearMap ℝ (fun _ : Fin A.length => D) V :=
  (iteratedFDeriv ℝ A.length F x).compContinuousLinearMap (fun k => L (A.get k))

theorem selectedMixedFDeriv_apply (L : ι → D →L[ℝ] X) (h : ι → D)
    (F : X → V) (A : List ι) (x : X) :
    selectedMixedFDeriv L F A x (listDirections h A) =
      actualMixedDirectionalDerivative (fun i => L i (h i)) F A x := by
  apply congrArg (fun u => iteratedFDeriv ℝ A.length F x u)
  funext k
  rw [listDirections_eq_get,listDirections_eq_get]
  rfl

theorem norm_iteratedFiniteDifference_of_selectedMixed
    (L : ι → D →L[ℝ] X) (h : ι → D) (F : X → V)
    (r : ℕ) (hF : ContDiff ℝ r F) (is : List ι) (hnodup : is.Nodup) (hlen : is.length ≤ r)
    (M : ℝ) (hbound : ∀ A, A.Nodup → (∀ i ∈ A, i ∈ is) → ∀ x,
      ‖selectedMixedFDeriv L F A x‖ ≤ M) (x : X) :
    ‖iteratedFiniteDifference (fun i => L i (h i)) is F x‖ ≤
      2^is.length * M * (is.map (fun i => min ‖h i‖ 1)).prod := by
  have hM : 0 ≤ M := (norm_nonneg (selectedMixedFDeriv L F [] x)).trans
    (hbound [] List.nodup_nil (by simp) x)
  apply norm_iteratedFiniteDifference_of_actualMixed (fun i => L i (h i)) F r hF is hnodup hlen
    (fun i => ‖h i‖) (fun i => norm_nonneg _) M hM
  intro A hA hmem y
  rw [← selectedMixedFDeriv_apply L h F A y]
  have hv := (selectedMixedFDeriv L F A y).le_opNorm (listDirections h A)
  calc
    _ ≤ ‖selectedMixedFDeriv L F A y‖ * ∏ k, ‖listDirections h A k‖ := hv
    _ ≤ M * ∏ k, ‖listDirections h A k‖ := mul_le_mul_of_nonneg_right
      (hbound A hA hmem y) (Finset.prod_nonneg (fun k hk => norm_nonneg _))
    _ = _ := by rw [prod_norm_listDirections]

/-- Starting at an actual order-n derivative uses only n+l ≤ r. -/
theorem norm_iteratedFiniteDifference_of_selectedMixed_derivative
    (L : ι → D →L[ℝ] X) (h : ι → D) (F : X → V)
    (r n : ℕ) (hF : ContDiff ℝ r F) (is : List ι) (hnodup : is.Nodup)
    (htotal : n+is.length ≤ r) (M : ℝ)
    (hbound : ∀ A, A.Nodup → (∀ i ∈ A, i ∈ is) → ∀ x,
      ‖selectedMixedFDeriv L (iteratedFDeriv ℝ n F) A x‖ ≤ M) (x : X) :
    ‖iteratedFiniteDifference (fun i => L i (h i)) is (iteratedFDeriv ℝ n F) x‖ ≤
      2^is.length * M * (is.map (fun i => min ‖h i‖ 1)).prod := by
  have hd : ContDiff ℝ is.length (iteratedFDeriv ℝ n F) :=
    hF.iteratedFDeriv_right (by exact_mod_cast (show is.length+n ≤ r by omega))
  exact norm_iteratedFiniteDifference_of_selectedMixed L h (iteratedFDeriv ℝ n F)
    is.length hd is hnodup le_rfl M hbound x

/-- A fixed chosen derivative, rather than the whole derivative operator,
can be the starting function. Only its selected difference-slot mixed
operators are bounded; its initial order is counted in the regularity. -/
theorem norm_iteratedFiniteDifference_of_selectedMixed_fixedDerivative
    {κ : Type*} (v0 : κ → X) (A0 : List κ)
    (L : ι → D →L[ℝ] X) (h : ι → D) (F : X → V)
    (r : ℕ) (hF : ContDiff ℝ r F) (is : List ι) (hnodup : is.Nodup)
    (htotal : A0.length+is.length ≤ r) (M : ℝ)
    (hbound : ∀ A, A.Nodup → (∀ i ∈ A, i ∈ is) → ∀ x,
      ‖selectedMixedFDeriv L (actualMixedDirectionalDerivative v0 F A0) A x‖ ≤ M) (x : X) :
    ‖iteratedFiniteDifference (fun i => L i (h i)) is
      (actualMixedDirectionalDerivative v0 F A0) x‖ ≤
      2^is.length * M * (is.map (fun i => min ‖h i‖ 1)).prod := by
  have hd : ContDiff ℝ is.length (iteratedFDeriv ℝ A0.length F) :=
    hF.iteratedFDeriv_right (by exact_mod_cast (show is.length+A0.length ≤ r by omega))
  have he : ContDiff ℝ is.length (actualMixedDirectionalDerivative v0 F A0) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin A0.length => X) V (listDirections v0 A0)).contDiff.comp hd
  exact norm_iteratedFiniteDifference_of_selectedMixed L h
    (actualMixedDirectionalDerivative v0 F A0) is.length he is hnodup le_rfl M hbound x

section Variables
variable [Fintype ι]

/-- Canonical separate-variable statement: each difference changes only slot i. -/
theorem norm_iteratedVariableDifference (h : ι → D) (F : (ι → D) → V)
    (r : ℕ) (hF : ContDiff ℝ r F) (is : List ι) (hnodup : is.Nodup) (hlen : is.length ≤ r)
    (M : ℝ) (hbound : ∀ A, A.Nodup → (∀ i ∈ A, i ∈ is) → ∀ x,
      ‖selectedMixedFDeriv (ContinuousLinearMap.single ℝ (fun _ : ι => D)) F A x‖ ≤ M)
    (x : ι → D) :
    ‖iteratedFiniteDifference (fun i => Pi.single i (h i)) is F x‖ ≤
      2^is.length * M * (is.map (fun i => min ‖h i‖ 1)).prod :=
  norm_iteratedFiniteDifference_of_selectedMixed
    (ContinuousLinearMap.single ℝ (fun _ : ι => D)) h F r hF is hnodup hlen M hbound x

end Variables
end Froehlich
