import Froehlich.Nodes.CA03MixedJets
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Data.Finset.Card

/-! Actual native iterated Fréchet derivatives instantiate the ordered
mixed jets. Bounds are required only on distinct selected directional
mixed derivatives, not on the whole total derivative operator. -/
noncomputable section
namespace Froehlich
variable {ι D V : Type*} [DecidableEq ι]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def listDirections (v : ι → D) : (A : List ι) → Fin A.length → D
  | [] => Fin.elim0
  | i::A => Fin.cons (v i) (listDirections v A)

def actualMixedDirectionalDerivative (v : ι → D) (F : D → V) (A : List ι) (x : D) : V :=
  iteratedFDeriv ℝ A.length F x (listDirections v A)

theorem actualMixedDirectionalDerivative_nil (v : ι → D) (F : D → V) :
    actualMixedDirectionalDerivative v F [] = F := rfl

theorem actualMixedDirectionalDerivative_hasDerivAt (v : ι → D) (F : D → V)
    (r : ℕ) (hF : ContDiff ℝ r F) (A : List ι) (hlen : A.length < r)
    (i : ι) (x : D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => actualMixedDirectionalDerivative v F A (x+s • v i))
      (actualMixedDirectionalDerivative v F (i::A) (x+t • v i)) t := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ A.length F) (x+t • v i) :=
    (hF.differentiable_iteratedFDeriv (by exact_mod_cast hlen)) _
  have hl : HasDerivAt (fun s : ℝ => x+s • v i) (v i) t := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const (v i)).const_add x
  have hc := (hd.hasFDerivAt.continuousMultilinear_apply_const (listDirections v A)).comp_hasDerivAt t hl
  change HasDerivAt (fun s : ℝ => actualMixedDirectionalDerivative v F A (x+s • v i))
    ((fderiv ℝ (iteratedFDeriv ℝ A.length F) (x+t • v i)) (v i) (listDirections v A)) t at hc
  exact hc

/-- The full finite-difference estimate from actual selected mixed derivatives.
The native derivative maps can themselves be the starting function F. -/
theorem norm_iteratedFiniteDifference_of_actualMixed
    (v : ι → D) (F : D → V) (r : ℕ) (hF : ContDiff ℝ r F)
    (is : List ι) (hnodup : is.Nodup) (hlen : is.length ≤ r)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ A, A.Nodup → (∀ i ∈ A, i ∈ is) → ∀ x,
      ‖actualMixedDirectionalDerivative v F A x‖ ≤ M*(A.map c).prod)
    (x : D) :
    ‖iteratedFiniteDifference v is F x‖ ≤
      2^is.length * M * (is.map (fun i => min (c i) 1)).prod := by
  have hbd : ∀ A, A.Nodup → (∀ i ∈ A, i ∈ is.toFinset) → ∀ x,
      ‖actualMixedDirectionalDerivative v F A x‖ ≤ M*(A.map c).prod := by
    intro A hA hmem y
    exact hbound A hA (fun i hi => List.mem_toFinset.mp (hmem i hi)) y
  have hderiv : ∀ A, A.Nodup → (∀ j ∈ A, j ∈ is.toFinset) →
      ∀ i ∈ is.toFinset, i ∉ A → ∀ x t,
      HasDerivAt (fun s : ℝ => actualMixedDirectionalDerivative v F A (x+s • v i))
        (actualMixedDirectionalDerivative v F (i::A) (x+t • v i)) t := by
    intro A hA hmem i hi hinot y t
    have hAn : (i::A).Nodup := List.nodup_cons.mpr ⟨hinot,hA⟩
    have hsubset : (i::A).toFinset ⊆ is.toFinset := by
      intro j hj
      rcases List.mem_cons.mp (List.mem_toFinset.mp hj) with hji|hjA
      · exact hji ▸ hi
      · exact hmem j hjA
    have hcard := Finset.card_le_card hsubset
    rw [List.toFinset_card_of_nodup hAn,List.toFinset_card_of_nodup hnodup,List.length_cons] at hcard
    exact actualMixedDirectionalDerivative_hasDerivAt v F r hF A (by omega) i y t
  have hb := norm_iteratedFiniteDifference_of_mixedJets is.toFinset v c hc (actualMixedDirectionalDerivative v F) M hM hbd hderiv is hnodup
    (fun i hi => List.mem_toFinset.mpr hi) [] List.nodup_nil (by simp) (by simp) x
  simpa only [actualMixedDirectionalDerivative_nil,List.map_nil,List.prod_nil,mul_one] using hb

/-- In ambient coordinates the natural choice is c_i = ‖v_i‖. -/
theorem norm_iteratedFiniteDifference_of_actualMixed_norm
    (v : ι → D) (F : D → V) (r : ℕ) (hF : ContDiff ℝ r F)
    (is : List ι) (hnodup : is.Nodup) (hlen : is.length ≤ r)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ A, A.Nodup → (∀ i ∈ A, i ∈ is) → ∀ x,
      ‖actualMixedDirectionalDerivative v F A x‖ ≤ M*(A.map (fun i => ‖v i‖)).prod)
    (x : D) :
    ‖iteratedFiniteDifference v is F x‖ ≤
      2^is.length * M * (is.map (fun i => min ‖v i‖ 1)).prod :=
  norm_iteratedFiniteDifference_of_actualMixed v F r hF is hnodup hlen
    (fun i => ‖v i‖) (fun i => norm_nonneg _) M hM hbound x

end Froehlich
