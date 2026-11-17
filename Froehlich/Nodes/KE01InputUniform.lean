import Froehlich.Nodes.KE01InputDerivativeBounds

set_option autoImplicit false
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance ke01UniformHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ke01UniformEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ke01UniformEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace

private theorem ke01_in_orderThree_box (alpha : Fin 3 → ℕ) (ha : (∑ i,alpha i) ≤ 3) :
    alpha ∈ multiIndexBox (fun _ : Fin 3 => 3) := by
  apply (mem_multiIndexBox _ alpha).mpr
  intro i
  exact (Finset.single_le_sum (fun j _ => Nat.zero_le (alpha j)) (Finset.mem_univ i)).trans ha

private theorem ke01_choose_common (K : (Fin 3 → ℕ) → ℝ) (hK : ∀ a,0 < K a) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 3 → ℕ, (∑ i,a i) ≤ 3 → K a ≤ C := by
  classical
  let S := multiIndexBox (fun _ : Fin 3 => 3)
  have hsum : 0 ≤ ∑ a ∈ S,K a := Finset.sum_nonneg (fun a _ => (hK a).le)
  refine ⟨(∑ a ∈ S,K a)+1,by linarith,?_⟩
  intro a ha
  have h := Finset.single_le_sum (s := S) (f := K) (fun b _ => (hK b).le)
    (ke01_in_orderThree_box a ha)
  exact h.trans (le_add_of_nonneg_right zero_le_one)

theorem ke01_groundSource_derivatives_common : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (alpha : Fin 3 → ℕ)
      (ha : (∑ i,alpha i) ≤ 3) (q : Fin 3 → ℝ),
      ‖coordinateMultiPartial alpha
        (fun t => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C*|g| := by
  classical
  have heach (a : Fin 3 → ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
        (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        (∑ i,a i) ≤ 3 → ‖coordinateMultiPartial a
          (fun t => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C*|g| := by
    by_cases ha : (∑ i,a i) ≤ 3
    · obtain ⟨C,hC,hB⟩ := auxiliaryGroundSourceVector_derivatives_uniform a ha
      exact ⟨C,hC,fun g e he hg hs q _ => hB g e he hg hs q⟩
    · exact ⟨1,one_pos,fun _ _ _ _ _ _ h => False.elim (ha h)⟩
  choose K hK hB using heach
  obtain ⟨C,hC,hCommon⟩ := ke01_choose_common K hK
  refine ⟨C,hC,?_⟩
  intro g e he hg hs a ha q
  exact (hB a g e he hg hs q ha).trans
    (mul_le_mul_of_nonneg_right (hCommon a ha) (abs_nonneg g))

theorem ke01_resolvent_derivatives_common : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
      (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (alpha : Fin 3 → ℕ) (ha : (∑ i,alpha i) ≤ 3) (q : Fin 3 → ℝ),
      ‖coordinateMultiPartial alpha
        (fun t => auxiliaryResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C := by
  classical
  have heach (a : Fin 3 → ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
        (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        (∑ i,a i) ≤ 3 → ‖coordinateMultiPartial a
          (fun t => auxiliaryResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C := by
    by_cases ha : (∑ i,a i) ≤ 3
    · obtain ⟨C,hC,hB⟩ := ke01_auxiliaryResolvent_derivatives_uniform a ha
      exact ⟨C,hC,fun n e hn he g hg hs q _ => hB n e hn he g hg hs q⟩
    · exact ⟨1,one_pos,fun _ _ _ _ _ _ _ _ h => False.elim (ha h)⟩
  choose K hK hB using heach
  obtain ⟨C,hC,hCommon⟩ := ke01_choose_common K hK
  refine ⟨C,hC,?_⟩
  intro n e hn he g hg hs a ha q
  exact (hB a n e hn he g hg hs q ha).trans (hCommon a ha)

end Froehlich
