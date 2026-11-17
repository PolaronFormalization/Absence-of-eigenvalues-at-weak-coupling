import Froehlich.Nodes.RS03DerivativesHessianChart

set_option autoImplicit false

/-! A parameter-uniform bound for the genuine physical total Hessian. -/
noncomputable section
namespace Froehlich

theorem auxiliarySelfEnergy_hessian_uniform : ∃ CE : ℝ, 0 < CE ∧
    ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (p : GW.Space),
      ‖fderiv ℝ (fderiv ℝ (fun x : GW.Space => auxiliarySelfEnergy e x he g hg hs)) p‖ ≤ CE*g^2 := by
  classical
  have hEach (i j : Fin 3) : ∃ C : ℝ, 0 < C ∧
      ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
        (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (q : Fin 3 → ℝ),
        ‖coordinateMultiPartial ((Pi.single i 1 : Fin 3 → ℕ)+Pi.single j 1)
          (fun t => auxiliarySelfEnergy e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C*g^2 := by
    apply auxiliarySelfEnergy_derivatives_uniform
    simp only [Pi.add_apply,Finset.sum_add_distrib,Finset.sum_pi_single']
    norm_num
  choose C hC hBound using hEach
  let M : ℝ := (∑ i : Fin 3, ∑ j : Fin 3, C i j)+1
  have hCs : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, C i j :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hC i j).le))
  have hM : 0 < M := by dsimp only [M]; linarith
  have hCi (i j : Fin 3) : C i j ≤ M := by
    have h1 : C i j ≤ ∑ k : Fin 3, C i k :=
      Finset.single_le_sum (fun k _ => (hC i k).le) (Finset.mem_univ j)
    have h2 : (∑ k : Fin 3, C i k) ≤ ∑ l : Fin 3, ∑ k : Fin 3, C l k :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => (hC l k).le)) (Finset.mem_univ i)
    exact (h1.trans h2).trans (le_add_of_nonneg_right zero_le_one)
  let A := coordinateDerivativeAssembler (E := (Fin 3 → ℝ) →L[ℝ] ℝ) 3
  let B := coordinateDerivativeAssembler (E := ℝ) 3
  let E := (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap
  let K := ‖A‖*‖B‖*M
  let CE := K*‖E‖*‖E‖+1
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg A.opNorm_nonneg B.opNorm_nonneg) hM.le
  have hCE : 0 < CE := by
    dsimp only [CE]
    have := mul_nonneg (mul_nonneg hK E.opNorm_nonneg) E.opNorm_nonneg
    linarith
  refine ⟨CE,hCE,?_⟩
  intro g e he hg hs p
  let F := fun x : GW.Space => auxiliarySelfEnergy e x he g hg hs
  let L := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap
  let f := fun t : Fin 3 → ℝ => F (L t)
  let q := (EuclideanSpace.equiv (Fin 3) ℝ) p
  have hF : ContDiff ℝ 2 F := auxiliarySelfEnergy_contDiff g e he hg hs
  have hf : ContDiff ℝ 2 f := by
    simpa only [f,Function.comp_def] using hF.comp L.contDiff
  have hentry (i j : Fin 3) :
      ‖fderiv ℝ (fderiv ℝ f) q (Pi.single i 1) (Pi.single j 1)‖ ≤ M*g^2 := by
    rw [rs03_hessian_basis_eq_multiPartial f hf q i j]
    exact (hBound i j g e he hg hs q).trans (mul_le_mul_of_nonneg_right (hCi i j) (sq_nonneg g))
  have hchart : ‖fderiv ℝ (fderiv ℝ f) q‖ ≤ K*g^2 := by
    have h := rs03_bilinear_norm_from_coordinates (fderiv ℝ (fderiv ℝ f) q)
      (M*g^2) (mul_nonneg hM.le (sq_nonneg g)) hentry
    simpa only [K,mul_assoc] using h
  have hEq (x y : GW.Space) : fderiv ℝ (fderiv ℝ F) p x y =
      fderiv ℝ (fderiv ℝ f) q (E x) (E y) := by
    have h := rs03_hessian_linearChart F hF L q (E x) (E y)
    simpa only [L,E,q,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply,f] using h.symm
  have hnorm : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ (K*‖E‖*‖E‖)*g^2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg
      (mul_nonneg (mul_nonneg hK E.opNorm_nonneg) E.opNorm_nonneg) (sq_nonneg g))
    intro x
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hK E.opNorm_nonneg) E.opNorm_nonneg) (sq_nonneg g)) (norm_nonneg x))
    intro y
    rw [hEq]
    have h := ((fderiv ℝ (fderiv ℝ f) q).le_opNorm (E x))
    have hb : ‖fderiv ℝ (fderiv ℝ f) q (E x) (E y)‖ ≤
        ‖fderiv ℝ (fderiv ℝ f) q‖*‖E x‖*‖E y‖ :=
      ((fderiv ℝ (fderiv ℝ f) q (E x)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    have hE1 := E.le_opNorm x
    have hE2 := E.le_opNorm y
    have hmul := mul_le_mul (mul_le_mul hchart hE1 (norm_nonneg _) (mul_nonneg hK (sq_nonneg g)))
      hE2 (norm_nonneg _) (mul_nonneg (mul_nonneg hK (sq_nonneg g))
        (mul_nonneg E.opNorm_nonneg (norm_nonneg x)))
    exact hb.trans (by convert hmul using 1 <;> ring)
  exact hnorm.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg g))

end Froehlich
