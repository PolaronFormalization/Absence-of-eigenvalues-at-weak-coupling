import Froehlich.Nodes.KE02QRSliceRegularity
import Froehlich.Nodes.KE02Vanishing
import Froehlich.Nodes.CA03SingleDifference
import Froehlich.Nodes.AN03

set_option autoImplicit false
noncomputable section
namespace Froehlich

private def ke02_qSection : GW.Space →L[ℝ] GW.Space × GW.Space :=
  (ContinuousLinearMap.id ℝ GW.Space).prod (0 : GW.Space →L[ℝ] GW.Space)

private theorem ke02_qSection_affine (r q : GW.Space) :
    ((0 : GW.Space),r)+ke02_qSection q = (q,r) := by
  apply Prod.ext
  · change 0+q=q; exact zero_add q
  · change r+0=r; exact add_zero r

private theorem ke02_qSection_norm : ‖ke02_qSection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖(q,(0 : GW.Space))‖ ≤ 1*‖q‖
  simp only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg q),one_mul,le_refl]

private theorem ke02_doubleDifference_q_native (F : (GW.Space × GW.Space) → ℝ)
    (hF : ContDiff ℝ 3 F) (j : ℕ) (hj : 1 ≤ j) (hj3 : j ≤ 3) (q r : GW.Space) :
    iteratedFDeriv ℝ j (fun p : GW.Space => F (p,r)-F (p,0)-F (0,r)+F (0,0)) q =
      (iteratedFDeriv ℝ j F (q,r)-iteratedFDeriv ℝ j F (q,0)).compContinuousLinearMap
        (fun _ => ke02_qSection) := by
  let Fr := fun p : GW.Space => F (((0 : GW.Space),r)+ke02_qSection p)
  let F0 := fun p : GW.Space => F (((0 : GW.Space),(0 : GW.Space))+ke02_qSection p)
  have hFr : ContDiff ℝ j Fr := (hF.of_le (by exact_mod_cast hj3)).comp
    (contDiff_const.add ke02_qSection.contDiff)
  have hF0 : ContDiff ℝ j F0 := (hF.of_le (by exact_mod_cast hj3)).comp
    (contDiff_const.add ke02_qSection.contDiff)
  have hf : (fun p : GW.Space => F (p,r)-F (p,0)-F (0,r)+F (0,0)) =
      (Fr-F0)-(fun _ => F (0,r)-F (0,0)) := by
    funext p
    simp only [Pi.sub_apply,Fr,F0,ke02_qSection_affine]
    ring
  have hDiff : ContDiff ℝ j (Fr-F0) := by
    simpa only [Pi.sub_def] using! hFr.sub hF0
  have hSub := iteratedFDeriv_sub_apply (f := Fr-F0) (g := fun _ : GW.Space => F (0,r)-F (0,0))
    (x := q) hDiff.contDiffAt contDiffAt_const
  rw [hf,hSub]
  simp only [iteratedFDeriv_const_of_ne (show j ≠ 0 by omega),Pi.zero_apply,sub_zero]
  rw [iteratedFDeriv_sub_apply (f := Fr) (g := F0) (x := q) hFr.contDiffAt hF0.contDiffAt]
  have hr := iteratedFDeriv_comp_affine_at ((0 : GW.Space),r) ke02_qSection F j q
    (hF.of_le (by exact_mod_cast hj3)).contDiffAt
  have h0 := iteratedFDeriv_comp_affine_at ((0 : GW.Space),(0 : GW.Space)) ke02_qSection F j q
    (hF.of_le (by exact_mod_cast hj3)).contDiffAt
  simp only [ke02_qSection_affine] at hr h0
  have hr' : iteratedFDeriv ℝ j Fr q =
      (iteratedFDeriv ℝ j F (q,r)).compContinuousLinearMap (fun _ => ke02_qSection) := by
    simpa only [Fr,ke02_qSection_affine] using! hr
  have h0' : iteratedFDeriv ℝ j F0 q =
      (iteratedFDeriv ℝ j F (q,0)).compContinuousLinearMap (fun _ => ke02_qSection) := by
    simpa only [F0,ke02_qSection_affine] using! h0
  rw [hr',h0']
  apply ContinuousMultilinearMap.ext
  intro m
  rfl

private theorem ke02_iterated_difference_bound (F : (GW.Space × GW.Space) → ℝ)
    (hF : ContDiff ℝ 3 F) (M : ℝ)
    (hB : ∀ k ≤ 3,∀ qr,‖iteratedFDeriv ℝ k F qr‖ ≤ M)
    (j : ℕ) (hj : j+1 ≤ 3) (q r : GW.Space) :
    ‖iteratedFDeriv ℝ j F (q,r)-iteratedFDeriv ℝ j F (q,0)‖ ≤ 2*M*omega r := by
  have hG : ContDiff ℝ 1 (iteratedFDeriv ℝ j F) := hF.iteratedFDeriv_right (by exact_mod_cast (show 1+j ≤ 3 by omega))
  have h1 (x : GW.Space × GW.Space) : ‖fderiv ℝ (iteratedFDeriv ℝ j F) x‖ ≤ M := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hB (j+1) hj x
  have h := norm_finiteDifference_le (iteratedFDeriv ℝ j F) M
    (hG.differentiable (by norm_num)) (hB j (by omega)) h1 (q,0) (0,r)
  simpa [finiteDifference,Prod.norm_def,omega] using h

theorem remainderKernel_qDerivatives_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q r : GW.Space), ‖P‖ ≤ 1/4 →
      ‖fderiv ℝ (fun p => remainderKernel e he g hg hs P p r) q‖+
      ‖fderiv ℝ (fderiv ℝ (fun p => remainderKernel e he g hg hs P p r)) q‖ ≤ C*omega r := by
  obtain ⟨M,hM,hB⟩ := kernelRealQRSlice_iterated_uniform
  refine ⟨4*M,by positivity,?_⟩
  intro e he g hg hs P q r hP
  let F := kernelRealQRSlice e he g hg hs P
  have hF : ContDiff ℝ 3 F := kernelRealQRSlice_contDiff e he g hg hs P (by linarith)
  have hf : (fun p => remainderKernel e he g hg hs P p r) =
      (fun p : GW.Space => F (p,r)-F (p,0)-F (0,r)+F (0,0)) := by
    funext p
    exact remainderKernel_double_difference e he g hg hs P p r
  have hj (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) :
      ‖iteratedFDeriv ℝ j (fun p => remainderKernel e he g hg hs P p r) q‖ ≤ 2*M*omega r := by
    rw [hf,ke02_doubleDifference_q_native F hF j hj1 (by omega) q r]
    have h := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j F (q,r)-iteratedFDeriv ℝ j F (q,0)) (fun _ : Fin j => ke02_qSection)
    have hp : ‖ke02_qSection‖^j ≤ 1 := by
      interval_cases j <;> norm_num <;>
        nlinarith [ke02_qSection_norm,norm_nonneg ke02_qSection]
    have ht := ke02_iterated_difference_bound F hF M (hB e he g hg hs P hP) j (by omega) q r
    refine h.trans ?_
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] 
    exact ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)).trans ht
  have h1 := hj 1 (by norm_num) (by norm_num)
  have h2 := hj 2 (by norm_num) (by norm_num)
  rw [norm_iteratedFDeriv_one] at h1
  rw [←norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] at h2
  nlinarith

end Froehlich
