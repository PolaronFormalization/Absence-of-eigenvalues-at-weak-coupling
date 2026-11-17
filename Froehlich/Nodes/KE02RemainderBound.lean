import Froehlich.Nodes.KE02QRSliceRegularity
import Froehlich.Nodes.KE02Vanishing
import Froehlich.Nodes.CA03VariableDifferences
import Froehlich.Nodes.AN03

set_option autoImplicit false
noncomputable section
namespace Froehlich

theorem remainderKernel_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (P q r : GW.Space), ‖P‖ ≤ 1/4 →
      |remainderKernel e he g hg hs P q r| ≤ C*omega q*omega r := by
  obtain ⟨M,hM,hB⟩ := kernelRealQRSlice_iterated_uniform
  refine ⟨4*M,by positivity,?_⟩
  intro e he g hg hs P q r hP
  let F := kernelRealQRSlice e he g hg hs P
  let v : Fin 2 → GW.Space × GW.Space := ![(q,0),(0,r)]
  have hF : ContDiff ℝ 3 F := kernelRealQRSlice_contDiff e he g hg hs P (by linarith)
  have hJet (A : List (Fin 2)) (hA : A.Nodup)
      (_hmem : ∀ i ∈ A,i ∈ ([0,1] : List (Fin 2))) (x : GW.Space × GW.Space) :
      ‖actualMixedDirectionalDerivative v F A x‖ ≤ M*(A.map (fun i => ‖v i‖)).prod := by
    have hcard := Finset.card_le_card (Finset.subset_univ A.toFinset)
    have hlen : A.length ≤ 3 := by
      rw [List.toFinset_card_of_nodup hA] at hcard
      norm_num only [Finset.card_univ,Fintype.card_fin] at hcard
      omega
    have hN : ‖iteratedFDeriv ℝ A.length F x‖ ≤ M := hB e he g hg hs P hP A.length hlen x
    unfold actualMixedDirectionalDerivative
    calc
      _ ≤ ‖iteratedFDeriv ℝ A.length F x‖*∏ j,‖listDirections v A j‖ :=
        (iteratedFDeriv ℝ A.length F x).le_opNorm _
      _ ≤ M*∏ j,‖listDirections v A j‖ := mul_le_mul_of_nonneg_right hN
        (Finset.prod_nonneg (fun j _ => norm_nonneg _))
      _ = _ := by rw [prod_norm_listDirections]
  have h := norm_iteratedFiniteDifference_of_actualMixed_norm v F 3 hF
    ([0,1] : List (Fin 2)) (by decide) (by norm_num) M hM.le hJet (0 : GW.Space × GW.Space)
  have hEq : iteratedFiniteDifference v ([0,1] : List (Fin 2)) F 0 =
      remainderKernel e he g hg hs P q r := by
    simp [iteratedFiniteDifference,finiteDifference,v,F,kernelRealQRSlice,remainderKernel_double_difference] <;> ring
  rw [hEq] at h
  have hv0 : ‖v 0‖ = ‖q‖ := by simp [v,Prod.norm_def,max_eq_left (norm_nonneg q)]
  have hv1 : ‖v 1‖ = ‖r‖ := by simp [v,Prod.norm_def,max_eq_right (norm_nonneg r)]
  norm_num only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    hv0,hv1,mul_one,Real.norm_eq_abs] at h
  simpa only [omega,mul_assoc] using h

end Froehlich
