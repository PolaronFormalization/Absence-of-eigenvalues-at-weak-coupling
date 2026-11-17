import Froehlich.Nodes.CA03LocalRectangularSlice
import Froehlich.Nodes.CA03VariableDifferences
import Froehlich.Nodes.AN03

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Global qr differences of the actual momentum difference; only the original
function's ordinary regularity on the true momentum slab is assumed. -/
theorem norm_rectangular_qr_differences
    (F : (GW.Space × (GW.Space × GW.Space)) → V) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ t ∈ rectangularMomentumSlab, ContDiffAt ℝ 3 F t)
    (hB : ∀ k ≤ 3, ∀ t ∈ rectangularMomentumSlab, ‖iteratedFDeriv ℝ k F t‖ ≤ M)
    (P q r : GW.Space) (hP : ‖P‖ ≤ 1/4)
    (is : List (Fin 2)) (his : is.Nodup) (x : GW.Space × GW.Space) :
    ‖iteratedFiniteDifference (![(q,0),(0,r)] : Fin 2 → GW.Space × GW.Space)
        is (rectangularMomentumDifference F P) x‖ ≤
      2^is.length*((1+‖rectangularQRInclusion‖)^2*M*‖P‖)*
        (is.map (fun i => min ‖(![(q,0),(0,r)] : Fin 2 → GW.Space × GW.Space) i‖ 1)).prod := by
  let G := rectangularMomentumDifference F P
  let v : Fin 2 → GW.Space × GW.Space := ![(q,0),(0,r)]
  let K := (1+‖rectangularQRInclusion‖)^2*M*‖P‖
  have hG : ContDiff ℝ 2 G :=
    (rectangularMomentumDifference_contDiff F hF P hP).of_le (by norm_num)
  have hlen (A : List (Fin 2)) (hA : A.Nodup) : A.length ≤ 2 := by
    have h := Finset.card_le_card (Finset.subset_univ A.toFinset)
    rw [List.toFinset_card_of_nodup hA] at h
    simpa only [Finset.card_univ,Fintype.card_fin] using h
  apply norm_iteratedFiniteDifference_of_actualMixed_norm v G 2 hG is his (hlen is his) K
    (mul_nonneg (mul_nonneg (sq_nonneg _) hM) (norm_nonneg P))
  intro A hA _ y
  unfold actualMixedDirectionalDerivative
  have hb := rectangularMomentumDifference_iterated_bound F M hM hF hB P hP
    A.length (hlen A hA) y
  calc
    _ ≤ ‖iteratedFDeriv ℝ A.length G y‖*∏ j,‖listDirections v A j‖ :=
      (iteratedFDeriv ℝ A.length G y).le_opNorm _
    _ ≤ K*∏ j,‖listDirections v A j‖ := mul_le_mul_of_nonneg_right hb
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := by rw [prod_norm_listDirections]

/-- One unrestricted q difference and one untruncated momentum difference. -/
theorem norm_rectangular_momentum_q
    (F : (GW.Space × (GW.Space × GW.Space)) → V) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ t ∈ rectangularMomentumSlab, ContDiffAt ℝ 3 F t)
    (hB : ∀ k ≤ 3, ∀ t ∈ rectangularMomentumSlab, ‖iteratedFDeriv ℝ k F t‖ ≤ M)
    (P q : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    ‖finiteDifference (P,((0 : GW.Space),0))
      (finiteDifference ((0 : GW.Space),(q,0)) F) 0‖ ≤
      2*(1+‖rectangularQRInclusion‖)^2*M*‖P‖*omega q := by
  have h := norm_rectangular_qr_differences F M hM hF hB P q 0 hP
    ([0] : List (Fin 2)) (by decide) 0
  have heq : iteratedFiniteDifference (![(q,0),(0,(0 : GW.Space))] : Fin 2 → GW.Space × GW.Space)
      [0] (rectangularMomentumDifference F P) 0 =
      finiteDifference (P,((0 : GW.Space),0))
        (finiteDifference ((0 : GW.Space),(q,0)) F) 0 := by
    simp only [iteratedFiniteDifference,finiteDifference,rectangularMomentumDifference,
      Matrix.cons_val_zero,zero_add,Prod.mk_add_mk,add_zero]
    abel
  rw [heq] at h
  simpa [omega,Prod.norm_def,max_eq_left (norm_nonneg q),mul_assoc] using h

/-- Two unrestricted qr differences and one untruncated momentum difference. -/
theorem norm_rectangular_momentum_qr
    (F : (GW.Space × (GW.Space × GW.Space)) → V) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ t ∈ rectangularMomentumSlab, ContDiffAt ℝ 3 F t)
    (hB : ∀ k ≤ 3, ∀ t ∈ rectangularMomentumSlab, ‖iteratedFDeriv ℝ k F t‖ ≤ M)
    (P q r : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    ‖finiteDifference (P,((0 : GW.Space),0))
      (finiteDifference ((0 : GW.Space),(q,0))
        (finiteDifference ((0 : GW.Space),(0,r)) F)) 0‖ ≤
      4*(1+‖rectangularQRInclusion‖)^2*M*‖P‖*omega q*omega r := by
  have h := norm_rectangular_qr_differences F M hM hF hB P q r hP
    ([0,1] : List (Fin 2)) (by decide) 0
  have heq : iteratedFiniteDifference (![(q,0),(0,r)] : Fin 2 → GW.Space × GW.Space)
      [0,1] (rectangularMomentumDifference F P) 0 =
      finiteDifference (P,((0 : GW.Space),0))
        (finiteDifference ((0 : GW.Space),(q,0))
          (finiteDifference ((0 : GW.Space),(0,r)) F)) 0 := by
    simp only [iteratedFiniteDifference,finiteDifference,rectangularMomentumDifference,
      Matrix.cons_val_zero,Matrix.cons_val_one,zero_add,Prod.mk_add_mk,add_zero]
    abel
  rw [heq] at h
  have hfour : (2 : ℝ)^([0,1] : List (Fin 2)).length = 4 := by norm_num
  rw [hfour] at h
  simpa [omega,Prod.norm_def,max_eq_left (norm_nonneg q),max_eq_right (norm_nonneg r),mul_assoc] using h

end Froehlich
