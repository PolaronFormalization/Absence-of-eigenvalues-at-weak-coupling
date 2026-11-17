import Froehlich.Nodes.CA01TotalDerivative

set_option autoImplicit false

/-! Finite coordinate reconstruction of a genuine bounded bilinear map. -/
noncomputable section
namespace Froehlich

private theorem rs03_single_scalar (d : ℕ) (x : Fin d → ℝ) (i : Fin d) :
    Pi.single i (x i) = x i • (Pi.single i (1 : ℝ) : Fin d → ℝ) := by
  classical
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_apply,h,Ne.symm h]

theorem rs03_coordinateDerivative_reconstruct {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] E) :
    coordinateDerivative d (fun i => L (Pi.single i 1)) = L := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  rw [coordinateDerivative_apply]
  have hx := congrArg L (Finset.univ_sum_single x)
  simp only [map_sum,rs03_single_scalar,map_smul] at hx
  exact hx

theorem rs03_bilinear_norm_from_coordinates
    (A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ i j : Fin 3, ‖A (Pi.single i 1) (Pi.single j 1)‖ ≤ M) :
    ‖A‖ ≤ ‖coordinateDerivativeAssembler (E := (Fin 3 → ℝ) →L[ℝ] ℝ) 3‖ *
      ‖coordinateDerivativeAssembler (E := ℝ) 3‖ * M := by
  let L := coordinateDerivativeAssembler (E := ℝ) 3
  let B := coordinateDerivativeAssembler (E := (Fin 3 → ℝ) →L[ℝ] ℝ) 3
  have hL := L.opNorm_nonneg
  have hB := B.opNorm_nonneg
  have hrow (i : Fin 3) : ‖A (Pi.single i 1)‖ ≤ ‖L‖*M := by
    have ht : ‖(fun j : Fin 3 => A (Pi.single i 1) (Pi.single j 1))‖ ≤ M :=
      (pi_norm_le_iff_of_nonneg hM).mpr (hA i)
    calc
      _ = ‖L (fun j => A (Pi.single i 1) (Pi.single j 1))‖ :=
        congrArg (fun T : (Fin 3 → ℝ) →L[ℝ] ℝ => ‖T‖)
          (rs03_coordinateDerivative_reconstruct 3 (A (Pi.single i 1))).symm
      _ ≤ ‖L‖ * ‖(fun j : Fin 3 => A (Pi.single i 1) (Pi.single j 1))‖ := L.le_opNorm _
      _ ≤ ‖L‖*M := mul_le_mul_of_nonneg_left ht hL
  have ht : ‖(fun i : Fin 3 => A (Pi.single i 1))‖ ≤ ‖L‖*M :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg hL hM)).mpr hrow
  calc
    _ = ‖B (fun i => A (Pi.single i 1))‖ :=
      congrArg (fun T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ => ‖T‖)
        (rs03_coordinateDerivative_reconstruct 3 A).symm
    _ ≤ ‖B‖ * ‖(fun i : Fin 3 => A (Pi.single i 1))‖ := B.le_opNorm _
    _ ≤ ‖B‖*(‖L‖*M) := mul_le_mul_of_nonneg_left ht hB
    _ = _ := mul_assoc _ _ _ |>.symm

end Froehlich
