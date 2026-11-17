import Froehlich.Nodes.KE01AffineInputBounds
import Froehlich.Nodes.KE01BilinearBounds

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
open scoped BoundedEndReal
local instance ke01JFockReal : NormedSpace ℝ GW.Fock.Carrier := NormedSpace.restrictScalars ℝ ℂ _
local instance ke01JFockModule : Module ℝ GW.Fock.Carrier := ke01JFockReal.toModule
local instance ke01JFockBounded : IsBoundedSMul ℝ GW.Fock.Carrier := NormedSpace.toIsBoundedSMul
local instance ke01JEndGroup : NormedAddCommGroup (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) := ContinuousLinearMap.toNormedAddCommGroup
local instance ke01JEndReal : NormedSpace ℝ (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  (BoundedEndReal.realNormedAlgebra (E := GW.Fock.Carrier)).toNormedSpace
local instance ke01JEndBounded : IsBoundedSMul ℝ (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) := NormedSpace.toIsBoundedSMul

private theorem ke01_vacuum_sub_bound {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (F : D → GW.Fock.Carrier) (hF : ContDiff ℝ 3 F) (A : ℝ)
    (hB : ∀ k ≤ 3,∀ x,‖iteratedFDeriv ℝ k F x‖ ≤ A)
    (k : ℕ) (hk : k ≤ 3) (x : D) :
    ‖iteratedFDeriv ℝ k (fun y => GW.Fock.vacuum-F y) x‖ ≤ 1+A := by
  have hc : ‖iteratedFDeriv ℝ k (fun _ : D => GW.Fock.vacuum) x‖ ≤ 1 := by
    cases k with
    | zero => simp only [norm_iteratedFDeriv_zero,GW.Fock.vacuum_norm,le_refl]
    | succ k => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]; norm_num
  have he := iteratedFDeriv_sub_apply (contDiffAt_const : ContDiffAt ℝ k (fun _ : D => GW.Fock.vacuum) x)
    (hF.of_le (by exact_mod_cast hk)).contDiffAt
  have hn : ‖iteratedFDeriv ℝ k (fun y => GW.Fock.vacuum-F y) x‖ ≤
      ‖iteratedFDeriv ℝ k (fun _ : D => GW.Fock.vacuum) x‖+‖iteratedFDeriv ℝ k F x‖ := by
    change ‖iteratedFDeriv ℝ k ((fun _ : D => GW.Fock.vacuum)-F) x‖ ≤ _
    rw [he]
    exact norm_sub_le _ _
  exact hn.trans (add_le_add hc (hB k hk x))

theorem thresholdKernelJ_iterated_uniform : ∃ C : ℝ, 0 < C ∧
    ∀ (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (k : ℕ) (hk : k ≤ 3) (x : Fin 9 → ℝ),
      ‖iteratedFDeriv ℝ k (thresholdKernelJCoordinates e he g hg hs) x‖ ≤ C := by
  obtain ⟨A,hA,hAB⟩ := ke01_groundSource_affine_common (kernelInputCoordinates 1)
  obtain ⟨B,hB,hBB⟩ := ke01_groundSource_affine_common (kernelInputCoordinates 2)
  obtain ⟨Z,hZ,hZB⟩ := ke01_extendedResolvent_affine_common kernelSumCoordinates
  obtain ⟨X,hX,hXB⟩ := ke01_extendedResolvent_affine_common kernelNegativeCoordinates
  let E : (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) →L[ℝ] GW.Fock.Carrier →L[ℝ] GW.Fock.Carrier := by
    simpa only [] using! ke01_operatorEvaluation_bilinear.toContinuousLinearMap
  let I : GW.Fock.Carrier →L[ℝ] GW.Fock.Carrier →L[ℝ] ℂ := by
    simpa only [] using! ke01_complexInner
  let CZ := ‖E‖*8*Z*(1+B)
  let CX := ‖E‖*8*X*B
  let C1 := ‖I‖*8*(1+A)*CZ
  let C2 := ‖I‖*8*A*CX
  have hCZ : 0 ≤ CZ := by dsimp [CZ]; positivity
  have hCX : 0 ≤ CX := by dsimp [CX]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  refine ⟨C1+C2+1,by positivity,?_⟩
  intro e he g hg hs k hk x
  let Hq := fun y : Fin 9 → ℝ => auxiliaryGroundSourceVector e (kernelCoordinateBlock 1 y) he g hg hs
  let Hr := fun y : Fin 9 → ℝ => auxiliaryGroundSourceVector e (kernelCoordinateBlock 2 y) he g hg hs
  let Uq := fun y : Fin 9 → ℝ => GW.Fock.vacuum-Hq y
  let Ur := fun y : Fin 9 → ℝ => GW.Fock.vacuum-Hr y
  let RZ := fun y : Fin 9 → ℝ => auxiliaryExtendedResolvent 0 e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm (kernelSumCoordinates y)) he g hg hs
  let RX := fun y : Fin 9 → ℝ => auxiliaryExtendedResolvent 2 e
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm (kernelNegativeCoordinates y)) he g hg hs
  have hHq : ContDiff ℝ 3 Hq := (auxiliaryGroundSourceVector_contDiff g e he hg hs).comp (kernelCoordinateBlock 1).contDiff
  have hHr : ContDiff ℝ 3 Hr := (auxiliaryGroundSourceVector_contDiff g e he hg hs).comp (kernelCoordinateBlock 2).contDiff
  have hUq : ContDiff ℝ 3 Uq := contDiff_const.sub hHq
  have hUr : ContDiff ℝ 3 Ur := contDiff_const.sub hHr
  have hRZ : ContDiff ℝ 3 RZ := by
    simpa only [RZ,Function.comp_def] using!
      (auxiliaryExtendedResolvent_contDiff 0 e (by norm_num) he g hg hs).comp
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp kernelSumCoordinates.contDiff)
  have hRX : ContDiff ℝ 3 RX := by
    simpa only [RX,Function.comp_def] using!
      (auxiliaryExtendedResolvent_contDiff 2 e (by norm_num) he g hg hs).comp
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp kernelNegativeCoordinates.contDiff)
  have hQ (i : ℕ) (hi : i ≤ 3) (y : Fin 9 → ℝ) : ‖iteratedFDeriv ℝ i Hq y‖ ≤ A := by
    have h := hAB g e he hg hs i hi y
    have ht : A*|g| ≤ A := by nlinarith
    have hN : ‖iteratedFDeriv ℝ i Hq y‖ ≤ A*|g| := by
      simpa only [Hq,kernelCoordinateBlock_eq] using! h
    exact hN.trans ht
  have hR (i : ℕ) (hi : i ≤ 3) (y : Fin 9 → ℝ) : ‖iteratedFDeriv ℝ i Hr y‖ ≤ B := by
    have h := hBB g e he hg hs i hi y
    have ht : B*|g| ≤ B := by nlinarith
    have hN : ‖iteratedFDeriv ℝ i Hr y‖ ≤ B*|g| := by
      simpa only [Hr,kernelCoordinateBlock_eq] using! h
    exact hN.trans ht
  have hUQ := ke01_vacuum_sub_bound Hq hHq A hQ
  have hUR := ke01_vacuum_sub_bound Hr hHr B hR
  have hZE := (E.contDiff.comp hRZ).clm_apply hUr
  have hXE := (E.contDiff.comp hRX).clm_apply hHr
  have hZEb (i : ℕ) (hi : i ≤ 3) (y : Fin 9 → ℝ) :
      ‖iteratedFDeriv ℝ i (fun z => E (RZ z) (Ur z)) y‖ ≤ CZ :=
    ke01_bilinear_native_bound E RZ Ur hRZ hUr Z (1+B) hZ.le (by positivity)
      (fun j hj z => hZB 0 e (by norm_num) he g hg hs j hj z) hUR i hi y
  have hXEb (i : ℕ) (hi : i ≤ 3) (y : Fin 9 → ℝ) :
      ‖iteratedFDeriv ℝ i (fun z => E (RX z) (Hr z)) y‖ ≤ CX :=
    ke01_bilinear_native_bound E RX Hr hRX hHr X B hX.le hB.le
      (fun j hj z => hXB 2 e (by norm_num) he g hg hs j hj z) hR i hi y
  have h1 := ke01_bilinear_native_bound I Uq (fun y => E (RZ y) (Ur y)) hUq hZE
    (1+A) CZ (by positivity) hCZ hUQ hZEb k hk x
  have h2 := ke01_bilinear_native_bound I Hq (fun y => E (RX y) (Hr y)) hHq hXE
    A CX hA.le hCX hQ hXEb k hk x
  have hf : thresholdKernelJCoordinates e he g hg hs =
      (fun y => I (Uq y) (E (RZ y) (Ur y)))+(fun y => I (Hq y) (E (RX y) (Hr y))) := by
    funext y
    simp only [thresholdKernelJCoordinates,thresholdKernelJ,Pi.add_apply,I,E,
      ke01_complexInner_apply,IsBoundedBilinearMap.toContinuousLinearMap_apply,
      RZ,RX,Uq,Ur,Hq,Hr,kernelSumCoordinates_physical,kernelNegativeCoordinates_physical,auxiliaryZ,auxiliaryX]
    rfl
  have hOne : ContDiff ℝ k (fun y => I (Uq y) (E (RZ y) (Ur y))) := by
    simpa only [Function.comp_def] using!
      (((I.contDiff.comp hUq).clm_apply hZE).of_le (by exact_mod_cast hk))
  have hTwo : ContDiff ℝ k (fun y => I (Hq y) (E (RX y) (Hr y))) := by
    simpa only [Function.comp_def] using!
      (((I.contDiff.comp hHq).clm_apply hXE).of_le (by exact_mod_cast hk))
  have hAdd := iteratedFDeriv_add_apply (x := x) hOne.contDiffAt hTwo.contDiffAt
  rw [hf,hAdd]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_add_of_nonneg_right zero_le_one))

end Froehlich
