import Froehlich.Nodes.KE01InputUniform
import Froehlich.Nodes.KE01ExtendedRegularity
import Froehlich.Nodes.KE01CanonicalNorm
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
noncomputable section
namespace Froehlich
open scoped BoundedEndReal
local instance ke01NativeFockReal : NormedSpace ℝ GW.Fock.Carrier := NormedSpace.restrictScalars ℝ ℂ _
local instance ke01NativeHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ke01NativeEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ke01NativeEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance ke01NativeFockEndGroup : NormedAddCommGroup (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ke01NativeFockEndReal : NormedSpace ℝ (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  (BoundedEndReal.realNormedAlgebra (E := GW.Fock.Carrier)).toNormedSpace

local instance ke01NativeEndBounded (n : ℕ) : IsBoundedSMul ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  NormedSpace.toIsBoundedSMul
local instance ke01NativeFockEndBounded : IsBoundedSMul ℝ (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  NormedSpace.toIsBoundedSMul
local instance ke01NativeExtensionGroup (n : ℕ) : NormedAddCommGroup
    ((HighSectorSpace n →L[ℂ] HighSectorSpace n) →L[ℝ] (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Expected-type normalization of the existing zero-extension map. -/
private def ke01_nativeExtension (n : ℕ) :
    (HighSectorSpace n →L[ℂ] HighSectorSpace n) →L[ℝ] (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) := by
  simpa only [] using! ke01_extendEnd n

private theorem ke01_three_pow_le (k : ℕ) (hk : k ≤ 3) : (3 : ℝ)^k ≤ 27 := by
  interval_cases k <;> norm_num

theorem ke01_groundSource_native_common : ∃ C : ℝ, 0 < C ∧
    ∀ (g e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (hg : |g| ≤ 1)
      (hs : auxiliaryResolventConstant*|g| ≤ 1/2) (k : ℕ) (hk : k ≤ 3) (q : Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ k
        (fun t => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C*|g| := by
  obtain ⟨C,hC,hB⟩ := ke01_groundSource_derivatives_common
  refine ⟨27*C,by positivity,?_⟩
  intro g e he hg hs k hk q
  let F := fun t : Fin 3 → ℝ => auxiliaryGroundSourceVector e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs
  have hF : ContDiff ℝ 3 F := by
    simpa only [F,Function.comp_def] using!
      (auxiliaryGroundSourceVector_contDiff g e he hg hs).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hN := iteratedFDeriv_norm_le_canonical k F (hF.of_le (by exact_mod_cast hk))
    (C*|g|) (mul_nonneg hC.le (abs_nonneg g)) q (fun a ha => hB g e he hg hs a (by omega) q)
  have hMul := mul_le_mul_of_nonneg_right (ke01_three_pow_le k hk) (mul_nonneg hC.le (abs_nonneg g))
  exact hN.trans (by simpa only [mul_assoc,Nat.cast_ofNat] using! hMul)

theorem ke01_extendedResolvent_native_common : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (e : ℝ) (hn : n ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
      (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
      (k : ℕ) (hk : k ≤ 3) (q : Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ k
        (fun t => auxiliaryExtendedResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := ke01_resolvent_derivatives_common
  let M := 1+‖ke01_nativeExtension 0‖+‖ke01_nativeExtension 1‖+‖ke01_nativeExtension 2‖
  have hM : 0 < M := by dsimp [M]; positivity
  have hMn (n : ℕ) (hn : n ≤ 2) : ‖ke01_nativeExtension n‖ ≤ M := by
    interval_cases n <;> dsimp [M] <;> nlinarith [norm_nonneg (ke01_nativeExtension 0),norm_nonneg (ke01_nativeExtension 1),norm_nonneg (ke01_nativeExtension 2)]
  refine ⟨M*(27*C),by positivity,?_⟩
  intro n e hn he g hg hs k hk q
  let F := fun t : Fin 3 → ℝ => auxiliaryResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs
  have hF : ContDiff ℝ 3 F := by
    simpa only [F,Function.comp_def] using!
      (auxiliaryResolvent_contDiff g n e hn he hg hs).comp (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  have hN := iteratedFDeriv_norm_le_canonical k F (hF.of_le (by exact_mod_cast hk)) C hC.le q
    (fun a ha => hB n e hn he g hg hs a (by omega) q)
  have hNF : ‖iteratedFDeriv ℝ k F q‖ ≤ 27*C :=
    hN.trans (mul_le_mul_of_nonneg_right (ke01_three_pow_le k hk) hC.le)
  have hpost := (ke01_nativeExtension n).norm_iteratedFDeriv_comp_left (x := q) hF.contDiffAt (by exact_mod_cast hk)
  have hpost' : ‖iteratedFDeriv ℝ k
      (fun t => auxiliaryExtendedResolvent n e ((EuclideanSpace.equiv (Fin 3) ℝ).symm t) he g hg hs) q‖ ≤
      ‖ke01_nativeExtension n‖*‖iteratedFDeriv ℝ k F q‖ := by
    simpa only [Function.comp_def,ke01_nativeExtension,ke01_extendEnd,auxiliaryExtendedResolvent,F] using! hpost
  exact hpost'.trans (mul_le_mul (hMn n hn) hNF (norm_nonneg _) hM.le)

end Froehlich
