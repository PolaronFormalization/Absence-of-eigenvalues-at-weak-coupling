import Froehlich.Nodes.RS02InverseSmooth
import Froehlich.Nodes.PT03KernelDefinitions

set_option autoImplicit false
noncomputable section
namespace Froehlich
open scoped BoundedEndReal

local instance ke01ExtendHighGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n) :=
  Submodule.normedAddCommGroup (HighSectorSpace n)
local instance ke01ExtendEndGroup (n : ℕ) : NormedAddCommGroup (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ke01ExtendEndReal (n : ℕ) : NormedSpace ℝ (HighSectorSpace n →L[ℂ] HighSectorSpace n) :=
  (BoundedEndReal.realNormedAlgebra (E := HighSectorSpace n)).toNormedSpace
local instance ke01ExtendFockEndGroup : NormedAddCommGroup (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ke01ExtendFockEndReal : NormedSpace ℝ (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  (BoundedEndReal.realNormedAlgebra (E := GW.Fock.Carrier)).toNormedSpace

/-- Actual zero extension is a bounded real-linear map of operator carriers. -/
def ke01_extendEnd (n : ℕ) :
    (HighSectorSpace n →L[ℂ] HighSectorSpace n) →L[ℝ]
      (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) where
  toFun T := (HighSectorSpace n).subtypeL.comp (T.comp (highSectorProject n))
  map_add' T S := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  map_smul' c T := by
    apply ContinuousLinearMap.ext
    intro x
    rfl
  cont := (continuous_id.clm_comp_const (highSectorProject n)).const_clm_comp
    (HighSectorSpace n).subtypeL

theorem auxiliaryExtendedResolvent_contDiff (n : ℕ) (e : ℝ) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2) :
    ContDiff ℝ 3 (fun p : GW.Space => auxiliaryExtendedResolvent n e p he g hg hs) := by
  have hR : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryResolvent n e p he g hg hs) := by
    simpa only [] using! auxiliaryResolvent_contDiff g n e hn he hg hs
  simpa only [Function.comp_def,ke01_extendEnd,auxiliaryExtendedResolvent] using!
    (ke01_extendEnd n).contDiff.comp hR

end Froehlich
