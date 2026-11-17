import Froehlich.Nodes.KE01ExtendedRegularity
import Froehlich.Nodes.KE01Denominator
import Froehlich.Nodes.RS02SourceDerivativesComposition

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich
open scoped BoundedEndReal
local instance ke01JointFockReal : NormedSpace ℝ GW.Fock.Carrier := NormedSpace.restrictScalars ℝ ℂ _
local instance ke01JointFockModule : Module ℝ GW.Fock.Carrier := ke01JointFockReal.toModule
local instance ke01JointEndGroup : NormedAddCommGroup (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance ke01JointEndReal : NormedSpace ℝ (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) :=
  (BoundedEndReal.realNormedAlgebra (E := GW.Fock.Carrier)).toNormedSpace

/-- Real bilinearity of evaluation on the unchanged complex operator carrier. -/
theorem ke01_operatorEvaluation_bilinear : IsBoundedBilinearMap ℝ
    (fun u : (GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier) × GW.Fock.Carrier => u.1 u.2) where
  add_left T S x := rfl
  smul_left c T x := rfl
  add_right T x y := T.map_add x y
  smul_right c T x := (T.restrictScalars ℝ).map_smul c x
  bound := ⟨1,zero_lt_one,fun T x => by simpa only [one_mul] using T.le_opNorm x⟩

variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem thresholdKernelJ_contDiff :
    ContDiff ℝ 3 (fun t : GW.Space × (GW.Space × GW.Space) =>
      thresholdKernelJ e he g hg hs t.1 t.2.1 t.2.2) := by
  have hh : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryGroundSourceVector e p he g hg hs) := by
    simpa only [] using! auxiliaryGroundSourceVector_contDiff g e he hg hs
  have hz0 : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryZ e p he g hg hs) := by
    simpa only [] using! auxiliaryExtendedResolvent_contDiff 0 e (by norm_num) he g hg hs
  have hx0 : ContDiff ℝ 3 (fun p : GW.Space => auxiliaryExtendedResolvent 2 e p he g hg hs) := by
    simpa only [] using! auxiliaryExtendedResolvent_contDiff 2 e (by norm_num) he g hg hs
  have hq : ContDiff ℝ 3 (fun t : GW.Space × (GW.Space × GW.Space) => auxiliaryGroundSourceVector e t.2.1 he g hg hs) :=
    hh.comp (contDiff_fst.comp contDiff_snd)
  have hr : ContDiff ℝ 3 (fun t : GW.Space × (GW.Space × GW.Space) => auxiliaryGroundSourceVector e t.2.2 he g hg hs) :=
    hh.comp (contDiff_snd.comp contDiff_snd)
  have hz : ContDiff ℝ 3 (fun t : GW.Space × (GW.Space × GW.Space) => auxiliaryZ e (t.1+t.2.1+t.2.2) he g hg hs) :=
    hz0.comp ((contDiff_fst.add (contDiff_fst.comp contDiff_snd)).add (contDiff_snd.comp contDiff_snd))
  have hx : ContDiff ℝ 3 (fun t : GW.Space × (GW.Space × GW.Space) => auxiliaryX e he g hg hs t.1) := by
    exact (hx0.comp contDiff_neg).comp contDiff_fst
  have hv : ContDiff ℝ 3 (fun _ : GW.Space × (GW.Space × GW.Space) => GW.Fock.vacuum) := contDiff_const
  have hZ := ke01_operatorEvaluation_bilinear.contDiff.comp₂ hz (hv.sub hr)
  have hX := ke01_operatorEvaluation_bilinear.contDiff.comp₂ hx hr
  exact ((hv.sub hq).inner (𝕜 := ℂ) hZ).add (hq.inner (𝕜 := ℂ) hX)

theorem thresholdKernelC_contDiffAt (t : GW.Space × (GW.Space × GW.Space))
    (ht : ‖t.1‖ < 1/3) :
    ContDiffAt ℝ 3 (fun u : GW.Space × (GW.Space × GW.Space) =>
      thresholdKernelC e he g hg hs u.1 u.2.1 u.2.2) t := by
  exact (ke01_denominator_contDiffAt e he t ht).sub
    (thresholdKernelJ_contDiff e he g hg hs).contDiffAt

end Froehlich
