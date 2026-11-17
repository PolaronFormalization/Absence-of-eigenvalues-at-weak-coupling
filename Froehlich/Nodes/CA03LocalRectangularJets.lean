import Froehlich.Nodes.CA03Local
import Froehlich.Nodes.GW01
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
namespace Froehlich

/-- The actual closed momentum slab; the other two variables are unrestricted. -/
def rectangularMomentumSlab : Set (GW.Space × (GW.Space × GW.Space)) :=
  {t | ‖t.1‖ ≤ (1/4 : ℝ)}

theorem rectangularMomentumSlab_convex : Convex ℝ rectangularMomentumSlab := by
  have h := (convex_closedBall (0 : GW.Space) (1/4 : ℝ)).linear_preimage
    (ContinuousLinearMap.fst ℝ GW.Space (GW.Space × GW.Space)).toLinearMap
  change Convex ℝ {t : GW.Space × (GW.Space × GW.Space) | dist t.1 0 ≤ (1/4 : ℝ)} at h
  simpa only [rectangularMomentumSlab,dist_zero_right] using h

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The first, untruncated momentum increment of every native jet through
order two. Only ordinary regularity on the true closed slab is used. -/
theorem norm_rectangularMomentum_jet_sub
    (F : (GW.Space × (GW.Space × GW.Space)) → V) (M : ℝ)
    (hF : ∀ t ∈ rectangularMomentumSlab, ContDiffAt ℝ 3 F t)
    (hB : ∀ k ≤ 3, ∀ t ∈ rectangularMomentumSlab,
      ‖iteratedFDeriv ℝ k F t‖ ≤ M)
    (n : ℕ) (hn : n ≤ 2) (P q r : GW.Space) (hP : ‖P‖ ≤ 1/4) :
    ‖iteratedFDeriv ℝ n F (P,(q,r))-iteratedFDeriv ℝ n F (0,(q,r))‖ ≤ M*‖P‖ := by
  have hd (t) (ht : t ∈ rectangularMomentumSlab) :
      DifferentiableAt ℝ (iteratedFDeriv ℝ n F) t :=
    ((hF t ht).iteratedFDeriv_right (m := 1) (by exact_mod_cast (show 1+n ≤ 3 by omega))).differentiableAt (by norm_num)
  have hb (t) (ht : t ∈ rectangularMomentumSlab) :
      ‖fderiv ℝ (iteratedFDeriv ℝ n F) t‖ ≤ M := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hB (n+1) (by omega) t ht
  have hx : (0,(q,r)) ∈ rectangularMomentumSlab := by
    change ‖(0 : GW.Space)‖ ≤ (1/4 : ℝ)
    norm_num
  have hy : (P,(q,r)) ∈ rectangularMomentumSlab := hP
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hd hb
    rectangularMomentumSlab_convex hx hy
  simpa only [Prod.mk_sub_mk,sub_zero,sub_self,Prod.norm_def,norm_zero,
    max_self,max_eq_left (norm_nonneg P)] using h

end Froehlich
