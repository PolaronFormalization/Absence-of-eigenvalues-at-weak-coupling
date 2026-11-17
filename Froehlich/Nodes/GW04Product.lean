import GW.Fock.FockAmplification

/-! GW04's product-contraction adapters reuse the retained rectangle-density unitary. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

namespace Froehlich
section Contraction
variable {Y E F : Type*} [MeasurableSpace Y] (μ : Measure Y)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem contraction_natural (T : E →L[ℂ] F) (f : Lp ℂ 2 μ) (u : Lp E 2 μ) :
    T (GW.Fock.contraction μ f u) = GW.Fock.contraction μ f (GW.Fock.amplify μ T u) := by
  change T (∫ y, (starRingEnd ℂ) (f y) • u y ∂μ) =
    ∫ y, (starRingEnd ℂ) (f y) • GW.Fock.amplify μ T u y ∂μ
  rw [← T.integral_comp_comm (GW.Fock.contraction_integrable μ f u)]
  apply integral_congr_ae
  filter_upwards [GW.Fock.amplify_ae μ T u] with y hy
  rw [hy, map_smul]

theorem contraction_tensor (f g : Lp ℂ 2 μ) (w : E) :
    GW.Fock.contraction μ f (GW.Fock.tensorEmbedding μ g w) = ⟪f,g⟫_ℂ • w := by
  change (∫ y, (starRingEnd ℂ) (f y) • GW.Fock.tensorEmbedding μ g w y ∂μ) = _
  calc
    _ = ∫ y, ((starRingEnd ℂ) (f y) * g y) • w ∂μ := by
      apply integral_congr_ae
      filter_upwards [GW.Fock.tensorEmbedding_ae μ g w] with y hy
      rw [hy, smul_smul]
    _ = (∫ y, (starRingEnd ℂ) (f y) * g y ∂μ) • w := integral_smul_const _ _
    _ = ⟪f,g⟫_ℂ • w := by
      congr 1
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by simp only [RCLike.inner_apply]; ring)

theorem contraction_scalar (f g : Lp ℂ 2 μ) : GW.Fock.contraction μ f g = ⟪f,g⟫_ℂ := by
  change (∫ y, (starRingEnd ℂ) (f y) • g y ∂μ) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by simp only [smul_eq_mul, RCLike.inner_apply]; ring)

theorem tensorEmbedding_scalar (g : Lp ℂ 2 μ) (c : ℂ) :
    GW.Fock.tensorEmbedding μ g c = c • g := by
  apply Lp.ext
  filter_upwards [GW.Fock.tensorEmbedding_ae μ g c, Lp.coeFn_smul c g] with y hy hc
  rw [hy, hc]
  change g y * c = c * g y
  ring
end Contraction

section SwapContraction
variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
  (μ : Measure Y) (ν : Measure Z) [SigmaFinite μ] [SigmaFinite ν]

theorem swapProduct_productFunction (g : Lp ℂ 2 μ) (w : Lp ℂ 2 ν) :
    GW.Fock.swapProduct μ ν (GW.Fock.productFunction μ ν g w) =
      GW.Fock.productFunction ν μ w g := by
  have hswap : MeasurePreserving (Prod.swap : Z × Y → Y × Z) (ν.prod μ) (μ.prod ν) :=
    Measure.measurePreserving_swap
  apply Lp.ext
  filter_upwards [GW.Fock.swapProduct_ae μ ν (GW.Fock.productFunction μ ν g w),
    hswap.quasiMeasurePreserving.ae (GW.Fock.productFunction_ae μ ν g w),
    GW.Fock.productFunction_ae ν μ w g] with p hp hg hw
  rw [hp, hg, hw]
  change g p.2 * w p.1 = w p.1 * g p.2
  ring

/-- Outer contraction of the curried scalar product equals the retained spectator
contraction after exchanging coordinates. All maps act on actual L² classes. -/
theorem contraction_inverseProduct_swap (f : Lp ℂ 2 μ) (v : Lp ℂ 2 (μ.prod ν)) :
    GW.Fock.contraction μ f ((GW.Fock.productUnitary μ ν).symm v) =
      GW.Fock.spectatorContraction ν μ f (GW.Fock.swapProduct μ ν v) := by
  let U := GW.Fock.productUnitary (E := ℂ) μ ν
  let A : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 ν :=
    (GW.Fock.contraction μ f).comp U.symm.toLinearIsometry.toContinuousLinearMap
  let B : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 ν :=
    (GW.Fock.spectatorContraction ν μ f).comp
      (GW.Fock.swapProduct (E := ℂ) μ ν).toLinearIsometry.toContinuousLinearMap
  have hAB : A = B := by
    apply GW.Fock.product_map_ext μ ν
    intro S T hS hT hSf hTf c
    rw [← GW.Fock.productFunction_indicator μ ν S T hS hT hSf hTf c]
    let g := indicatorConstLp 2 hS hSf (1 : ℂ)
    let w := indicatorConstLp 2 hT hTf c
    change GW.Fock.contraction μ f (U.symm (GW.Fock.productFunction μ ν g w)) =
      GW.Fock.spectatorContraction ν μ f (GW.Fock.swapProduct μ ν (GW.Fock.productFunction μ ν g w))
    have hi : U.symm (GW.Fock.productFunction μ ν g w) = GW.Fock.tensorEmbedding μ g w := by
      apply U.injective
      rw [LinearIsometryEquiv.apply_symm_apply, GW.Fock.productUnitary_tensor]
    rw [hi, contraction_tensor, swapProduct_productFunction,
      GW.Fock.spectatorContraction_productFunction, contraction_scalar, tensorEmbedding_scalar]
  exact congrArg (fun T => T v) hAB

end SwapContraction
end Froehlich
