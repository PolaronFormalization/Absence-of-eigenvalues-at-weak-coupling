import Froehlich.Nodes.OP00KernelOperator

set_option autoImplicit false

/-! Fixed null sets are removed by a measurable null hull, without changing
any original row almost everywhere or the L2 majorant norm. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace Froehlich

def kernelNullHull (N : Set GW.Space) : Set GW.Space := toMeasurable volume N

def kernelCleanMajorant (N : Set GW.Space) (a : GW.Space → ℝ) (q : GW.Space) : ℝ :=
  if q ∈ kernelNullHull N then 0 else a q

def kernelCleanKernel (N : Set GW.Space) (k : GW.Space → GW.Space → ℂ)
    (q r : GW.Space) : ℂ :=
  if q ∈ kernelNullHull N ∨ r ∈ kernelNullHull N then 0 else k q r

theorem kernelNullHull_ae_compl (N : Set GW.Space) (hN : volume N = 0) :
    ∀ᵐ q ∂volume, q ∉ kernelNullHull N := by
  apply ae_iff.mpr
  simpa only [not_not,kernelNullHull,Set.setOf_mem_eq,measure_toMeasurable] using hN

theorem kernelCleanMajorant_ae (N : Set GW.Space) (hN : volume N = 0) (a : GW.Space → ℝ) :
    kernelCleanMajorant N a =ᵐ[volume] a := by
  filter_upwards [kernelNullHull_ae_compl N hN] with q hq
  simp only [kernelCleanMajorant,if_neg hq]

theorem kernelCleanMajorant_memLp (N : Set GW.Space) (hN : volume N = 0)
    (a : GW.Space → ℝ) (ha : MemLp a 2 volume) : MemLp (kernelCleanMajorant N a) 2 volume :=
  MemLp.ae_eq (kernelCleanMajorant_ae N hN a).symm ha

theorem kernelCleanMajorant_norm (N : Set GW.Space) (hN : volume N = 0)
    (a : GW.Space → ℝ) (ha : MemLp a 2 volume) :
    ‖(kernelCleanMajorant_memLp N hN a ha).toLp (kernelCleanMajorant N a)‖ = ‖ha.toLp a‖ := by
  rw [MemLp.toLp_congr _ _ (kernelCleanMajorant_ae N hN a)]

theorem kernelCleanMajorant_nonnegative (N : Set GW.Space) (a : GW.Space → ℝ)
    (ha0 : ∀ q, 0 ≤ a q) (q : GW.Space) : 0 ≤ kernelCleanMajorant N a q := by
  unfold kernelCleanMajorant
  split_ifs
  · exact le_rfl
  · exact ha0 q

theorem kernelCleanKernel_measurable (N : Set GW.Space) (k : GW.Space → GW.Space → ℂ)
    (hk : Measurable (Function.uncurry k)) : Measurable (Function.uncurry (kernelCleanKernel N k)) := by
  change Measurable (fun z : GW.Space × GW.Space =>
    if z.1 ∈ toMeasurable volume N ∨ z.2 ∈ toMeasurable volume N then (0 : ℂ) else k z.1 z.2)
  apply Measurable.ite
    (((measurableSet_toMeasurable volume N).preimage measurable_fst).union
      ((measurableSet_toMeasurable volume N).preimage measurable_snd)) measurable_const hk

theorem kernelCleanKernel_bound (N : Set GW.Space) (a : GW.Space → ℝ)
    (k : GW.Space → GW.Space → ℂ) (M : ℝ)
    (hb : ∀ q ∉ N, ∀ r ∉ N, ‖k q r‖ ≤ M*a q*a r) (q r : GW.Space) :
    ‖kernelCleanKernel N k q r‖ ≤ M*kernelCleanMajorant N a q*kernelCleanMajorant N a r := by
  by_cases hq : q ∈ kernelNullHull N
  · simp only [kernelCleanKernel,kernelCleanMajorant,if_pos hq,if_pos (Or.inl hq),mul_zero,zero_mul,norm_zero,le_refl]
  · by_cases hr : r ∈ kernelNullHull N
    · simp only [kernelCleanKernel,kernelCleanMajorant,if_pos hr,if_neg hq,if_pos (Or.inr hr),mul_zero,norm_zero,le_refl]
    · simp only [kernelCleanKernel,kernelCleanMajorant,if_neg hq,if_neg hr,if_neg (not_or.mpr ⟨hq,hr⟩)]
      exact hb q (fun h => hq (subset_toMeasurable volume N h)) r
        (fun h => hr (subset_toMeasurable volume N h))

theorem kernelCleanKernel_row_ae (N : Set GW.Space) (hN : volume N = 0)
    (k : GW.Space → GW.Space → ℂ) (f : GW.OnePhonon) :
    kernelRowIntegral (kernelCleanKernel N k) f =ᵐ[volume] kernelRowIntegral k f := by
  filter_upwards [kernelNullHull_ae_compl N hN] with q hq
  apply integral_congr_ae
  filter_upwards [kernelNullHull_ae_compl N hN] with r hr
  simp only [kernelCleanKernel,if_neg (not_or.mpr ⟨hq,hr⟩)]

theorem kernelNegativeMajorant_zero (a : GW.Space → ℝ) (k : GW.Space → GW.Space → ℂ)
    (M : ℝ) (hM : M < 0) (hb : ∀ q r, ‖k q r‖ ≤ M*a q*a r) : a = 0 := by
  funext q
  have h := (norm_nonneg (k q q)).trans (hb q q)
  have hs : a q^2 = 0 := by nlinarith [sq_nonneg (a q)]
  simpa only [Pi.zero_apply] using (sq_eq_zero_iff.mp hs)

end Froehlich
