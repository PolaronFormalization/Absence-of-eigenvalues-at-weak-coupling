import GW.Conventions
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! FC08: actual L² fields acted on by bounded operator families.
Second countability belongs to the momentum domain, never to the operator space. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Froehlich
section OperatorFields
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem continuousOperatorField_stronglyMeasurable (K : Set GW.Space)
    (T : GW.Space → V →L[ℂ] W) (hT : ContinuousOn T K)
    (F : Lp V 2 (volume.restrict K)) :
    StronglyMeasurable (fun k : K => T k (F k)) := by
  have hTc : Continuous (fun k : K => T k) :=
    continuousOn_iff_continuous_domRestrict.mp hT
  have hTs := hTc.stronglyMeasurable
  have hFs : StronglyMeasurable (fun k : K => F (k : GW.Space)) :=
    (Lp.stronglyMeasurable F).comp_measurable measurable_subtype_coe
  exact (ContinuousLinearMap.id ℂ (V →L[ℂ] W)).continuous₂.comp_stronglyMeasurable
    (hTs.prodMk hFs)

theorem operatorField_memLp (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : AEStronglyMeasurable T (volume.restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (F : Lp V 2 (volume.restrict K)) :
    MemLp (fun k => T k (F k)) 2 (volume.restrict K) := by
  have hm := (ContinuousLinearMap.id ℂ (V →L[ℂ] W)).aestronglyMeasurable_comp₂
    hT (Lp.memLp F).aestronglyMeasurable
  apply (Lp.memLp F).of_le_mul hm
  filter_upwards [self_mem_ae_restrict hK] with k hk
  exact ((T k).le_opNorm (F k)).trans
    (mul_le_mul_of_nonneg_right (hM k hk) (norm_nonneg _))

def operatorFieldValue (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : AEStronglyMeasurable T (volume.restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (F : Lp V 2 (volume.restrict K)) :
    Lp W 2 (volume.restrict K) :=
  (operatorField_memLp K hK T hT M hM F).toLp _

theorem operatorFieldValue_ae (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : AEStronglyMeasurable T (volume.restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (F : Lp V 2 (volume.restrict K)) :
    operatorFieldValue K hK T hT M hM F =ᵐ[volume.restrict K] (fun k => T k (F k)) :=
  (operatorField_memLp K hK T hT M hM F).coeFn_toLp

/-- This source norm bound retains the empty-set case even when M is negative. -/
theorem operatorFieldValue_norm (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : AEStronglyMeasurable T (volume.restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (F : Lp V 2 (volume.restrict K)) :
    ‖operatorFieldValue K hK T hT M hM F‖ ≤ M * ‖F‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [operatorFieldValue_ae K hK T hT M hM F,
    self_mem_ae_restrict hK] with k hk hmem
  rw [hk]
  exact ((T k).le_opNorm (F k)).trans
    (mul_le_mul_of_nonneg_right (hM k hmem) (norm_nonneg _))

theorem operatorFieldValue_representative (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : AEStronglyMeasurable T (volume.restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (F : Lp V 2 (volume.restrict K))
    (f : GW.Space → V) (hf : (F : GW.Space → V) =ᵐ[volume.restrict K] f) :
    operatorFieldValue K hK T hT M hM F =ᵐ[volume.restrict K] (fun k => T k (f k)) :=
  (operatorFieldValue_ae K hK T hT M hM F).trans
    (hf.mono (fun k hk => congrArg (T k) hk))

def operatorFieldLinear (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : AEStronglyMeasurable T (volume.restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) :
    Lp V 2 (volume.restrict K) →ₗ[ℂ] Lp W 2 (volume.restrict K) where
  toFun := operatorFieldValue K hK T hT M hM
  map_add' F G := by
    apply Lp.ext
    filter_upwards [operatorFieldValue_ae K hK T hT M hM (F+G),
      operatorFieldValue_ae K hK T hT M hM F, operatorFieldValue_ae K hK T hT M hM G,
      Lp.coeFn_add F G,
      Lp.coeFn_add (operatorFieldValue K hK T hT M hM F) (operatorFieldValue K hK T hT M hM G)]
      with k hs hf hg hin hout
    simp only [Pi.add_apply] at hin hout
    rw [hs, hin, hout, map_add, ← hf, ← hg]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [operatorFieldValue_ae K hK T hT M hM (c • F),
      operatorFieldValue_ae K hK T hT M hM F, Lp.coeFn_smul c F,
      Lp.coeFn_smul c (operatorFieldValue K hK T hT M hM F)] with k hs hf hin hout
    simp only [Pi.smul_apply] at hin hout
    simp only [RingHom.id_apply]
    rw [hs, hin, hout, map_smul, ← hf]

def operatorFieldAction (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : AEStronglyMeasurable T (volume.restrict K))
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) :
    Lp V 2 (volume.restrict K) →L[ℂ] Lp W 2 (volume.restrict K) :=
  (operatorFieldLinear K hK T hT M hM).mkContinuous M
    (operatorFieldValue_norm K hK T hT M hM)

def continuousOperatorFieldAction (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : ContinuousOn T K)
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) :
    Lp V 2 (volume.restrict K) →L[ℂ] Lp W 2 (volume.restrict K) :=
  operatorFieldAction K hK T (hT.aestronglyMeasurable hK) M hM

theorem continuousOperatorFieldAction_ae (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : ContinuousOn T K)
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (F : Lp V 2 (volume.restrict K)) :
    continuousOperatorFieldAction K hK T hT M hM F =ᵐ[volume.restrict K] (fun k => T k (F k)) :=
  operatorFieldValue_ae K hK T (hT.aestronglyMeasurable hK) M hM F

theorem continuousOperatorFieldAction_norm (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : ContinuousOn T K)
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (F : Lp V 2 (volume.restrict K)) :
    ‖continuousOperatorFieldAction K hK T hT M hM F‖ ≤ M * ‖F‖ := by
  change ‖operatorFieldValue K hK T (hT.aestronglyMeasurable hK) M hM F‖ ≤ M * ‖F‖
  exact operatorFieldValue_norm K hK T (hT.aestronglyMeasurable hK) M hM F

theorem continuousOperatorFieldAction_representative (K : Set GW.Space) (hK : MeasurableSet K)
    (T : GW.Space → V →L[ℂ] W) (hT : ContinuousOn T K)
    (M : ℝ) (hM : ∀ k ∈ K, ‖T k‖ ≤ M) (F : Lp V 2 (volume.restrict K))
    (f : GW.Space → V) (hf : (F : GW.Space → V) =ᵐ[volume.restrict K] f) :
    continuousOperatorFieldAction K hK T hT M hM F =ᵐ[volume.restrict K] (fun k => T k (f k)) :=
  operatorFieldValue_representative K hK T (hT.aestronglyMeasurable hK) M hM F f hf

section Limits
variable {ι : Type*} (l : Filter ι) [NeBot l] [IsCountablyGenerated l]

theorem limitOperatorFamily_aestronglyMeasurable (K : Set GW.Space) (hK : MeasurableSet K)
    (T : ι → GW.Space → V →L[ℂ] W) (S : GW.Space → V →L[ℂ] W)
    (hT : ∀ i, ContinuousOn (T i) K)
    (hlim : ∀ k ∈ K, Tendsto (fun i => T i k) l (𝓝 (S k))) :
    AEStronglyMeasurable S (volume.restrict K) := by
  apply aestronglyMeasurable_of_tendsto_ae l (f := T)
  · intro i
    exact (hT i).aestronglyMeasurable hK
  · filter_upwards [self_mem_ae_restrict hK] with k hk
    exact hlim k hk

theorem limitOperatorField_stronglyMeasurable (K : Set GW.Space)
    (T : ι → GW.Space → V →L[ℂ] W) (S : GW.Space → V →L[ℂ] W)
    (hT : ∀ i, ContinuousOn (T i) K)
    (hlim : ∀ k ∈ K, Tendsto (fun i => T i k) l (𝓝 (S k)))
    (F : Lp V 2 (volume.restrict K)) :
    StronglyMeasurable (fun k : K => S k (F k)) := by
  have hs : StronglyMeasurable (fun k : K => S k) := by
    apply stronglyMeasurable_of_tendsto l (f := fun i (k : K) => T i k)
    · intro i
      exact (continuousOn_iff_continuous_domRestrict.mp (hT i)).stronglyMeasurable
    · exact tendsto_pi_nhds.mpr (fun k : K => hlim k k.property)
  have hF : StronglyMeasurable (fun k : K => F (k : GW.Space)) :=
    (Lp.stronglyMeasurable F).comp_measurable measurable_subtype_coe
  exact (ContinuousLinearMap.id ℂ (V →L[ℂ] W)).continuous₂.comp_stronglyMeasurable
    (hs.prodMk hF)

theorem limitOperatorFamily_bound (K : Set GW.Space)
    (T : ι → GW.Space → V →L[ℂ] W) (S : GW.Space → V →L[ℂ] W)
    (hlim : ∀ k ∈ K, Tendsto (fun i => T i k) l (𝓝 (S k)))
    (M : ℝ) (hM : ∀ i, ∀ k ∈ K, ‖T i k‖ ≤ M) :
    ∀ k ∈ K, ‖S k‖ ≤ M := by
  intro k hk
  exact le_of_tendsto (hlim k hk).norm (Eventually.of_forall (fun i => hM i k hk))

/-- The same class construction for pointwise operator-norm limits; both natural
sequences and the real ultraviolet-cutoff filter are supported. -/
def limitOperatorFieldAction (K : Set GW.Space) (hK : MeasurableSet K)
    (T : ι → GW.Space → V →L[ℂ] W) (S : GW.Space → V →L[ℂ] W)
    (hT : ∀ i, ContinuousOn (T i) K)
    (hlim : ∀ k ∈ K, Tendsto (fun i => T i k) l (𝓝 (S k)))
    (M : ℝ) (hM : ∀ i, ∀ k ∈ K, ‖T i k‖ ≤ M) :
    Lp V 2 (volume.restrict K) →L[ℂ] Lp W 2 (volume.restrict K) :=
  operatorFieldAction K hK S (limitOperatorFamily_aestronglyMeasurable l K hK T S hT hlim)
    M (limitOperatorFamily_bound l K T S hlim M hM)

theorem limitOperatorFieldAction_ae (K : Set GW.Space) (hK : MeasurableSet K)
    (T : ι → GW.Space → V →L[ℂ] W) (S : GW.Space → V →L[ℂ] W)
    (hT : ∀ i, ContinuousOn (T i) K)
    (hlim : ∀ k ∈ K, Tendsto (fun i => T i k) l (𝓝 (S k)))
    (M : ℝ) (hM : ∀ i, ∀ k ∈ K, ‖T i k‖ ≤ M) (F : Lp V 2 (volume.restrict K)) :
    limitOperatorFieldAction l K hK T S hT hlim M hM F =ᵐ[volume.restrict K] (fun k => S k (F k)) :=
  operatorFieldValue_ae K hK S (limitOperatorFamily_aestronglyMeasurable l K hK T S hT hlim)
    M (limitOperatorFamily_bound l K T S hlim M hM) F

theorem limitOperatorFieldAction_norm (K : Set GW.Space) (hK : MeasurableSet K)
    (T : ι → GW.Space → V →L[ℂ] W) (S : GW.Space → V →L[ℂ] W)
    (hT : ∀ i, ContinuousOn (T i) K)
    (hlim : ∀ k ∈ K, Tendsto (fun i => T i k) l (𝓝 (S k)))
    (M : ℝ) (hM : ∀ i, ∀ k ∈ K, ‖T i k‖ ≤ M) (F : Lp V 2 (volume.restrict K)) :
    ‖limitOperatorFieldAction l K hK T S hT hlim M hM F‖ ≤ M * ‖F‖ := by
  change ‖operatorFieldValue K hK S
    (limitOperatorFamily_aestronglyMeasurable l K hK T S hT hlim)
      M (limitOperatorFamily_bound l K T S hlim M hM) F‖ ≤ M * ‖F‖
  exact operatorFieldValue_norm K hK S
    (limitOperatorFamily_aestronglyMeasurable l K hK T S hT hlim)
      M (limitOperatorFamily_bound l K T S hlim M hM) F

theorem limitOperatorFieldAction_representative (K : Set GW.Space) (hK : MeasurableSet K)
    (T : ι → GW.Space → V →L[ℂ] W) (S : GW.Space → V →L[ℂ] W)
    (hT : ∀ i, ContinuousOn (T i) K)
    (hlim : ∀ k ∈ K, Tendsto (fun i => T i k) l (𝓝 (S k)))
    (M : ℝ) (hM : ∀ i, ∀ k ∈ K, ‖T i k‖ ≤ M) (F : Lp V 2 (volume.restrict K))
    (f : GW.Space → V) (hf : (F : GW.Space → V) =ᵐ[volume.restrict K] f) :
    limitOperatorFieldAction l K hK T S hT hlim M hM F =ᵐ[volume.restrict K] (fun k => S k (f k)) :=
  operatorFieldValue_representative K hK S
    (limitOperatorFamily_aestronglyMeasurable l K hK T S hT hlim)
      M (limitOperatorFamily_bound l K T S hlim M hM) F f hf

end Limits

end OperatorFields
end Froehlich
