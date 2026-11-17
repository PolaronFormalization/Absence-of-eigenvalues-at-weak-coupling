import GW.Fock.FockAmplification
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Sequences

/-! GW02's section statement for the retained product unitary.
The norm-limit argument uses compatible subsequences of the supplied simple approximants;
it does not construct another currying map. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace Froehlich
section ProductSections
variable {Y Z E : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure Y) (ν : Measure Z) [SigmaFinite μ] [SigmaFinite ν]

/-- The section identity is stable under the norm limits used in GW's product construction.
The inner a.e. subsequence may depend on `y`; no diagonal substitution is used. -/
theorem product_sections_of_norm_limit
    (f : ℕ → Lp (Lp E 2 ν) 2 μ) (u : Lp (Lp E 2 ν) 2 μ)
    (hf : Tendsto f atTop (𝓝 u))
    (hs : ∀ n, ∀ᵐ y ∂μ,
      (fun z => GW.Fock.productUnitary μ ν (f n) (y,z)) =ᵐ[ν] (f n y)) :
    ∀ᵐ y ∂μ, (fun z => GW.Fock.productUnitary μ ν u (y,z)) =ᵐ[ν] (u y) := by
  have hp : Tendsto (fun n => GW.Fock.productUnitary μ ν (f n)) atTop
      (𝓝 (GW.Fock.productUnitary μ ν u)) :=
    ((GW.Fock.productUnitary (E := E) μ ν).continuous.tendsto u).comp hf
  obtain ⟨a, ha, hpa⟩ := (tendstoInMeasure_of_tendsto_Lp hp).exists_seq_tendsto_ae
  obtain ⟨b, hb, hba⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hf.comp ha.tendsto_atTop)).exists_seq_tendsto_ae
  have hsections := Measure.ae_ae_of_ae_prod hpa
  have hsall := ae_all_iff.mpr hs
  filter_upwards [hsections, hba, hsall] with y hpy hby hsy
  obtain ⟨c, hc, hcy⟩ := (tendstoInMeasure_of_tendsto_Lp hby).exists_seq_tendsto_ae
  filter_upwards [hpy, hcy, ae_all_iff.mpr hsy] with z hpz hcz hsz
  have hpbc := (hpz.comp hb.tendsto_atTop).comp hc.tendsto_atTop
  apply tendsto_nhds_unique _ hcz
  exact hpbc.congr' (Eventually.of_forall (fun i => hsz (a (b (c i)))))

theorem product_sections_simple (s : Lp.simpleFunc (Lp E 2 ν) 2 μ) :
    ∀ᵐ y ∂μ, (fun z => GW.Fock.productUnitary μ ν (s : Lp (Lp E 2 ν) 2 μ) (y,z)) =ᵐ[ν]
      (s : Lp (Lp E 2 ν) 2 μ) y := by
  have hp := GW.Fock.simpleProductClass_ae μ ν (Lp.simpleFunc.toSimpleFunc s)
    (Lp.simpleFunc.memLp s)
  have he : GW.Fock.productUnitary μ ν (s : Lp (Lp E 2 ν) 2 μ) =
      GW.Fock.simpleProductClass μ ν (Lp.simpleFunc.toSimpleFunc s) (Lp.simpleFunc.memLp s) :=
    GW.Fock.productIsometry_simple μ ν s
  rw [he]
  filter_upwards [Measure.ae_ae_of_ae_prod hp, Lp.simpleFunc.toSimpleFunc_eq_toFun s] with y hy hs
  filter_upwards [hy] with z hz
  exact hz.trans (congrArg (fun q : Lp E 2 ν => q z) hs)

/-- The arbitrary-class section identity for the existing GW product unitary. -/
theorem productUnitary_sections (u : Lp (Lp E 2 ν) 2 μ) :
    ∀ᵐ y ∂μ, (fun z => GW.Fock.productUnitary μ ν u (y,z)) =ᵐ[ν] (u y) := by
  obtain ⟨f, hfmem, hflim⟩ := mem_closure_iff_seq_limit.mp
    (GW.Fock.simpleInclusion_dense (E := E) μ ν u)
  choose s hs using hfmem
  apply product_sections_of_norm_limit μ ν f u hflim
  intro n
  rw [← hs n]
  exact product_sections_simple μ ν (s n)

end ProductSections
end Froehlich
