import Froehlich.Nodes.UV02FreeInverse

/-! The bounded shifted reciprocal lands in the actual maximal free
operator domain, with the literal free-plus-scalar equation. -/
noncomputable section
open MeasureTheory Filter
namespace Froehlich
variable (P : GW.Space) (c : ℝ) (hc : 1 ≤ c)

theorem freeShiftInverse_free_graph (f : GW.Fock.Carrier) :
    (freeShiftInverse P c hc f, f-(c : ℂ) • freeShiftInverse P c hc f) ∈ (freeFiberOperator P).graph := by
  apply (freeFiberOperator_graph_ae_iff P _ _).mpr
  intro n
  let u := freeShiftInverse P c hc f
  have hweight := freeShiftInverse_weighted_ae P c hc f n
  have he : physicalSector n ((f-(c : ℂ) • u) n)=
      physicalSector n (f n)-(c : ℂ) • physicalSector n (u n) := by
    change physicalSector n (f n-(c : ℂ) • u n)=_
    rw [map_sub,map_smul]
  change (fun K => (freeSymbol P n K : ℂ) • physicalSector n (u n) K)
    =ᵐ[GW.Fock.sectorMeasure n] physicalSector n ((f-(c : ℂ) • u) n)
  rw [he]
  filter_upwards [hweight,Lp.coeFn_sub (physicalSector n (f n)) ((c : ℂ) • physicalSector n (u n)),
    Lp.coeFn_smul (c : ℂ) (physicalSector n (u n))] with K hw hsub hsmul
  change (freeSymbol P n K : ℂ)*physicalSector n (u n) K = _
  rw [hsub,Pi.sub_apply,hsmul,Pi.smul_apply]
  change (freeSymbol P n K : ℂ)*physicalSector n (u n) K =
    physicalSector n (f n) K-(c : ℂ)*physicalSector n (u n) K
  change ((freeSymbol P n K+c : ℝ) : ℂ)*physicalSector n (u n) K=physicalSector n (f n) K at hw
  push_cast at hw
  linear_combination hw

theorem freeShiftInverse_mem_free_domain (f : GW.Fock.Carrier) :
    freeShiftInverse P c hc f ∈ (freeFiberOperator P).domain :=
  (freeFiberOperator P).mem_domain_of_mem_graph (freeShiftInverse_free_graph P c hc f)

theorem freeShiftInverse_free_equation (f : GW.Fock.Carrier) :
    freeFiberOperator P ⟨freeShiftInverse P c hc f,freeShiftInverse_mem_free_domain P c hc f⟩ +
      (c : ℂ) • freeShiftInverse P c hc f=f := by
  have he := (freeFiberOperator P).mem_graph_snd_inj
    ((freeFiberOperator P).mem_graph ⟨freeShiftInverse P c hc f,freeShiftInverse_mem_free_domain P c hc f⟩)
    (freeShiftInverse_free_graph P c hc f) rfl
  rw [he,sub_add_cancel]

end Froehlich
