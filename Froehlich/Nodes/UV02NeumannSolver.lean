import Froehlich.Nodes.UV02RelativeField
import Froehlich.Nodes.UV02FreeDomainInclusion
import Froehlich.Nodes.UV02FreeGraph
import Froehlich.Nodes.BA02

/-! The source's fixed-cutoff Neumann construction solves HΛ+c on the
actual maximal free domain. The shift c is not used in any cutoff limit. -/
noncomputable section
namespace Froehlich
variable (g : ℝ) (P : GW.Space) (Λ : GW.Operators.PositiveCutoff) (c : ℝ) (hc : 1 ≤ c)

def cutoffShiftFactorInverse : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier :=
  neumannInverse (-(freeShiftRelativeField P c hc (cutoffFormFactorL2 g Λ.val Λ.property)))

def cutoffShiftSolution (z : GW.Fock.Carrier) : GW.Fock.Carrier :=
  freeShiftInverse P c hc (cutoffShiftFactorInverse g P Λ c hc z)

theorem cutoffShiftSolution_mem_free (z : GW.Fock.Carrier) :
    cutoffShiftSolution g P Λ c hc z ∈ (freeFiberOperator P).domain :=
  freeShiftInverse_mem_free_domain P c hc _

variable (hsmall : ‖freeShiftRelativeField P c hc (cutoffFormFactorL2 g Λ.val Λ.property)‖<1/2)
include hsmall

theorem cutoffShiftFactorInverse_right :
    (1+freeShiftRelativeField P c hc (cutoffFormFactorL2 g Λ.val Λ.property))*
      cutoffShiftFactorInverse g P Λ c hc=1 := by
  have hn : ‖-(freeShiftRelativeField P c hc (cutoffFormFactorL2 g Λ.val Λ.property))‖<1 :=
    (ContinuousLinearMap.opNorm_neg _).trans_lt (hsmall.trans (by norm_num))
  simpa only [cutoffShiftFactorInverse,sub_neg_eq_add] using
    neumannInverse_right (-(freeShiftRelativeField P c hc (cutoffFormFactorL2 g Λ.val Λ.property))) hn

theorem cutoffShiftSolution_graph (z : GW.Fock.Carrier) :
    (cutoffShiftSolution g P Λ c hc z,z-(c : ℂ) • cutoffShiftSolution g P Λ c hc z) ∈
      (cutoffHamiltonian g P Λ).graph := by
  let y := cutoffShiftFactorInverse g P Λ c hc z
  let u := freeShiftInverse P c hc y
  obtain ⟨x,hx,hgraph⟩ := freeGraph_cutoffGraph g P Λ u (y-(c : ℂ) • u)
    (freeShiftInverse_free_graph P c hc y)
  have hx' : x=freeShiftEnergyInverse P c hc y := by
    apply energyEmbedding_injective P
    rw [hx,freeShiftEnergyInverse_physical]
  rw [hx'] at hgraph
  have hfactor := congrArg (fun T : GW.Fock.Carrier →L[ℂ] GW.Fock.Carrier => T z)
    (cutoffShiftFactorInverse_right g P Λ c hc hsmall)
  change y+freeShiftRelativeField P c hc (cutoffFormFactorL2 g Λ.val Λ.property) y=z at hfactor
  have he : y-(c : ℂ) • u+energySmearedField P (cutoffFormFactorL2 g Λ.val Λ.property)
      (freeShiftEnergyInverse P c hc y)=z-(c : ℂ) • u := by
    change y-(c : ℂ) • u+freeShiftRelativeField P c hc (cutoffFormFactorL2 g Λ.val Λ.property) y=_
    rw [←hfactor]
    abel
  rw [he] at hgraph
  exact hgraph

theorem cutoffShiftSolution_mem_cutoff (z : GW.Fock.Carrier) :
    cutoffShiftSolution g P Λ c hc z ∈ (cutoffHamiltonian g P Λ).domain :=
  (cutoffHamiltonian g P Λ).mem_domain_of_mem_graph (cutoffShiftSolution_graph g P Λ c hc hsmall z)

theorem cutoffShiftSolution_equation (z : GW.Fock.Carrier) :
    cutoffHamiltonian g P Λ ⟨cutoffShiftSolution g P Λ c hc z,cutoffShiftSolution_mem_cutoff g P Λ c hc hsmall z⟩+
      (c : ℂ) • cutoffShiftSolution g P Λ c hc z=z := by
  have he := (cutoffHamiltonian g P Λ).mem_graph_snd_inj
    ((cutoffHamiltonian g P Λ).mem_graph ⟨cutoffShiftSolution g P Λ c hc z,cutoffShiftSolution_mem_cutoff g P Λ c hc hsmall z⟩)
    (cutoffShiftSolution_graph g P Λ c hc hsmall z) rfl
  rw [he,sub_add_cancel]

end Froehlich
