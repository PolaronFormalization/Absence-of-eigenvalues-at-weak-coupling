import Froehlich.Nodes.SY01TotalForms

/-! Actual Hamiltonian graph transport from its full weak-domain characterization. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem energyReflection_symm_intertwines (P : GW.Space) (w : EnergySpace (-P)) :
    energyEmbedding P ((energyReflection P).symm w) = fockReflection (energyEmbedding (-P) w) := by
  have h := energyReflection_intertwines P ((energyReflection P).symm w)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  have he := congrArg fockReflection h
  rw [fockReflection_involutive] at he
  exact he.symm

theorem fockConjugation_inner_flip (u v : GW.Fock.Carrier) :
    (starRingEnd ℂ) ⟪fockConjugation u,v⟫_ℂ = ⟪u,fockConjugation v⟫_ℂ := by
  have h := fockConjugation_inner u (fockConjugation v)
  rw [fockConjugation_involutive] at h
  rw [h,starRingEnd_self_apply]

theorem fockReflection_inner_flip (u v : GW.Fock.Carrier) :
    ⟪fockReflection u,v⟫_ℂ = ⟪u,fockReflection v⟫_ℂ := by
  have h := fockReflectionEquiv.inner_map_map u (fockReflection v)
  change ⟪fockReflection u,fockReflection (fockReflection v)⟫_ℂ = _ at h
  rw [fockReflection_involutive] at h
  exact h

theorem fiberHamiltonian_graph_conjugation (g : ℝ) (P : GW.Space) (u f : GW.Fock.Carrier)
    (h : (u,f) ∈ (fiberHamiltonian g P).graph) :
    (fockConjugation u,fockConjugation f) ∈ (fiberHamiltonian g P).graph := by
  obtain ⟨x,hx,hw⟩ := (fiberHamiltonian_graph_iff g P u f).mp h
  apply (fiberHamiltonian_graph_iff g P _ _).mpr
  refine ⟨energyConjugation P x,by rw [energyConjugation_intertwines,hx],?_⟩
  intro w
  have hc := fiberTotalForm_conjugation g P (energyConjugation P w) x
  rw [energyConjugation_involutive P w] at hc
  have ht := hw (energyConjugation P w)
  rw [energyConjugation_intertwines] at ht
  change (fiberFormData g P none).form w (energyConjugation P x) = _
  rw [hc]
  change (starRingEnd ℂ) (freeFiberForm P (energyConjugation P w) x +
    singularInteraction g P (energyConjugation P w) x) = _
  rw [ht,fockConjugation_inner_flip]

theorem fiberHamiltonian_graph_reflection (g : ℝ) (P : GW.Space) (u f : GW.Fock.Carrier)
    (h : (u,f) ∈ (fiberHamiltonian g P).graph) :
    (fockReflection u,fockReflection f) ∈ (fiberHamiltonian g (-P)).graph := by
  obtain ⟨x,hx,hw⟩ := (fiberHamiltonian_graph_iff g P u f).mp h
  apply (fiberHamiltonian_graph_iff g (-P) _ _).mpr
  refine ⟨energyReflection P x,by rw [energyReflection_intertwines,hx],?_⟩
  intro w
  have hc := fiberTotalForm_reflection g P ((energyReflection P).symm w) x
  rw [LinearIsometryEquiv.apply_symm_apply] at hc
  have ht := hw ((energyReflection P).symm w)
  rw [energyReflection_symm_intertwines] at ht
  change (fiberFormData g (-P) none).form w (energyReflection P x) = _
  rw [hc]
  change freeFiberForm P ((energyReflection P).symm w) x +
    singularInteraction g P ((energyReflection P).symm w) x = _
  rw [ht,fockReflection_inner_flip]

theorem fiberHamiltonian_domain_conjugation (g : ℝ) (P : GW.Space) (u : GW.Fock.Carrier)
    (hu : u ∈ (fiberHamiltonian g P).domain) : fockConjugation u ∈ (fiberHamiltonian g P).domain :=
  (fiberHamiltonian g P).mem_domain_of_mem_graph
    (fiberHamiltonian_graph_conjugation g P u _ ((fiberHamiltonian g P).mem_graph ⟨u,hu⟩))

theorem fiberHamiltonian_domain_reflection (g : ℝ) (P : GW.Space) (u : GW.Fock.Carrier)
    (hu : u ∈ (fiberHamiltonian g P).domain) : fockReflection u ∈ (fiberHamiltonian g (-P)).domain :=
  (fiberHamiltonian g (-P)).mem_domain_of_mem_graph
    (fiberHamiltonian_graph_reflection g P u _ ((fiberHamiltonian g P).mem_graph ⟨u,hu⟩))

end Froehlich
