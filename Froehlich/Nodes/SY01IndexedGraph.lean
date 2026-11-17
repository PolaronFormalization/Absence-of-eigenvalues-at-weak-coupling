import Froehlich.Nodes.SY01Hamiltonian
import Froehlich.Nodes.SY01IndexedForms

/-! Literal graph and domain equivalences for every actual cutoff/singular
associated operator. The reverse implications use only involutions. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem indexedHamiltonian_graph_weak_iff (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (u f : GW.Fock.Carrier) :
    (u,f) ∈ (GW.Operators.formOperator (fiberFormData g P i)).graph ↔
      ∃ x : EnergySpace P, energyEmbedding P x = u ∧
        ∀ w, (fiberFormData g P i).form w x = ⟪energyEmbedding P w,f⟫_ℂ := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := (GW.Operators.formOperator (fiberFormData g P i)).mem_graph_iff'.mp h
    refine ⟨GW.Operators.operatorFormCoordinate (fiberFormData g P i) a,?_,?_⟩
    · exact (GW.Operators.operatorFormCoordinate_embedding _ a).trans (congrArg Prod.fst ha)
    · intro w
      exact (GW.Operators.formOperator_form_identity _ a w).trans
        (congrArg (fun z : GW.Fock.Carrier => ⟪energyEmbedding P w,z⟫_ℂ) (congrArg Prod.snd ha))
  · rintro ⟨x,hx,hw⟩
    obtain ⟨hm,hf⟩ := GW.Operators.formOperator_domain_of_equation (fiberFormData g P i) x f hw
    exact (GW.Operators.formOperator (fiberFormData g P i)).mem_graph_iff.mpr
      ⟨⟨energyEmbedding P x,hm⟩,hx,hf⟩

theorem indexedHamiltonian_graph_conjugation (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (u f : GW.Fock.Carrier)
    (h : (u,f) ∈ (GW.Operators.formOperator (fiberFormData g P i)).graph) :
    (fockConjugation u,fockConjugation f) ∈ (GW.Operators.formOperator (fiberFormData g P i)).graph := by
  obtain ⟨x,hx,hw⟩ := (indexedHamiltonian_graph_weak_iff g P i u f).mp h
  apply (indexedHamiltonian_graph_weak_iff g P i _ _).mpr
  refine ⟨energyConjugation P x,by rw [energyConjugation_intertwines,hx],?_⟩
  intro w
  have hc := indexedFiberForm_conjugation g P i (energyConjugation P w) x
  rw [energyConjugation_involutive P w,hw,energyConjugation_intertwines,
    fockConjugation_inner_flip] at hc
  exact hc

theorem indexedHamiltonian_graph_reflection (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (u f : GW.Fock.Carrier)
    (h : (u,f) ∈ (GW.Operators.formOperator (fiberFormData g P i)).graph) :
    (fockReflection u,fockReflection f) ∈ (GW.Operators.formOperator (fiberFormData g (-P) i)).graph := by
  obtain ⟨x,hx,hw⟩ := (indexedHamiltonian_graph_weak_iff g P i u f).mp h
  apply (indexedHamiltonian_graph_weak_iff g (-P) i _ _).mpr
  refine ⟨energyReflection P x,by rw [energyReflection_intertwines,hx],?_⟩
  intro w
  have hc := indexedFiberForm_reflection g P i ((energyReflection P).symm w) x
  rw [LinearIsometryEquiv.apply_symm_apply,hw,energyReflection_symm_intertwines,
    fockReflection_inner_flip] at hc
  exact hc

theorem indexedHamiltonian_graph_conjugation_iff (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (u f : GW.Fock.Carrier) :
    (fockConjugation u,fockConjugation f) ∈ (GW.Operators.formOperator (fiberFormData g P i)).graph ↔
      (u,f) ∈ (GW.Operators.formOperator (fiberFormData g P i)).graph := by
  constructor
  · intro h
    simpa only [fockConjugation_involutive u,fockConjugation_involutive f] using
      indexedHamiltonian_graph_conjugation g P i _ _ h
  · exact indexedHamiltonian_graph_conjugation g P i u f

theorem indexedHamiltonian_graph_reflection_iff (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (u f : GW.Fock.Carrier) :
    (fockReflection u,fockReflection f) ∈ (GW.Operators.formOperator (fiberFormData g (-P) i)).graph ↔
      (u,f) ∈ (GW.Operators.formOperator (fiberFormData g P i)).graph := by
  constructor
  · intro h
    have hh := indexedHamiltonian_graph_reflection g (-P) i
      (fockReflection u) (fockReflection f) h
    rw [neg_neg] at hh
    rw [fockReflection_involutive u] at hh
    rw [fockReflection_involutive f] at hh
    exact hh
  · exact indexedHamiltonian_graph_reflection g P i u f

theorem indexedHamiltonian_domain_conjugation_iff (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (u : GW.Fock.Carrier) :
    fockConjugation u ∈ (GW.Operators.formOperator (fiberFormData g P i)).domain ↔
      u ∈ (GW.Operators.formOperator (fiberFormData g P i)).domain := by
  constructor <;> intro hu
  · have h := indexedHamiltonian_graph_conjugation g P i _ _
      ((GW.Operators.formOperator (fiberFormData g P i)).mem_graph ⟨fockConjugation u,hu⟩)
    rw [fockConjugation_involutive u] at h
    exact (GW.Operators.formOperator (fiberFormData g P i)).mem_domain_of_mem_graph h
  · exact (GW.Operators.formOperator (fiberFormData g P i)).mem_domain_of_mem_graph
      (indexedHamiltonian_graph_conjugation g P i _ _
        ((GW.Operators.formOperator (fiberFormData g P i)).mem_graph ⟨u,hu⟩))

theorem indexedHamiltonian_domain_reflection_iff (g : ℝ) (P : GW.Space)
    (i : Option GW.Operators.PositiveCutoff) (u : GW.Fock.Carrier) :
    fockReflection u ∈ (GW.Operators.formOperator (fiberFormData g (-P) i)).domain ↔
      u ∈ (GW.Operators.formOperator (fiberFormData g P i)).domain := by
  constructor <;> intro hu
  · have h := indexedHamiltonian_graph_reflection g (-P) i _ _
      ((GW.Operators.formOperator (fiberFormData g (-P) i)).mem_graph ⟨fockReflection u,hu⟩)
    rw [neg_neg] at h
    rw [fockReflection_involutive u] at h
    exact (GW.Operators.formOperator (fiberFormData g P i)).mem_domain_of_mem_graph h
  · exact (GW.Operators.formOperator (fiberFormData g (-P) i)).mem_domain_of_mem_graph
      (indexedHamiltonian_graph_reflection g P i _ _
        ((GW.Operators.formOperator (fiberFormData g P i)).mem_graph ⟨u,hu⟩))

end Froehlich
