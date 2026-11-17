import Froehlich.Nodes.MN02Reciprocal
import Froehlich.Nodes.GW06Free
import Froehlich.Nodes.DF01
import Froehlich.Nodes.FB02Vacuum

/-! The free vacuum is an eigenvector in the full operator domain. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem freeFiberOperator_vacuum_graph (P : GW.Space) :
    (GW.Fock.vacuum, (‖P‖^2 : ℂ) • GW.Fock.vacuum) ∈ (freeFiberOperator P).graph := by
  apply (freeFiberOperator_graph_ae_iff P _ _).mpr
  intro n
  have hs : physicalSector n ((((‖P‖^2 : ℝ) : ℂ) • GW.Fock.vacuum) n) =
      (((‖P‖^2 : ℝ) : ℂ)) • physicalSector n (GW.Fock.vacuum n) := by
    exact (physicalSector n).map_smul (((‖P‖^2 : ℝ) : ℂ)) (GW.Fock.vacuum n)
  have hcast : (‖P‖^2 : ℂ) = ((‖P‖^2 : ℝ) : ℂ) := by norm_cast
  rw [hcast,hs]
  cases n with
  | zero =>
    filter_upwards [Lp.coeFn_smul (((‖P‖^2 : ℝ) : ℂ))
      (physicalSector 0 (GW.Fock.vacuum 0))] with k hk
    simpa only [freeSymbol_zero,Pi.smul_apply] using hk.symm
  | succ n =>
    rw [GW.Fock.vacuum_succ,map_zero,smul_zero]
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := GW.Fock.sectorMeasure (n+1))] with k hk
    change _ = (0 : GW.Fock.AmbientSector (n+1)) k
    rw [hk]
    simp only [Pi.zero_apply,smul_zero]
theorem fiberHamiltonian_zero_vacuum (P : GW.Space) :
    HasEigenvector (fiberHamiltonian 0 P) (‖P‖^2) := by
  rw [fiberHamiltonian_zero_coupling]
  have hg := freeFiberOperator_vacuum_graph P
  refine ⟨⟨GW.Fock.vacuum,(freeFiberOperator P).mem_domain_of_mem_graph hg⟩, ?_, ?_⟩
  · intro hz
    change GW.Fock.vacuum = 0 at hz
    have hn := GW.Fock.vacuum_norm
    rw [hz,norm_zero] at hn
    norm_num at hn
  · simpa only [Complex.ofReal_pow] using
      (((freeFiberOperator P).image_iff ((freeFiberOperator P).mem_domain_of_mem_graph hg)).mpr hg).symm

end Froehlich
