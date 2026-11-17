import Froehlich.Nodes.UV02
import Froehlich.Nodes.UV01PhysicalResolvent
import Froehlich.Nodes.PT01EnergyField
import Froehlich.Nodes.CV01FormRepresentatives

set_option autoImplicit false

/-! UV02 applied to the actual finite-cutoff resolvent: its vector lies in
the true free graph, so FC04 supplies a genuine fixed energy-valued field. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

theorem cutoffShiftGraph_fixed_pairing (m : ℕ) (e : ℝ) (p0 p : GW.Space)
    (hm : m ≤ 2) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ)
    (Λ : GW.Operators.PositiveCutoff) (q r : HighSectorSpace m)
    (v : HighEnergySpace (-p0) m) (hv : highEnergyEmbedding (-p0) m v = q)
    (hgraph : (q,r) ∈ (GW.Operators.complexShift (compressedHamiltonian g (-p) m (some Λ))
      ((e-1+(m : ℝ) : ℝ) : ℂ)).graph) (w : HighEnergySpace (-p0) m) :
    ⟪w,cutoffCommonFormOperator m e p0 p hm he g Λ v⟫_ℂ =
      ⟪highEnergyEmbedding (-p0) m w,r⟫_ℂ := by
  have hfull := (GW.Operators.complexShift_graph_iff
    (compressedHamiltonian g (-p) m (some Λ)) ((e-1+(m : ℝ) : ℝ) : ℂ) (q,r)).mp hgraph
  obtain ⟨x,hx,hweak⟩ := (compressedHamiltonian_graph_iff g (-p) m (some Λ) q
    (r+((e-1+(m : ℝ) : ℝ) : ℂ) • q)).mp hfull
  have hxeq : x = highEnergyCoordinateChange (-p) (-p0) m v := by
    apply highEnergyEmbedding_injective (-p) m
    rw [hx,highEnergyCoordinateChange_physical,hv]
  have h := hweak (highEnergyCoordinateChange (-p) (-p0) m w)
  rw [hxeq] at h
  change (compressedFiberFormData g (-p) m (some Λ)).form
    (highEnergyCoordinateChange (-p) (-p0) m w) (highEnergyCoordinateChange (-p) (-p0) m v) = _ at h
  have hsmul : ⟪highEnergyEmbedding (-p0) m w, ((e-1+(m : ℝ) : ℝ) : ℂ) • q⟫_ℂ =
      ((e-1+(m : ℝ) : ℝ) : ℂ) * ⟪highEnergyEmbedding (-p0) m w,q⟫_ℂ := by
    change ⟪(highEnergyEmbedding (-p0) m w : GW.Fock.Carrier),
      ((e-1+(m : ℝ) : ℝ) : ℂ) • (q : GW.Fock.Carrier)⟫_ℂ = _
    exact inner_smul_right _ _ _
  rw [cutoffCommonFormOperator_spec,h,highEnergyCoordinateChange_physical,
    inner_add_right,hsmul,← hv]
  ring

section FreeGraph
variable (n : ℕ) (e : ℝ) (p : GW.Space) (hn : n ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)

def cutoffAuxiliaryFreeInput (f : HighSectorSpace n) : (freeFiberOperator (-p)).domain :=
  ⟨(cutoffAuxiliaryResolvent n e p he Λ g hg hs f : GW.Fock.Carrier),
    highCutoffDomain_subset_freeDomain g (-p) n Λ
      ((cutoffAuxiliaryResolvent_isResolvent n e p hn he Λ g hg hs).mem_domain f)⟩

def cutoffAuxiliaryGraphCoordinate (f : HighSectorSpace n) : OperatorGraphSpace (-p) :=
  (graphCoordinates (-p)).symm
    (graphWeightOperator (-p) (cutoffAuxiliaryFreeInput n e p hn he Λ g hg hs f))

theorem cutoffAuxiliaryGraphCoordinate_physical (f : HighSectorSpace n) :
    graphEmbedding (-p) (cutoffAuxiliaryGraphCoordinate n e p hn he Λ g hg hs f) =
      (cutoffAuxiliaryResolvent n e p he Λ g hg hs f : GW.Fock.Carrier) :=
  graphEmbedding_product (-p) (cutoffAuxiliaryFreeInput n e p hn he Λ g hg hs f)

end FreeGraph

section LocalField
variable (m : ℕ) (e : ℝ) (p : GW.Space) (hm : m+1 ≤ 2)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (Λ : GW.Operators.PositiveCutoff)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (K : Set GW.Space) (hK : MeasurableSet K) (R : ℝ) (hR : 0 ≤ R)
    (hKR : ∀ k ∈ K, ‖k‖ ≤ R)

def cutoffAuxiliaryLocalEnergyField (f : HighSectorSpace (m+1)) :
    Lp (HighEnergySpace 0 m) 2 ((volume : Measure GW.Space).restrict K) :=
  restrictedHighEnergyFieldMap (-p) m K hK R hR hKR
    (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs f)

theorem cutoffAuxiliaryLocalEnergyField_physical (f : HighSectorSpace (m+1)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      (highEnergyEmbedding 0 m
        (cutoffAuxiliaryLocalEnergyField m e p hm he Λ g hg hs K hK R hR hKR f k) : GW.Fock.Carrier) =
      annihilationField (freeGraphNumberCoordinates (-p)
        (cutoffAuxiliaryGraphCoordinate (m+1) e p hm he Λ g hg hs f)) k := by
  apply restrictedHighEnergyFieldMap_physical
  rw [cutoffAuxiliaryGraphCoordinate_physical]
  exact (cutoffAuxiliaryResolvent (m+1) e p he Λ g hg hs f).property

end LocalField

end Froehlich
