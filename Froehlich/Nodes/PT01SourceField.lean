import Froehlich.Nodes.PT01EnergyField

set_option autoImplicit false

/-! The actual local L² physical source and its energy-dual lift in PT01.
No pull-through identity is assumed here. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Froehlich

variable (m : ℕ) (K : Set GW.Space)

def restrictedHighAnnihilationField (x : NumberFormSpace) :
    Lp (HighSectorSpace m) 2 ((volume : Measure GW.Space).restrict K) :=
  (highSectorProject m).compLp
    (LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K (annihilationField x))

theorem restrictedHighAnnihilationField_physical (x : NumberFormSpace)
    (hx : numberFormEmbedding x ∈ HighSectorSpace (m+1)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      (restrictedHighAnnihilationField m K x k : GW.Fock.Carrier) = annihilationField x k := by
  have hh := ae_restrict_of_ae (s := K) (annihilationField_mem_high_of_number_high m x hx)
  filter_upwards [(highSectorProject m).coeFn_compLp
    (LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K (annihilationField x)),
    LpToLpRestrictCLM_coeFn ℂ K (annihilationField x),hh] with k hm hr hh
  change ((highSectorProject m).compLp
    (LpToLpRestrictCLM GW.Space GW.Fock.Carrier ℂ volume 2 K (annihilationField x)) k : GW.Fock.Carrier) = _
  rw [hm,hr]
  exact (highSector_mem_iff m _).mp hh

def localPullthroughSource (x : NumberFormSpace) (u : HighSectorSpace m)
    (v : GW.Space → ℂ) (hv : MemLp v 2 ((volume : Measure GW.Space).restrict K)) :
    Lp (HighSectorSpace m) 2 ((volume : Measure GW.Space).restrict K) :=
  restrictedHighAnnihilationField m K x -
    ((ContinuousLinearMap.id ℂ ℂ).smulRight u).compLp (hv.toLp v)

theorem localPullthroughSource_physical (x : NumberFormSpace)
    (hx : numberFormEmbedding x ∈ HighSectorSpace (m+1)) (u : HighSectorSpace m)
    (v : GW.Space → ℂ) (hv : MemLp v 2 ((volume : Measure GW.Space).restrict K)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K),
      (localPullthroughSource m K x u v hv k : GW.Fock.Carrier) =
        annihilationField x k - v k • (u : GW.Fock.Carrier) := by
  filter_upwards [Lp.coeFn_sub (restrictedHighAnnihilationField m K x)
      (((ContinuousLinearMap.id ℂ ℂ).smulRight u).compLp (hv.toLp v)),
    restrictedHighAnnihilationField_physical m K x hx,
    ((ContinuousLinearMap.id ℂ ℂ).smulRight u).coeFn_compLp (hv.toLp v),
    hv.coeFn_toLp] with k hs ha hm hvk
  simp only [Pi.sub_apply] at hs
  change ((restrictedHighAnnihilationField m K x -
    ((ContinuousLinearMap.id ℂ ℂ).smulRight u).compLp (hv.toLp v)) k : GW.Fock.Carrier) = _
  rw [hs,hm,hvk]
  change (restrictedHighAnnihilationField m K x k : GW.Fock.Carrier) -
    v k • (u : GW.Fock.Carrier) = _
  rw [ha]

def localPullthroughDualSource (x : NumberFormSpace) (u : HighSectorSpace m)
    (v : GW.Space → ℂ) (hv : MemLp v 2 ((volume : Measure GW.Space).restrict K)) :
    Lp (HighEnergySpace 0 m) 2 ((volume : Measure GW.Space).restrict K) :=
  (highEnergyEmbedding 0 m).adjoint.compLp (localPullthroughSource m K x u v hv)

theorem localPullthroughDualSource_pairing (x : NumberFormSpace)
    (hx : numberFormEmbedding x ∈ HighSectorSpace (m+1)) (u : HighSectorSpace m)
    (v : GW.Space → ℂ) (hv : MemLp v 2 ((volume : Measure GW.Space).restrict K)) :
    ∀ᵐ k ∂((volume : Measure GW.Space).restrict K), ∀ w : HighEnergySpace 0 m,
      ⟪w,localPullthroughDualSource m K x u v hv k⟫_ℂ =
        ⟪(highEnergyEmbedding 0 m w : GW.Fock.Carrier),
          annihilationField x k - v k • (u : GW.Fock.Carrier)⟫_ℂ := by
  filter_upwards [(highEnergyEmbedding 0 m).adjoint.coeFn_compLp
      (localPullthroughSource m K x u v hv),
    localPullthroughSource_physical m K x hx u v hv] with k hj hp
  intro w
  change ⟪w,(highEnergyEmbedding 0 m).adjoint.compLp
    (localPullthroughSource m K x u v hv) k⟫_ℂ = _
  rw [hj,(highEnergyEmbedding 0 m).adjoint_inner_right]
  change ⟪(highEnergyEmbedding 0 m w : GW.Fock.Carrier),
    (localPullthroughSource m K x u v hv k : GW.Fock.Carrier)⟫_ℂ = _
  rw [hp]

end Froehlich
