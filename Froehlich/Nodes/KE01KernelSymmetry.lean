import Froehlich.Nodes.KE01KernelReality
import Froehlich.Nodes.RS03StaticBounded

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem ke01_auxiliaryResolvent_selfadjoint (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2) :
    (auxiliaryResolvent n e p he g hg hs).adjoint = auxiliaryResolvent n e p he g hg hs := by
  simp only [auxiliaryResolvent,ContinuousLinearMap.adjoint_comp,
    auxiliaryPhysicalFreeInverse_selfadjoint,rs03NormalizedInverse_selfadjoint,
    ContinuousLinearMap.comp_assoc]

theorem auxiliaryExtendedResolvent_pairing (n : ℕ) (e : ℝ) (p : GW.Space)
    (he : e ∈ Set.Icc (-1/4 : ℝ) 0)
    (g : ℝ) (hg : |g| ≤ 1) (hs : auxiliaryResolventConstant*|g| ≤ 1/2)
    (u v : GW.Fock.Carrier) :
    ⟪u,auxiliaryExtendedResolvent n e p he g hg hs v⟫_ℂ =
      ⟪auxiliaryExtendedResolvent n e p he g hg hs u,v⟫_ℂ := by
  let R := auxiliaryResolvent n e p he g hg hs
  have hleft (a : GW.Fock.Carrier) (b : HighSectorSpace n) :
      ⟪a,(b : GW.Fock.Carrier)⟫_ℂ = ⟪highSectorProject n a,b⟫_ℂ := by
    change ⟪a,(b : GW.Fock.Carrier)⟫_ℂ = ⟪highSectorProjection n a,(b : GW.Fock.Carrier)⟫_ℂ
    rw [highSectorProjection_pairing,(highSector_mem_iff n b).mp b.property]
  have hright (a : HighSectorSpace n) (b : GW.Fock.Carrier) :
      ⟪(a : GW.Fock.Carrier),b⟫_ℂ = ⟪a,highSectorProject n b⟫_ℂ := by
    change ⟪(a : GW.Fock.Carrier),b⟫_ℂ = ⟪(a : GW.Fock.Carrier),highSectorProjection n b⟫_ℂ
    rw [←highSectorProjection_pairing,(highSector_mem_iff n a).mp a.property]
  change ⟪u,(R (highSectorProject n v) : GW.Fock.Carrier)⟫_ℂ =
    ⟪(R (highSectorProject n u) : GW.Fock.Carrier),v⟫_ℂ
  rw [hleft,hright]
  have h := R.adjoint_inner_right (highSectorProject n u) (highSectorProject n v)
  rw [show R.adjoint = R from ke01_auxiliaryResolvent_selfadjoint n e p he g hg hs] at h
  exact h


variable (e : ℝ) (he : e ∈ Set.Icc (-1/4 : ℝ) 0) (g : ℝ) (hg : |g| ≤ 1)
    (hs : auxiliaryResolventConstant * |g| ≤ 1/2)

theorem thresholdKernelJ_symmetric (P q r : GW.Space) :
    thresholdKernelJ e he g hg hs P q r = thresholdKernelJ e he g hg hs P r q := by
  have hP : P+q+r = P+r+q := by abel
  have h := thresholdKernelJ_conj e he g hg hs P r q
  unfold thresholdKernelJ at h ⊢
  simp only [map_add,inner_conj_symm] at h
  rw [show P+r+q = P+q+r from hP.symm] at h
  rw [show P+r+q = P+q+r from hP.symm]
  have hz := auxiliaryExtendedResolvent_pairing 0 e (P+q+r) he g hg hs
    (GW.Fock.vacuum-auxiliaryGroundSourceVector e q he g hg hs)
    (GW.Fock.vacuum-auxiliaryGroundSourceVector e r he g hg hs)
  have hx := auxiliaryExtendedResolvent_pairing 2 e (-P) he g hg hs
    (auxiliaryGroundSourceVector e q he g hg hs) (auxiliaryGroundSourceVector e r he g hg hs)
  change ⟪_,auxiliaryZ e (P+q+r) he g hg hs _⟫_ℂ = ⟪auxiliaryZ e (P+q+r) he g hg hs _,_⟫_ℂ at hz
  change ⟪_,auxiliaryX e he g hg hs P _⟫_ℂ = ⟪auxiliaryX e he g hg hs P _,_⟫_ℂ at hx
  rw [hz,hx]
  exact h

theorem thresholdKernelC_symmetric (P q r : GW.Space) :
    thresholdKernelC e he g hg hs P q r = thresholdKernelC e he g hg hs P r q := by
  unfold thresholdKernelC
  rw [thresholdKernelJ_symmetric e he g hg hs P q r]

end Froehlich
