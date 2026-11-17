import Froehlich.Nodes.FC07ProjectionField

/-! The source projected cutoff pullthrough, with the same fixed real e on
both sides. All compressed operators and scalar shifts are actual GW maps. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem highSectorProjection_absorbs (n m : ℕ) (hnm : n ≤ m) (u : GW.Fock.Carrier) :
    highSectorProjection n (highSectorProjection m u) = highSectorProjection m u := by
  apply lp.ext
  funext r
  simp only [highSectorProjection_apply]
  by_cases hm : m ≤ r
  · simp only [if_pos hm,if_pos (hnm.trans hm)]
  · simp only [if_neg hm,ite_self]

theorem highSector_mem_of_succ (m : ℕ) (u : GW.Fock.Carrier) (hu : u ∈ HighSectorSpace (m+1)) :
    u ∈ HighSectorSpace m := by
  apply (highSector_mem_iff m u).mpr
  have h := highSectorProjection_absorbs m (m+1) (Nat.le_succ m) u
  rw [(highSector_mem_iff (m+1) u).mp hu] at h
  exact h

theorem projectedCutoffField_ae (g : ℝ) (P : GW.Space) (m : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P (m+1) Λ e u)) k =
        highSectorProjection m (annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)) k) -
          ((e-1+((m+1 : ℕ) : ℝ) : ℝ) : ℂ) • annihilationField (coreNumberLift u) k := by
  let c : ℂ := ((e-1+((m+1 : ℕ) : ℝ) : ℝ) : ℂ)
  have he : annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P (m+1) Λ e u)) =
      (highSectorProjection m).compLp (annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u))) -
        c • annihilationField (coreNumberLift u) := by
    simp only [coreProjectedCutoffShiftAction,map_sub,map_smul,annihilationField_core_highProjection,c]
  filter_upwards [Lp.coeFn_sub
    ((highSectorProjection m).compLp (annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u))))
    (c • annihilationField (coreNumberLift u)),
    (highSectorProjection m).coeFn_compLp (annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u))),
    Lp.coeFn_smul c (annihilationField (coreNumberLift u))] with k hs hp hc
  have hk := congrArg (fun z : Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) => z k) he
  simp only [Pi.sub_apply,Pi.smul_apply] at hs hc
  exact hk.trans (hs.trans (congrArg₂ (fun x y : GW.Fock.Carrier => x-y) hp hc))

def projectedCutoffShiftField (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore) :
    Lp GW.Fock.Carrier 2 (volume : Measure GW.Space) :=
  annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P n Λ e u)) -
    GW.Fock.tensorEmbedding volume (cutoffFormFactorL2 g Λ.val Λ.property) (u : GW.Fock.Carrier)

theorem projectedCutoffShiftField_ae (g : ℝ) (P : GW.Space) (n : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore) :
    ∀ᵐ k ∂(volume : Measure GW.Space), projectedCutoffShiftField g P n Λ e u k =
      annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P n Λ e u)) k -
        cutoffFormFactorL2 g Λ.val Λ.property k • (u : GW.Fock.Carrier) := by
  filter_upwards [Lp.coeFn_sub
    (annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P n Λ e u)))
    (GW.Fock.tensorEmbedding volume (cutoffFormFactorL2 g Λ.val Λ.property) (u : GW.Fock.Carrier)),
    GW.Fock.tensorEmbedding_ae volume (cutoffFormFactorL2 g Λ.val Λ.property) (u : GW.Fock.Carrier)] with k hs ht
  have he : projectedCutoffShiftField g P n Λ e u k =
      annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P n Λ e u)) k -
        GW.Fock.tensorEmbedding volume (cutoffFormFactorL2 g Λ.val Λ.property) (u : GW.Fock.Carrier) k := hs
  exact he.trans (congrArg (fun z : GW.Fock.Carrier =>
    annihilationField (coreNumberLift (coreProjectedCutoffShiftAction g P n Λ e u)) k-z) ht)

theorem projectedCutoffShiftField_graph (g : ℝ) (P : GW.Space) (m : ℕ)
    (Λ : GW.Operators.PositiveCutoff) (e : ℝ) (u : boundedMomentumCore)
    (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace (m+1)) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∃ q r : HighSectorSpace m,
      (q : GW.Fock.Carrier) = annihilationField (coreNumberLift u) k ∧
      (r : GW.Fock.Carrier) = projectedCutoffShiftField g P (m+1) Λ e u k ∧
      (q,r) ∈ (GW.Operators.complexShift (compressedHamiltonian g (P-k) m (some Λ))
        ((e-1+(m : ℝ) : ℝ) : ℂ)).graph := by
  have hfixU : highSectorProjection m (u : GW.Fock.Carrier) = (u : GW.Fock.Carrier) :=
    (highSector_mem_iff m _).mp (highSector_mem_of_succ m _ hu)
  have hscalar : ((e-1+((m+1 : ℕ) : ℝ) : ℝ) : ℂ) = ((e-1+(m : ℝ) : ℝ) : ℂ) + 1 := by
    push_cast
    ring
  filter_upwards [annihilationField_core_ae u,annihilationField_high_core_ae m u hu,
    cutoffShiftField_graph g P Λ u,cutoffShiftField_ae g P Λ u,
    projectedCutoffField_ae g P m Λ e u,projectedCutoffShiftField_ae g P (m+1) Λ e u]
      with k hcore hhigh hcut hcutval hproj hresult
  let v : boundedMomentumCore := ⟨annihilationField (coreNumberLift u) k,hcore⟩
  have hv : (v : GW.Fock.Carrier) = annihilationField (coreNumberLift u) k := rfl
  have hvhigh : (v : GW.Fock.Carrier) ∈ HighSectorSpace m := hhigh
  have hfixV : highSectorProjection m (annihilationField (coreNumberLift u) k) =
      annihilationField (coreNumberLift u) k := (highSector_mem_iff m _).mp hhigh
  have haction := (cutoffHamiltonian g (P-k) Λ).mem_graph_snd_inj hcut
    (cutoffHamiltonian_core_graph g (P-k) Λ v) hv.symm
  have hproject : highSectorProjection m (coreCutoffAction g (P-k) Λ v) =
      highSectorProjection m (annihilationField (coreNumberLift (coreCutoffActionCore g P Λ u)) k) -
        annihilationField (coreNumberLift u) k - cutoffFormFactorL2 g Λ.val Λ.property k • (u : GW.Fock.Carrier) := by
    rw [← haction,hcutval,map_sub,map_sub,map_smul,hfixV,hfixU]
  let q : HighSectorSpace m := ⟨(v : GW.Fock.Carrier),hvhigh⟩
  let r := compressedCutoffShiftCoreOutput g (P-k) m Λ e v hvhigh
  have hr : projectedCutoffShiftField g P (m+1) Λ e u k = (r : GW.Fock.Carrier) := by
    rw [hresult,hproj]
    change _ = highSectorProjection m (coreCutoffAction g (P-k) Λ v) -
      ((e-1+(m : ℝ) : ℝ) : ℂ) • (v : GW.Fock.Carrier)
    rw [hproject,hv,hscalar,add_smul,one_smul]
    abel
  exact ⟨q,r,hv,hr.symm,compressedCutoffShift_core_graph g (P-k) m Λ e v hvhigh⟩

/-- Source n=1: the zero complement is the actual full canonical operator. -/
theorem projectedCutoff_one_graph (g : ℝ) (p : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (e : ℝ) (u : boundedMomentumCore) (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace 1) :
    ∀ᵐ k ∂(volume : Measure GW.Space),
      (annihilationField (coreNumberLift u) k,projectedCutoffShiftField g (-p) 1 Λ e u k) ∈
        (GW.Operators.complexShift (cutoffHamiltonian g (-(p+k)) Λ) ((e-1 : ℝ) : ℂ)).graph := by
  filter_upwards [projectedCutoffShiftField_graph g (-p) 0 Λ e u hu] with k hk
  obtain ⟨q,r,hq,hr,hgraph⟩ := hk
  have h := (compressed_zero_shift_graph_iff g (-p-k) (some Λ) ((e-1+(0 : ℝ) : ℝ) : ℂ) q r).mp hgraph
  have hP : -p-k = -(p+k) := by abel
  rw [hq,hr,hP] at h
  change (annihilationField (coreNumberLift u) k,projectedCutoffShiftField g (-p) 1 Λ e u k) ∈
    (GW.Operators.complexShift (cutoffHamiltonian g (-(p+k)) Λ) ((e-1+(0 : ℝ) : ℝ) : ℂ)).graph at h
  simpa only [add_zero] using h

/-- Source n=2: the moving output is in the actual one-sector complement. -/
theorem projectedCutoff_two_graph (g : ℝ) (p : GW.Space) (Λ : GW.Operators.PositiveCutoff)
    (e : ℝ) (u : boundedMomentumCore) (hu : (u : GW.Fock.Carrier) ∈ HighSectorSpace 2) :
    ∀ᵐ k ∂(volume : Measure GW.Space), ∃ q r : HighSectorSpace 1,
      (q : GW.Fock.Carrier) = annihilationField (coreNumberLift u) k ∧
      (r : GW.Fock.Carrier) = projectedCutoffShiftField g (-p) 2 Λ e u k ∧
      (q,r) ∈ (GW.Operators.complexShift (compressedHamiltonian g (-(p+k)) 1 (some Λ)) (e : ℂ)).graph := by
  filter_upwards [projectedCutoffShiftField_graph g (-p) 1 Λ e u hu] with k hk
  obtain ⟨q,r,hq,hr,hgraph⟩ := hk
  have hP : -p-k = -(p+k) := by abel
  have hc : ((e-1+(1 : ℝ) : ℝ) : ℂ) = (e : ℂ) := by rw [sub_add_cancel]
  rw [hP] at hgraph
  simp only [Nat.cast_one] at hgraph
  rw [hc] at hgraph
  have hr' : (r : GW.Fock.Carrier) = projectedCutoffShiftField g (-p) 2 Λ e u k := by
    change (r : GW.Fock.Carrier) = projectedCutoffShiftField g (-p) (1+1) Λ e u k
    exact hr
  exact ⟨q,r,hq,hr',hgraph⟩

end Froehlich
