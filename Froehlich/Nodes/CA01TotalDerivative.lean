import Froehlich.Nodes.CA01PartialFTC
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Mul

/-! Continuous coordinate partials give the actual total norm derivative.
The finite induction reuses Mathlib's two-factor partial-derivative theorem. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def finCoordinateSplit (d : ℕ) : (Fin (d+1) → ℝ) ≃L[ℝ] ℝ × (Fin d → ℝ) :=
  (show (Fin (d+1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin d → ℝ) from
    { toFun := fun q => (q 0,fun i => q i.succ)
      invFun := fun r => Fin.cons r.1 r.2
      left_inv := fun q => Fin.cons_self_tail q
      right_inv := fun r => by cases r; rfl
      map_add' := fun q r => rfl
      map_smul' := fun c q => rfl }).toContinuousLinearEquiv

def finTailInclusion (d : ℕ) : (Fin d → ℝ) →L[ℝ] (Fin (d+1) → ℝ) :=
  (finCoordinateSplit d).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ (Fin d → ℝ))

theorem finTailInclusion_apply (d : ℕ) (q : Fin d → ℝ) :
    finTailInclusion d q = Fin.cons 0 q := rfl

theorem finTailInclusion_single (d : ℕ) (i : Fin d) :
    finTailInclusion d (Pi.single i (1 : ℝ) : Fin d → ℝ) =
      (Pi.single i.succ (1 : ℝ) : Fin (d+1) → ℝ) := by
  rw [finTailInclusion_apply]
  funext j
  cases j using Fin.cases with
  | zero => simp [Pi.single_apply]
  | succ j =>
    simp only [Fin.cons_succ]
    by_cases hji : j = i
    · subst j
      simp [Pi.single_apply]
    · simp [Pi.single_apply,hji,Ne.symm hji]

/-- Internal coordinate version. The candidate is continuous, and each of
its basis values is the genuine coordinate derivative on the same open set. -/
theorem finiteCoordinate_hasFDerivAt (d : ℕ)
    (F : (Fin d → ℝ) → E) (L : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S) (hL : ContinuousOn L S)
    (hpartial : ∀ q ∈ S, ∀ i : Fin d,
      HasDerivAt (fun s : ℝ => F (Function.update q i s)) (L q (Pi.single i 1)) (q i)) :
    ∀ p ∈ S, HasFDerivAt F (L p) p := by
  induction d with
  | zero =>
    intro p hp
    have he : L p = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      have hv : v = 0 := Subsingleton.elim _ _
      rw [hv,map_zero,ContinuousLinearMap.zero_apply]
    rw [he]
    exact hasFDerivAt_of_subsingleton F p
  | succ d ih =>
    intro p hp
    let e := finCoordinateSplit d
    let C : ℝ → (Fin d → ℝ) → E := fun a y => F (Fin.cons a y)
    let A : ℝ → (Fin d → ℝ) → ℝ →L[ℝ] E := fun a y =>
      ContinuousLinearMap.toSpanSingleton ℝ (L (Fin.cons a y) (Pi.single 0 1))
    let B : ℝ → (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] E := fun a y =>
      (L (Fin.cons a y)).comp (finTailInclusion d)
    have hcons : Fin.cons (e p).1 (e p).2 = p := e.symm_apply_apply p
    have hc : Continuous (fun r : ℝ × (Fin d → ℝ) => (Fin.cons r.1 r.2 : Fin (d+1) → ℝ)) := e.symm.continuous
    have hn : ∀ᶠ r in 𝓝 (e p), Fin.cons r.1 r.2 ∈ S :=
      hc.continuousAt.preimage_mem_nhds (by simpa only [hcons] using hS.mem_nhds hp)
    have hA : ∀ᶠ r in 𝓝 (e p), HasFDerivAt (fun a => C a r.2) (A r.1 r.2) r.1 := by
      filter_upwards [hn] with r hr
      have hd := (hpartial (Fin.cons r.1 r.2) hr 0).hasFDerivAt
      simpa only [Fin.update_cons_zero,Fin.cons_zero] using hd
    have hB : ∀ᶠ r in 𝓝 (e p), HasFDerivAt (C r.1) (B r.1 r.2) r.2 := by
      filter_upwards [hn] with r hr
      let T : Set (Fin d → ℝ) := (fun y => Fin.cons r.1 y) ⁻¹' S
      have hpair : Continuous (fun y : Fin d → ℝ => ((r.1,y) : ℝ × (Fin d → ℝ))) :=
        continuous_const.prodMk continuous_id
      have hct : Continuous (fun y : Fin d → ℝ => (Fin.cons r.1 y : Fin (d+1) → ℝ)) :=
        e.symm.continuous.comp hpair
      have hT : IsOpen T := hS.preimage hct
      have hLT : ContinuousOn (fun y => (L (Fin.cons r.1 y)).comp (finTailInclusion d)) T :=
        (hL.comp hct.continuousOn (fun _ hy => hy)).clm_comp continuousOn_const
      have hp₂ : r.2 ∈ T := by
        change Fin.cons r.1 r.2 ∈ S
        exact hr
      have hPT : ∀ y ∈ T, ∀ i : Fin d,
          HasDerivAt (fun s : ℝ => C r.1 (Function.update y i s))
            (((L (Fin.cons r.1 y)).comp (finTailInclusion d)) (Pi.single i 1)) (y i) := by
        intro y hy i
        have hd := hpartial (Fin.cons r.1 y) hy i.succ
        have hf : (fun s : ℝ => F (Function.update (Fin.cons r.1 y) i.succ s)) =
            (fun s : ℝ => C r.1 (Function.update y i s)) := by
          funext s
          rw [← Fin.cons_update]
        rw [hf] at hd
        simpa only [B,ContinuousLinearMap.comp_apply,finTailInclusion_single,Fin.cons_succ] using hd
      exact ih (C r.1) (fun y => (L (Fin.cons r.1 y)).comp (finTailInclusion d)) T hT hLT hPT r.2 hp₂
    have hLc : ContinuousAt (fun r : ℝ × (Fin d → ℝ) => L (Fin.cons r.1 r.2)) (e p) :=
      (hL.continuousAt (hS.mem_nhds (by simpa only [hcons] using hp))).comp hc.continuousAt
    have hAc : ContinuousAt (Function.uncurry A) (e p) :=
      (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.continuousAt.comp
        (hLc.clm_apply continuousAt_const)
    have hBc : ContinuousAt (Function.uncurry B) (e p) := hLc.clm_comp continuousAt_const
    have hd0 := (hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := e p) (f := C) (f₁ := A) (f₂ := B)
      hA hB hAc hBc).hasFDerivAt.comp p e.hasFDerivAt
    have hd : HasFDerivAt F
        (((A (e p).1 (e p).2).coprod (B (e p).1 (e p).2)).comp e.toContinuousLinearMap) p := by
      convert hd0 using 1
      · funext q
        have heq := congrArg F (e.symm_apply_apply q)
        first | exact heq | exact heq.symm
      · apply ContinuousLinearMap.ext
        intro v
        rfl
    have hder : (((A (e p).1 (e p).2).coprod (B (e p).1 (e p).2)).comp e.toContinuousLinearMap) = L p := by
      apply ContinuousLinearMap.ext
      intro v
      change v 0 • L (Fin.cons (e p).1 (e p).2) (Pi.single 0 1) +
        L (Fin.cons (e p).1 (e p).2) (finTailInclusion d (fun i => v i.succ)) = L p v
      rw [hcons,← map_smul,← map_add]
      congr 1
      rw [finTailInclusion_apply]
      funext i
      cases i using Fin.cases <;> simp
    rw [hder] at hd
    exact hd

/-- One fixed bounded linear map assembles the finite partial tuple. -/
def coordinateDerivativeAssembler (d : ℕ) :
    (Fin d → E) →L[ℝ] ((Fin d → ℝ) →L[ℝ] E) :=
  ∑ i : Fin d,
    ((ContinuousLinearMap.smulRightL ℝ (Fin d → ℝ) E)
      (show (Fin d → ℝ) →L[ℝ] ℝ from ContinuousLinearMap.proj i)).comp
        (show (Fin d → E) →L[ℝ] E from ContinuousLinearMap.proj i)

def coordinateDerivative (d : ℕ) (D : Fin d → E) : (Fin d → ℝ) →L[ℝ] E :=
  coordinateDerivativeAssembler d D

theorem coordinateDerivative_apply (d : ℕ) (D : Fin d → E) (h : Fin d → ℝ) :
    coordinateDerivative d D h = ∑ i : Fin d, h i • D i := by
  simp only [coordinateDerivative,coordinateDerivativeAssembler,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRightL_apply_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

theorem coordinateDerivative_single (d : ℕ) (D : Fin d → E) (i : Fin d) :
    coordinateDerivative d D (Pi.single i 1) = D i := by
  rw [coordinateDerivative_apply]
  simp [Pi.single_apply]

/-- The derivative depends continuously on the point when every partial does. -/
theorem coordinateDerivative_continuousOn {X : Type*} [TopologicalSpace X]
    (d : ℕ) (D : X → Fin d → E) (S : Set X) (hD : ∀ i, ContinuousOn (fun p => D p i) S) :
    ContinuousOn (fun p => coordinateDerivative d (D p)) S := by
  exact (coordinateDerivativeAssembler (E := E) d).continuous.comp_continuousOn
    (continuousOn_pi.mpr hD)

theorem continuousCoordinatePartials_hasFDerivAt (d : ℕ)
    (F : (Fin d → ℝ) → E) (D : (Fin d → ℝ) → Fin d → E)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hD : ∀ i, ContinuousOn (fun p => D p i) S)
    (hpartial : ∀ q ∈ S, ∀ i : Fin d,
      HasDerivAt (fun s : ℝ => F (Function.update q i s)) (D q i) (q i))
    (p : Fin d → ℝ) (hp : p ∈ S) :
    HasFDerivAt F (coordinateDerivative d (D p)) p := by
  apply finiteCoordinate_hasFDerivAt d F (fun q => coordinateDerivative d (D q)) S hS
    (coordinateDerivative_continuousOn d D S hD) _ p hp
  intro q hq i
  simpa only [coordinateDerivative_single] using hpartial q hq i

def euclideanCoordinateDerivative (d : ℕ) (D : Fin d → E) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] E :=
  (coordinateDerivative d D).comp (EuclideanSpace.equiv (Fin d) ℝ).toContinuousLinearMap

theorem euclideanCoordinateDerivative_apply (d : ℕ) (D : Fin d → E)
    (h : EuclideanSpace ℝ (Fin d)) :
    euclideanCoordinateDerivative d D h = ∑ i : Fin d, h i • D i :=
  coordinateDerivative_apply d D _

/-- Local continuous coordinate partials on the canonical Euclidean carrier.
The coordinate update changes exactly one coordinate of the physical point. -/
theorem euclideanContinuousPartials_hasFDerivAt (d : ℕ)
    (F : EuclideanSpace ℝ (Fin d) → E) (D : EuclideanSpace ℝ (Fin d) → Fin d → E)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : IsOpen S)
    (hD : ∀ i, ContinuousOn (fun p => D p i) S)
    (hpartial : ∀ q ∈ S, ∀ i : Fin d,
      HasDerivAt (fun s : ℝ => F ((EuclideanSpace.equiv (Fin d) ℝ).symm
        (Function.update ((EuclideanSpace.equiv (Fin d) ℝ) q) i s))) (D q i) (q i))
    (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ S) :
    HasFDerivAt F (euclideanCoordinateDerivative d (D p)) p := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let T := e.symm ⁻¹' S
  have hT : IsOpen T := hS.preimage e.symm.continuous
  have hDT : ∀ i, ContinuousOn (fun y : Fin d → ℝ => D (e.symm y) i) T :=
    fun i => (hD i).comp e.symm.continuous.continuousOn (fun _ hy => hy)
  have hPT : ∀ y ∈ T, ∀ i : Fin d,
      HasDerivAt (fun s : ℝ => F (e.symm (Function.update y i s)))
        (D (e.symm y) i) (y i) := by
    intro y hy i
    have hd : HasDerivAt (fun s : ℝ => F (e.symm (Function.update (e (e.symm y)) i s)))
        (D (e.symm y) i) ((e (e.symm y)) i) := hpartial (e.symm y) hy i
    rw [e.apply_symm_apply] at hd
    exact hd
  have hTp : e p ∈ T := by
    change e.symm (e p) ∈ S
    rw [e.symm_apply_apply]
    exact hp
  have hq := continuousCoordinatePartials_hasFDerivAt d (fun y => F (e.symm y))
    (fun y => D (e.symm y)) T hT hDT hPT (e p) hTp
  have hd := hq.comp p e.hasFDerivAt
  have hf : ((fun y => F (e.symm y)) ∘ e) = F := by
    funext q
    rw [Function.comp_apply,e.symm_apply_apply]
  rw [hf] at hd
  change HasFDerivAt F
    ((coordinateDerivative d (D (e.symm (e p)))).comp e.toContinuousLinearMap) p at hd
  rw [e.symm_apply_apply] at hd
  change HasFDerivAt F ((coordinateDerivative d (D p)).comp e.toContinuousLinearMap) p
  exact hd

theorem euclideanContinuousPartials_continuousDerivative (d : ℕ)
    (F : EuclideanSpace ℝ (Fin d) → E) (D : EuclideanSpace ℝ (Fin d) → Fin d → E)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : IsOpen S)
    (hD : ∀ i, ContinuousOn (fun p => D p i) S)
    (hpartial : ∀ q ∈ S, ∀ i : Fin d,
      HasDerivAt (fun s : ℝ => F ((EuclideanSpace.equiv (Fin d) ℝ).symm
        (Function.update ((EuclideanSpace.equiv (Fin d) ℝ) q) i s))) (D q i) (q i)) :
    ContinuousOn (fderiv ℝ F) S := by
  have hc : ContinuousOn (fun q => euclideanCoordinateDerivative d (D q)) S :=
    (coordinateDerivative_continuousOn d D S hD).clm_comp continuousOn_const
  exact hc.congr (fun q hq => (euclideanContinuousPartials_hasFDerivAt d F D S hS hD hpartial q hq).fderiv)

end Froehlich
