import Froehlich.Nodes.MN02Reciprocal
import Froehlich.Nodes.DF01

/-! Full two-sided free resolvent, including its actual maximal domain. -/
noncomputable section
open MeasureTheory
namespace Froehlich

theorem freeReciprocalAction_graph (P : GW.Space) (lam : ℝ) (hl : lam < 1)
    (hv : lam ≠ ‖P‖^2) (f : GW.Fock.Carrier) :
    ∃ hu : freeReciprocalAction P lam hl f ∈ (freeFiberOperator P).domain,
      freeFiberOperator P ⟨freeReciprocalAction P lam hl f,hu⟩ =
        f + (lam : ℂ) • freeReciprocalAction P lam hl f := by
  apply (freeFiberOperator_domain_action_iff P _ _).mpr
  intro n
  have ha := freeReciprocalAction_ae P lam hl f n
  have hlin := Lp.coeFn_add (physicalSector n (f n))
    ((lam : ℂ) • physicalSector n (freeReciprocalAction P lam hl f n))
  have hs := Lp.coeFn_smul (lam : ℂ)
    (physicalSector n (freeReciprocalAction P lam hl f n))
  change _ =ᵐ[_] physicalSector n ((f + (lam : ℂ) • freeReciprocalAction P lam hl f) n)
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
    map_add, map_smul]
  filter_upwards [ha,hlin,hs] with k hk hsum hsmul
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply]
  rw [← hk]
  simp only [smul_eq_mul]
  have hn : (freeSymbol P n k : ℂ) - (lam : ℂ) ≠ 0 := by
    exact_mod_cast freeSymbol_sub_ne_zero P lam hl hv n k
  simp only [freeReciprocal, Complex.ofReal_inv, Complex.ofReal_sub]
  field_simp [hn] <;> ring

theorem freeReciprocalAction_isResolvent (P : GW.Space) (lam : ℝ) (hl : lam < 1)
    (hv : lam ≠ ‖P‖^2) :
    GW.Operators.IsResolvent (freeFiberOperator P) (lam : ℂ)
      (freeReciprocalAction P lam hl) where
  mem_domain f := (freeReciprocalAction_graph P lam hl hv f).choose
  left_inv f := by
    change freeFiberOperator P _ - (lam : ℂ) • freeReciprocalAction P lam hl f = f
    exact (congrArg (fun v : GW.Fock.Carrier => v - (lam : ℂ) • freeReciprocalAction P lam hl f)
      (freeReciprocalAction_graph P lam hl hv f).choose_spec).trans (add_sub_cancel_right _ _)
  right_inv u := by
    apply lp.ext
    funext n
    apply (physicalSector n).injective
    apply Lp.ext
    have ha := freeReciprocalAction_ae P lam hl
      (GW.Operators.complexShift (freeFiberOperator P) (lam : ℂ) u) n
    have hu := freeFiberOperator_ae P u n
    have he : physicalSector n ((GW.Operators.complexShift (freeFiberOperator P) (lam : ℂ) u) n) =
        physicalSector n (freeFiberOperator P u n) -
          (lam : ℂ) • physicalSector n ((u : GW.Fock.Carrier) n) := by
      change physicalSector n ((freeFiberOperator P u - (lam : ℂ) • (u : GW.Fock.Carrier)) n) = _
      simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, map_sub, map_smul]
    rw [he] at ha
    have hsub := Lp.coeFn_sub (physicalSector n (freeFiberOperator P u n))
      ((lam : ℂ) • physicalSector n ((u : GW.Fock.Carrier) n))
    have hsmul := Lp.coeFn_smul (lam : ℂ) (physicalSector n ((u : GW.Fock.Carrier) n))
    filter_upwards [ha,hu,hsub,hsmul] with k hk hu hs hm
    rw [← hk,hs]
    simp only [Pi.sub_apply]
    rw [hm]
    simp only [Pi.smul_apply]
    rw [← hu]
    simp only [smul_eq_mul, freeReciprocal, Complex.ofReal_inv, Complex.ofReal_sub]
    have hn : (freeSymbol P n k : ℂ) - (lam : ℂ) ≠ 0 := by
      exact_mod_cast freeSymbol_sub_ne_zero P lam hl hv n k
    field_simp [hn] <;> ring

end Froehlich
