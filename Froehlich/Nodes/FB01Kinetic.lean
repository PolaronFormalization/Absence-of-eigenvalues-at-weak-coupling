import Froehlich.Nodes.FC07Momentum
import Froehlich.Nodes.FC01Lifts

/-! Actual shifted momentum components on the core and their free-energy
control, used in the finite-cutoff Lieb--Yamazaki calculation. -/
noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal
namespace Froehlich

theorem fockRealMultiplier_sector_norm_sq
    (m : ∀ n, GW.Fock.Coordinates n → ℝ) (u v : GW.Fock.Carrier)
    (hg : (u,v) ∈ (fockRealMultiplier m).graph) (n : ℕ) :
    Integrable (fun K => m n K ^ 2 * ‖physicalSector n (u n) K‖^2) (GW.Fock.sectorMeasure n) ∧
      ‖v n‖^2 = ∫ K, m n K ^ 2 * ‖physicalSector n (u n) K‖^2 ∂GW.Fock.sectorMeasure n := by
  have ha := (fockRealMultiplier_graph_ae_iff m u v).mp hg n
  have he : (fun K => ‖physicalSector n (v n) K‖^2) =ᵐ[GW.Fock.sectorMeasure n]
      (fun K => m n K ^ 2 * ‖physicalSector n (u n) K‖^2) := by
    filter_upwards [ha] with K hk
    rw [← hk, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨((Lp.memLp (physicalSector n (v n))).integrable_norm_pow (p := 2) (by norm_num)).congr he, ?_⟩
  rw [← (physicalSector n).norm_map (v n), GW.Analysis.l2_norm_sq (𝕜 := ℂ)]
  exact integral_congr_ae he

theorem fockRealMultiplier_shift_graph
    (m : ∀ n, GW.Fock.Coordinates n → ℝ) (c : ℝ) (u v : GW.Fock.Carrier)
    (hg : (u,v) ∈ (fockRealMultiplier m).graph) :
    (u,v-(c : ℂ) • u) ∈ (fockRealMultiplier (fun n K => m n K-c)).graph := by
  apply (fockRealMultiplier_graph_ae_iff _ _ _).mpr
  intro n
  have ha := (fockRealMultiplier_graph_ae_iff m u v).mp hg n
  have he : physicalSector n ((v-(c : ℂ) • u) n) =
      physicalSector n (v n) - (c : ℂ) • physicalSector n (u n) := by
    change physicalSector n (v n - (c : ℂ) • u n) = _
    rw [map_sub,map_smul]
  rw [he]
  filter_upwards [ha, Lp.coeFn_sub (physicalSector n (v n)) ((c : ℂ) • physicalSector n (u n)),
    Lp.coeFn_smul (c : ℂ) (physicalSector n (u n))] with K hk hsub hsmul
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul
  rw [hsub,hsmul,← hk]
  simp only [smul_eq_mul, Complex.ofReal_sub]
  ring

def coreKineticComponent (P : GW.Space) (a : Fin 3) (u : boundedMomentumCore) : GW.Fock.Carrier :=
  (coreMomentumAction a u : GW.Fock.Carrier) - (P a : ℂ) • (u : GW.Fock.Carrier)

theorem coreKineticComponent_graph (P : GW.Space) (a : Fin 3) (u : boundedMomentumCore) :
    ((u : GW.Fock.Carrier),coreKineticComponent P a u) ∈
      (fockRealMultiplier (fun n K => totalMomentum n K a-P a)).graph :=
  fockRealMultiplier_shift_graph (fun n K => totalMomentum n K a) (P a)
    (u : GW.Fock.Carrier) (coreMomentumAction a u) (coreMomentumAction_graph a u)

theorem coreKineticComponent_sector_bound (P : GW.Space) (u : boundedMomentumCore) (n : ℕ) :
    (∑ a : Fin 3, ‖coreKineticComponent P a u n‖^2) ≤
      freeSectorEnergy P n ((u : GW.Fock.Carrier) n) := by
  have hi (a : Fin 3) := fockRealMultiplier_sector_norm_sq
    (fun n K => totalMomentum n K a-P a) (u : GW.Fock.Carrier)
    (coreKineticComponent P a u) (coreKineticComponent_graph P a u) n
  have hfree := freeSectorEnergy_integrable P (coreEnergyLift P u) n
  rw [coreEnergyLift_embedding] at hfree
  calc
    _ = ∑ a : Fin 3, ∫ K, (totalMomentum n K a-P a)^2 *
        ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2 ∂GW.Fock.sectorMeasure n :=
      Finset.sum_congr rfl (fun a _ => (hi a).2)
    _ = ∫ K, ∑ a : Fin 3, (totalMomentum n K a-P a)^2 *
        ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2 ∂GW.Fock.sectorMeasure n :=
      (integral_finsetSum Finset.univ (fun a _ => (hi a).1)).symm
    _ ≤ _ := by
      apply integral_mono (integrable_finsetSum Finset.univ (fun a _ => (hi a).1)) hfree
      intro K
      change (∑ a : Fin 3, (totalMomentum n K a-P a)^2 *
        ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2) ≤
          freeSymbol P n K * ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖^2
      rw [← Finset.sum_mul]
      have he : (∑ a : Fin 3, (totalMomentum n K a-P a)^2) = ‖totalMomentum n K-P‖^2 := by
        simpa using (EuclideanSpace.real_norm_sq_eq (totalMomentum n K-P)).symm
      rw [he]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg n))
        (sq_nonneg ‖physicalSector n ((u : GW.Fock.Carrier) n) K‖)

theorem coreKineticComponent_bound (P : GW.Space) (u : boundedMomentumCore) :
    (∑ a : Fin 3, ‖coreKineticComponent P a u‖^2) ≤ freeEnergy P (u : GW.Fock.Carrier) := by
  have hf := freeSectorEnergy_summable P (coreEnergyLift P u)
  rw [coreEnergyLift_embedding] at hf
  have hs : Summable (fun n => ∑ a : Fin 3, ‖coreKineticComponent P a u n‖^2) :=
    Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (coreKineticComponent_sector_bound P u) hf
  have hn (a : Fin 3) : Summable (fun n => ‖coreKineticComponent P a u n‖^2) :=
    (GW.Analysis.memℓp_two_iff_sq _).mp (coreKineticComponent P a u).property
  have he : (∑' n, ∑ a : Fin 3, ‖coreKineticComponent P a u n‖^2) =
      ∑ a : Fin 3, ‖coreKineticComponent P a u‖^2 := by
    rw [Summable.tsum_finsetSum (fun a _ => hn a)]
    simp_rw [← GW.Fock.carrier_norm_sq]
  rw [← he]
  exact Summable.tsum_le_tsum (coreKineticComponent_sector_bound P u) hs hf

end Froehlich
