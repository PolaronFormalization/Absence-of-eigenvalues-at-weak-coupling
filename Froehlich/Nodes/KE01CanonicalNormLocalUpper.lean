import Froehlich.Nodes.KE01CanonicalNorm
import Froehlich.Nodes.KE01CanonicalNormLocal

set_option autoImplicit false
noncomputable section
namespace Froehlich
variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coordinateWordPartial_contDiffOn (is : List (Fin d)) (F : (Fin d → ℝ) → V)
    (n : ℕ) (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (n+is.length : ℕ) F S) :
    ContDiffOn ℝ n (coordinateWordPartial is F) S := by
  induction is generalizing n with
  | nil => simpa only [List.length_nil,Nat.add_zero,coordinateWordPartial] using hF
  | cons i is ih =>
    have ht : ContDiffOn ℝ ((n+1)+is.length : ℕ) F S := by
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hF
    exact coordinatePartial_contDiffOn i _ S hS n (ih (n+1) ht)

theorem coordinatePartial_pair_fderiv_on (F : (Fin d → ℝ) → V)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S) (hF : ContDiffOn ℝ 2 F S)
    (i j : Fin d) (q : Fin d → ℝ) (hq : q ∈ S) :
    coordinatePartial i (coordinatePartial j F) q =
      fderiv ℝ (fderiv ℝ F) q (Pi.single i 1) (Pi.single j 1) := by
  have he : Set.EqOn (coordinatePartial j F) (fun p => fderiv ℝ F p (Pi.single j 1)) S := by
    intro p hp
    exact coordinatePartial_eq_fderiv j F p
      (((hF p hp).contDiffAt (hS.mem_nhds hp)).differentiableAt (by norm_num))
  have heq := coordinateIterate_congr_of_isOpen i 1 _ _ S hS he hq
  change coordinatePartial i (coordinatePartial j F) q =
    coordinatePartial i (fun p => fderiv ℝ F p (Pi.single j 1)) q at heq
  rw [heq]
  have hAt : ContDiffAt ℝ 2 F q := (hF q hq).contDiffAt (hS.mem_nhds hq)
  have hdd : DifferentiableAt ℝ (fderiv ℝ F) q :=
    (hAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hap : HasFDerivAt (fun p : Fin d → ℝ => fderiv ℝ F p (Pi.single j 1))
      ((ContinuousLinearMap.apply ℝ V (Pi.single j (1 : ℝ))).comp (fderiv ℝ (fderiv ℝ F) q)) q := by
    simpa only [Function.comp_def] using!
      ((ContinuousLinearMap.apply ℝ V (Pi.single j (1 : ℝ))).hasFDerivAt).comp q hdd.hasFDerivAt
  rw [coordinatePartial_eq_fderiv i _ q hap.differentiableAt,hap.fderiv]
  rfl

theorem coordinatePartial_comm_on (F : (Fin d → ℝ) → V)
    (S : Set (Fin d → ℝ)) (hS : IsOpen S) (hF : ContDiffOn ℝ 2 F S) (i j : Fin d) :
    Set.EqOn (coordinatePartial i (coordinatePartial j F))
      (coordinatePartial j (coordinatePartial i F)) S := by
  intro q hq
  rw [coordinatePartial_pair_fderiv_on F S hS hF i j q hq,
    coordinatePartial_pair_fderiv_on F S hS hF j i q hq]
  exact (((hF q hq).contDiffAt (hS.mem_nhds hq)).isSymmSndFDerivAt (by norm_num))
    (Pi.single i 1) (Pi.single j 1)

theorem coordinateWordPartial_perm_on {is js : List (Fin d)} (h : is.Perm js)
    (F : (Fin d → ℝ) → V) (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (is.length : ℕ) F S) :
    Set.EqOn (coordinateWordPartial is F) (coordinateWordPartial js F) S := by
  induction h with
  | nil => intro q _; rfl
  | @cons i is js h ih =>
    have ht : ContDiffOn ℝ (is.length : ℕ) F S := hF.of_le (by simp)
    intro q hq
    exact coordinateIterate_congr_of_isOpen i 1 _ _ S hS (ih ht) hq
  | swap i j is =>
    have hn : (2+is.length : ℕ) = (j::i::is).length := by simp only [List.length_cons]; omega
    have ht : ContDiffOn ℝ 2 (coordinateWordPartial is F) S :=
      coordinateWordPartial_contDiffOn is F 2 S hS (by rw [hn]; exact hF)
    exact coordinatePartial_comm_on _ S hS ht j i
  | @trans is js ks h1 h2 ih1 ih2 =>
    have ht : ContDiffOn ℝ (js.length : ℕ) F S := by simpa only [←h1.length_eq] using hF
    exact (ih1 hF).trans (ih2 ht)

theorem coordinateWordPartial_native_ofFn_on {k : ℕ} (is : Fin k → Fin d)
    (F : (Fin d → ℝ) → V) (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ k F S) (q : Fin d → ℝ) (hq : q ∈ S) :
    coordinateWordPartial (List.ofFn is) F q =
      iteratedFDeriv ℝ k F q (fun j => Pi.single (is j) 1) := by
  have hn := coordinateWordPartial_native_on (List.ofFn is) F S hS
    (by simpa only [List.length_ofFn] using hF) q hq
  have hdir : listDirections (fun i : Fin d => (Pi.single i 1 : Fin d → ℝ)) (List.ofFn is) =
      (fun j => (Pi.single (is (Fin.cast (by simp) j)) 1 : Fin d → ℝ)) := by
    funext j
    rw [listDirections_eq_get,List.get_ofFn]
  rw [hdir] at hn
  have hc (n : ℕ) (h : n = k) :
      iteratedFDeriv ℝ n F q (fun j => Pi.single (is (Fin.cast h j)) 1) =
        iteratedFDeriv ℝ k F q (fun j => Pi.single (is j) 1) := by
    subst n
    rfl
  exact hn.trans (hc _ List.length_ofFn)

/-- Local finite-dimensional norm reconstruction. Only ordinary finite C^k
regularity at the point and its actual canonical derivatives are used. -/
theorem iteratedFDeriv_norm_le_canonical_at (k : ℕ) (F : (Fin d → ℝ) → V)
    (q : Fin d → ℝ) (hF : ContDiffAt ℝ k F q) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ alpha : Fin d → ℕ, (∑ i, alpha i) = k →
      ‖coordinateMultiPartial alpha F q‖ ≤ K) :
    ‖iteratedFDeriv ℝ k F q‖ ≤ (d : ℝ)^k*K := by
  have hWithin : ContDiffWithinAt ℝ k F Set.univ q := hF.contDiffWithinAt
  have hfinite : (k : WithTop ENat) ≠ ((⊤ : ENat) : WithTop ENat) := by
    exact_mod_cast ENat.natCast_ne_top k
  obtain ⟨S,hS,hq,hOn⟩ := hWithin.contDiffOn' (m := k) le_rfl (fun h => False.elim (hfinite h))
  simp only [Set.insert_eq_of_mem (Set.mem_univ q),Set.univ_inter] at hOn
  apply multilinearMap_norm_le_coordinates d k _ K hK
  intro is
  rw [←coordinateWordPartial_native_ofFn_on is F S hS hOn q hq]
  let alpha : Fin d → ℕ := fun i => (List.ofFn is).count i
  have hp : (List.ofFn is).Perm (canonicalMultiIndexCoordinates alpha) :=
    coordinateWordPartial_canonical (List.ofFn is)
  have hdegree : (∑ i, alpha i) = k :=
    (canonicalMultiIndexCoordinates_length alpha).symm.trans
      (hp.length_eq.symm.trans (List.length_ofFn (f := is)))
  have hword := coordinateWordPartial_perm_on hp F S hS (by simpa only [List.length_ofFn] using hOn)
  rw [hword hq,←coordinateMultiPartial_word]
  exact hbound alpha hdegree

end Froehlich
