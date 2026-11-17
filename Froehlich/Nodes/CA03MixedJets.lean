import Froehlich.Nodes.CA03SingleDifference

/-! Ordered selected mixed directional jets suffice for the full finite-difference
estimate. Only distinct lists of the selected directions are differentiated; no
bound on repeated or unselected derivatives is assumed. -/
noncomputable section
namespace Froehlich
variable {ι D V : Type*} [DecidableEq ι]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def iteratedFiniteDifference (v : ι → D) : List ι → (D → V) → D → V
  | [], F => F
  | i::is, F => finiteDifference (v i) (iteratedFiniteDifference v is F)

theorem iteratedFiniteDifference_hasDerivAt (v : ι → D) (is : List ι)
    (F G : D → V) (h : D)
    (hd : ∀ x t, HasDerivAt (fun s : ℝ => F (x+s • h)) (G (x+t • h)) t)
    (x : D) (t : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFiniteDifference v is F (x+s • h))
      (iteratedFiniteDifference v is G (x+t • h)) t := by
  induction is generalizing x with
  | nil => exact hd x t
  | cons i is ih =>
    convert (ih (x+v i)).sub (ih x) using 1 <;>
      simp only [iteratedFiniteDifference,finiteDifference,add_assoc,add_left_comm,add_comm]
    rfl

theorem norm_finiteDifference_of_directionalDerivative
    (F G : D → V) (h : D) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h0 : ∀ x, ‖F x‖ ≤ K) (h1 : ∀ x, ‖G x‖ ≤ K*c)
    (hd : ∀ x t, HasDerivAt (fun s : ℝ => F (x+s • h)) (G (x+t • h)) t)
    (x : D) : ‖finiteDifference h F x‖ ≤ 2*K*min c 1 := by
  have hs : ‖finiteDifference h F x‖ ≤ K*c := by
    have hv := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (hd x t).hasDerivWithinAt) (fun t ht => h1 (x+t • h))
    simpa only [finiteDifference,one_smul,zero_smul,add_zero] using hv
  have hl : ‖finiteDifference h F x‖ ≤ 2*K :=
    (norm_sub_le _ _).trans (by linarith [h0 (x+h),h0 x])
  by_cases hh : c ≤ 1
  · rw [min_eq_left hh]
    exact hs.trans (by nlinarith)
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hh)),mul_one]
    exact hl

theorem norm_iteratedFiniteDifference_of_mixedJets
    (T : Finset ι) (v : ι → D) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (J : List ι → D → V) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ A, A.Nodup → (∀ i ∈ A, i ∈ T) → ∀ x,
      ‖J A x‖ ≤ M * (A.map c).prod)
    (hderiv : ∀ A, A.Nodup → (∀ j ∈ A, j ∈ T) → ∀ i ∈ T, i ∉ A → ∀ x t,
      HasDerivAt (fun s : ℝ => J A (x+s • v i)) (J (i::A) (x+t • v i)) t)
    (is : List ι) (hnodup : is.Nodup) (hmem : ∀ i ∈ is, i ∈ T)
    (A : List ι) (hAnodup : A.Nodup) (hA : ∀ i ∈ A, i ∈ T)
    (hdisjoint : ∀ i ∈ is, i ∉ A) (x : D) :
    ‖iteratedFiniteDifference v is (J A) x‖ ≤
      2^is.length * M * (A.map c).prod * (is.map (fun i => min (c i) 1)).prod := by
  induction is generalizing A x with
  | nil => simpa only [iteratedFiniteDifference,List.length_nil,pow_zero,one_mul,
      List.map_nil,List.prod_nil,mul_one] using hbound A hAnodup hA x
  | cons i is ih =>
    obtain ⟨hinot,htail⟩ := List.nodup_cons.mp hnodup
    have hiT : i ∈ T := hmem i (List.mem_cons_self ..)
    have hiA : i ∉ A := hdisjoint i (List.mem_cons_self ..)
    have hmemtail : ∀ j ∈ is, j ∈ T := fun j hj => hmem j (List.mem_cons_of_mem _ hj)
    have hdistail : ∀ j ∈ is, j ∉ A := fun j hj => hdisjoint j (List.mem_cons_of_mem _ hj)
    have hdins : ∀ j ∈ is, j ∉ i::A := by
      intro j hj
      simp only [List.mem_cons]
      rintro (hji|hjA)
      · exact hinot (hji ▸ hj)
      · exact hdistail j hj hjA
    have hAmem : ∀ j ∈ i::A, j ∈ T := by
      intro j hj
      rcases List.mem_cons.mp hj with hji|hjA
      · exact hji ▸ hiT
      · exact hA j hjA
    let K : ℝ := 2^is.length * M * (A.map c).prod * (is.map (fun j => min (c j) 1)).prod
    have hpA : 0 ≤ (A.map c).prod := by
      apply List.prod_nonneg
      intro b hb
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
      exact hc j
    have hpis : 0 ≤ (is.map (fun j => min (c j) 1)).prod := by
      apply List.prod_nonneg
      intro b hb
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
      exact le_min (hc j) zero_le_one
    have hK : 0 ≤ K := mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM) hpA) hpis
    have h0 : ∀ y, ‖iteratedFiniteDifference v is (J A) y‖ ≤ K := by
      intro y
      exact ih htail hmemtail A hAnodup hA hdistail y
    have h1 : ∀ y, ‖iteratedFiniteDifference v is (J (i::A)) y‖ ≤ K*c i := by
      intro y
      have hb := ih htail hmemtail (i::A) (List.nodup_cons.mpr ⟨hiA,hAnodup⟩) hAmem hdins y
      simp only [List.map_cons,List.prod_cons] at hb
      convert hb using 1 <;> dsimp [K] <;> ring
    have hd := iteratedFiniteDifference_hasDerivAt v is (J A) (J (i::A)) (v i)
      (hderiv A hAnodup hA i hiT hiA)
    have hb := norm_finiteDifference_of_directionalDerivative
      (iteratedFiniteDifference v is (J A)) (iteratedFiniteDifference v is (J (i::A)))
      (v i) K (c i) hK (hc i) h0 h1 hd x
    change ‖finiteDifference (v i) (iteratedFiniteDifference v is (J A)) x‖ ≤ _
    rw [List.length_cons,List.map_cons,List.prod_cons,pow_succ]
    convert hb using 1 <;> dsimp [K] <;> ring

end Froehlich
