import Froehlich.Nodes.CA01CoordinateIterates

/-! Ordered finite coordinate blocks: genuine mixed partial operators,
locality, and exact finite regularity loss. No commutation assumption is used. -/
noncomputable section
open Filter
open scoped Topology
namespace Froehlich
variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def coordinateBlocksPartial : List (Fin d × ℕ) → ((Fin d → ℝ) → V) → (Fin d → ℝ) → V
  | [], F => F
  | (i,n)::bs, F => coordinateIterate i n (coordinateBlocksPartial bs F)

def coordinateBlocksOrder : List (Fin d × ℕ) → ℕ
  | [] => 0
  | (_,n)::bs => n + coordinateBlocksOrder bs

theorem coordinateIterate_contDiffOn (i : Fin d) (k m : ℕ)
    (F : (Fin d → ℝ) → V) (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (m+k : ℕ) F S) :
    ContDiffOn ℝ m (coordinateIterate i k F) S := by
  induction k generalizing m with
  | zero => simpa only [Nat.add_zero,coordinateIterate_zero] using hF
  | succ k ih =>
    have heq : (m+1)+k = m+(k+1) := by omega
    have hf : ContDiffOn ℝ ((m+1)+k : ℕ) F S := by
      rw [heq]
      exact hF
    have hi := ih (m+1) hf
    rw [coordinateIterate_succ]
    exact coordinatePartial_contDiffOn i (coordinateIterate i k F) S hS m hi

theorem coordinateBlocksPartial_contDiffOn (bs : List (Fin d × ℕ)) (m : ℕ)
    (F : (Fin d → ℝ) → V) (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hF : ContDiffOn ℝ (m+coordinateBlocksOrder bs : ℕ) F S) :
    ContDiffOn ℝ m (coordinateBlocksPartial bs F) S := by
  induction bs generalizing m with
  | nil => simpa only [coordinateBlocksOrder,Nat.add_zero,coordinateBlocksPartial] using hF
  | cons b bs ih =>
    obtain ⟨i,k⟩ := b
    have heq : (m+k)+coordinateBlocksOrder bs = m+(k+coordinateBlocksOrder bs) := by omega
    have hf : ContDiffOn ℝ ((m+k)+coordinateBlocksOrder bs : ℕ) F S := by
      rw [heq]
      exact hF
    exact coordinateIterate_contDiffOn i k m (coordinateBlocksPartial bs F) S hS (ih (m+k) hf)

theorem coordinateIterate_congr_of_isOpen (i : Fin d) (k : ℕ)
    (F G : (Fin d → ℝ) → V) (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hFG : Set.EqOn F G S) : Set.EqOn (coordinateIterate i k F) (coordinateIterate i k G) S := by
  intro q hq
  have hmem : S ∈ 𝓝 (Function.update q i (q i)) := by
    simpa only [Function.update_eq_self] using hS.mem_nhds hq
  have hn := (hasDerivAt_update q i (q i)).continuousAt.preimage_mem_nhds hmem
  have he : (fun s : ℝ => F (Function.update q i s)) =ᶠ[𝓝 (q i)]
      (fun s : ℝ => G (Function.update q i s)) := by
    filter_upwards [hn] with s hs
    exact hFG hs
  rw [coordinateIterate_eq_iteratedDeriv,coordinateIterate_eq_iteratedDeriv]
  exact he.iteratedDeriv_eq k

theorem coordinateBlocksPartial_congr_of_isOpen (bs : List (Fin d × ℕ))
    (F G : (Fin d → ℝ) → V) (S : Set (Fin d → ℝ)) (hS : IsOpen S)
    (hFG : Set.EqOn F G S) : Set.EqOn (coordinateBlocksPartial bs F) (coordinateBlocksPartial bs G) S := by
  induction bs with
  | nil => exact hFG
  | cons b bs ih =>
    exact coordinateIterate_congr_of_isOpen b.1 b.2 _ _ S hS ih

/-- Source multi-index derivative, in increasing coordinate order. -/
def coordinateMultiPartial (alpha : Fin d → ℕ) (F : (Fin d → ℝ) → V) : (Fin d → ℝ) → V :=
  coordinateBlocksPartial (List.ofFn (fun i : Fin d => (i,alpha i))) F

end Froehlich
