import Froehlich.Nodes.CA02TermData
import Froehlich.Nodes.CA01CoordinateIterates

/-! Finite source expansions are differentiated termwise, preserving the
literal degree invariant and the sum of absolute coefficients. -/
noncomputable section
namespace Froehlich
variable {d : ℕ}

def evalScalarTerms (ts : List (ScalarWeightTermData d)) (b : ℝ) (x : Fin d → ℝ) : ℝ :=
  (ts.map (fun t => t.eval b x)).sum

def deriveScalarTerms (i : Fin d) (ts : List (ScalarWeightTermData d)) : List (ScalarWeightTermData d) :=
  ts.flatMap (fun t => t.derive i)

theorem evalScalarTerms_append (ts us : List (ScalarWeightTermData d)) (b : ℝ) (x : Fin d → ℝ) :
    evalScalarTerms (ts++us) b x = evalScalarTerms ts b x + evalScalarTerms us b x := by
  simp only [evalScalarTerms,List.map_append,List.sum_append]

theorem scalarTermMass_append (ts us : List (ScalarWeightTermData d)) :
    scalarTermMass (ts++us) = scalarTermMass ts + scalarTermMass us := by
  simp only [scalarTermMass,List.map_append,List.sum_append]

theorem scalarTermMass_cons (t : ScalarWeightTermData d) (ts : List (ScalarWeightTermData d)) :
    scalarTermMass (t::ts) = |t.coefficient|+scalarTermMass ts := rfl

theorem evalScalarTerms_cons (t : ScalarWeightTermData d) (ts : List (ScalarWeightTermData d))
    (b : ℝ) (x : Fin d → ℝ) : evalScalarTerms (t::ts) b x = t.eval b x + evalScalarTerms ts b x := rfl

theorem scalarWeightTermData_hasDerivAt_update (t : ScalarWeightTermData d)
    (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun s : ℝ => t.eval b (Function.update x i s))
      (evalScalarTerms (t.derive i) b x) (x i) := by
  have hd := scalarWeightTerm_hasDerivAt_update t.coefficient t.powers t.shift b hb x i
  by_cases hi : t.powers i = 0
  · have hl : scalarWeightTerm (t.coefficient*(t.powers i : ℝ))
        (Function.update t.powers i (t.powers i-1)) t.shift b x = 0 := by
      simp only [hi,Nat.cast_zero,mul_zero,scalarWeightTerm,zero_mul,zero_div]
    rw [hl,zero_add] at hd
    simpa only [ScalarWeightTermData.eval,ScalarWeightTermData.derive,if_pos hi,
      evalScalarTerms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      ScalarWeightTermData.raise] using hd
  · simpa only [ScalarWeightTermData.eval,ScalarWeightTermData.derive,if_neg hi,
      evalScalarTerms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      ScalarWeightTermData.raise,ScalarWeightTermData.lower] using hd

theorem evalScalarTerms_hasDerivAt_update (ts : List (ScalarWeightTermData d))
    (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun s : ℝ => evalScalarTerms ts b (Function.update x i s))
      (evalScalarTerms (deriveScalarTerms i ts) b x) (x i) := by
  induction ts with
  | nil => simpa only [evalScalarTerms,deriveScalarTerms,List.flatMap_nil,List.map_nil,List.sum_nil]
      using hasDerivAt_const (x i) (0 : ℝ)
  | cons t ts ih =>
    simpa only [evalScalarTerms_cons,deriveScalarTerms,List.flatMap_cons,evalScalarTerms_append]
      using (scalarWeightTermData_hasDerivAt_update t b hb x i).fun_add ih

theorem deriveScalarTerms_admissible (ts : List (ScalarWeightTermData d)) (r : ℕ)
    (hts : ∀ t ∈ ts, t.Admissible r) (i : Fin d) :
    ∀ u ∈ deriveScalarTerms i ts, u.Admissible (r+1) := by
  intro u hu
  obtain ⟨t,ht,hu⟩ := List.mem_flatMap.mp hu
  exact t.derive_admissible r (hts t ht) i u hu

theorem deriveScalarTerms_mass_le (ts : List (ScalarWeightTermData d)) (r : ℕ)
    (hts : ∀ t ∈ ts, t.Admissible r) (i : Fin d) :
    scalarTermMass (deriveScalarTerms i ts) ≤ (3*(r : ℝ)+1)*scalarTermMass ts := by
  induction ts with
  | nil => simp only [deriveScalarTerms,List.flatMap_nil,scalarTermMass,List.map_nil,List.sum_nil,mul_zero,le_rfl]
  | cons t ts ih =>
    have ht := hts t (List.mem_cons_self ..)
    have htail : ∀ u ∈ ts, u.Admissible r := fun u hu => hts u (List.mem_cons_of_mem _ hu)
    change scalarTermMass (t.derive i ++ deriveScalarTerms i ts) ≤ _
    rw [scalarTermMass_append,scalarTermMass_cons]
    calc
      _ ≤ (3*(r : ℝ)+1)*|t.coefficient| + (3*(r : ℝ)+1)*scalarTermMass ts :=
        add_le_add (t.derive_mass_le r ht i) (ih htail)
      _ = _ := by ring

theorem evalScalarTerms_relative_bound (ts : List (ScalarWeightTermData d)) (r : ℕ)
    (hts : ∀ t ∈ ts, t.Admissible r) (b : ℝ) (hb : 1 ≤ b) (x : Fin d → ℝ) :
    |evalScalarTerms ts b x| ≤ scalarTermMass ts * scalarInverseRootWeight b x := by
  induction ts with
  | nil => simp only [evalScalarTerms,scalarTermMass,List.map_nil,List.sum_nil,abs_zero,zero_mul,le_rfl]
  | cons t ts ih =>
    have ht := hts t (List.mem_cons_self ..)
    have htail : ∀ u ∈ ts, u.Admissible r := fun u hu => hts u (List.mem_cons_of_mem _ hu)
    have hdeg : (∑ k, t.powers k) ≤ 2*t.shift := by have h := ht.1; omega
    rw [evalScalarTerms_cons,scalarTermMass_cons]
    calc
      _ ≤ |t.eval b x| + |evalScalarTerms ts b x| := abs_add_le _ _
      _ ≤ |t.coefficient| *scalarInverseRootWeight b x + scalarTermMass ts*scalarInverseRootWeight b x :=
        add_le_add (scalarWeightTerm_relative_bound t.coefficient t.powers t.shift b hb x hdeg) (ih htail)
      _ = _ := by ring

end Froehlich
