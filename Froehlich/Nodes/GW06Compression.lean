import Froehlich.Nodes.GW06Sectors

/-! Actual associated operators on the closed particle-sector subspaces. -/
noncomputable section
open scoped InnerProductSpace
namespace Froehlich

theorem highEnergyEmbedding_injective (P : GW.Space) (n : ℕ) :
    Function.Injective (highEnergyEmbedding P n) := by
  intro u v h
  apply Subtype.ext
  apply energyEmbedding_injective P
  exact congrArg (fun x : HighSectorSpace n => (x : GW.Fock.Carrier)) h

theorem highEnergyEmbedding_dense (P : GW.Space) (n : ℕ) : DenseRange (highEnergyEmbedding P n) := by
  have hd : DenseRange (fun x : EnergySpace P => highSectorProject n (energyEmbedding P x)) :=
    (highSectorProject_surjective n).denseRange.comp (energyEmbedding_dense P) (highSectorProject n).continuous
  have he (x : EnergySpace P) :
      highEnergyEmbedding P n (highEnergyProject P n x) = highSectorProject n (energyEmbedding P x) := by
    apply Subtype.ext
    exact energyHighProjection_intertwines P n x
  have hs : Set.range (fun x : EnergySpace P => highSectorProject n (energyEmbedding P x)) ⊆
      Set.range (highEnergyEmbedding P n) := by
    rintro y ⟨x,rfl⟩
    exact ⟨highEnergyProject P n x,he x⟩
  exact Dense.mono hs hd

def compressedFiberFormData (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) :
    GW.Operators.CoerciveFormData (HighEnergySpace P n) (HighSectorSpace n) where
  embedding := highEnergyEmbedding P n
  embedding_injective := highEnergyEmbedding_injective P n
  embedding_dense := highEnergyEmbedding_dense P n
  form := ((fiberFormData g P i).form.comp (HighEnergySpace P n).subtype).compl₂ (HighEnergySpace P n).subtype
  hermitian w u := (fiberFormData g P i).hermitian w u
  continuous_form := by
    have h₁ : Continuous (fun q : HighEnergySpace P n × HighEnergySpace P n => (q.1 : EnergySpace P)) :=
      continuous_subtype_val.comp continuous_fst
    have h₂ : Continuous (fun q : HighEnergySpace P n × HighEnergySpace P n => (q.2 : EnergySpace P)) :=
      continuous_subtype_val.comp continuous_snd
    change Continuous (fun q : HighEnergySpace P n × HighEnergySpace P n =>
      (⟪(q.1 : EnergySpace P),(q.2 : EnergySpace P)⟫_ℂ -
        ⟪energyEmbedding P (q.1 : EnergySpace P),energyEmbedding P (q.2 : EnergySpace P)⟫_ℂ) +
      ⟪(q.1 : EnergySpace P),GW.Operators.uniformIndexOperator (fiberUniformData g P) i (q.2 : EnergySpace P)⟫_ℂ)
    exact ((h₁.inner h₂).sub (((energyEmbedding P).continuous.comp h₁).inner
      ((energyEmbedding P).continuous.comp h₂))).add
        (h₁.inner ((GW.Operators.uniformIndexOperator (fiberUniformData g P) i).continuous.comp h₂))
  shift := (fiberFormData g P i).shift
  lower := (fiberFormData g P i).lower
  upper := (fiberFormData g P i).upper
  lower_pos := (fiberFormData g P i).lower_pos
  lower_le_upper := (fiberFormData g P i).lower_le_upper
  lower_bound u := (fiberFormData g P i).lower_bound u
  upper_bound u := (fiberFormData g P i).upper_bound u

def compressedHamiltonian (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) : HighSectorSpace n →ₗ.[ℂ] HighSectorSpace n :=
  GW.Operators.formOperator (compressedFiberFormData g P n i)

theorem compressedHamiltonian_selfadjoint (g : ℝ) (P : GW.Space) (n : ℕ)
    (i : Option GW.Operators.PositiveCutoff) :
    GW.IsSelfAdjointOperator (compressedHamiltonian g P n i) :=
  GW.Operators.formOperator_selfadjoint (compressedFiberFormData g P n i)

end Froehlich
