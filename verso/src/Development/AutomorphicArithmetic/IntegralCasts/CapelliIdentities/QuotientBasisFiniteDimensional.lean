import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.QuotientBasisFiniteDimensional.qb_fd :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {ι : Type} [Finite ι]
    (f : ι → PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] ↥K ∧ ∀ (i : ι), f i ∈ K := by
  intro l _ ι _ f
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range f), ?_, fun i =>
    IntermediateField.subset_adjoin ℚ_[l] (Set.range f) ⟨i, rfl⟩⟩
  haveI : Finite (Set.range f) := (Set.finite_range f).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ =>
    Algebra.IsIntegral.isIntegral x
