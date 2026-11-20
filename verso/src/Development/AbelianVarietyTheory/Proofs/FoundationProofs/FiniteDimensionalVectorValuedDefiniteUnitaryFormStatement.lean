import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalVectorValuedDefiniteUnitaryForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFiniteDimensionalVectorValuedDefiniteUnitaryForm.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_vectorValued_definiteUnitaryForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧ ∀ k ∈ K, ∀ v, RU E n (k : UA E n) (f v) = f v) → FiniteDimensional ℂ M := by
  first | exact @GlobalTheory.DefU.finiteDimensional_vecForms | exact GlobalTheory.DefU.finiteDimensional_vecForms | (intros; apply GlobalTheory.DefU.finiteDimensional_vecForms <;> assumption)
