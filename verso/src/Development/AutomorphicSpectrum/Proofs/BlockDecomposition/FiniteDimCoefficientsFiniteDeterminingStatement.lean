import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimCoefficientsFiniteDetermining
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteDimCoefficientsFiniteDetermining.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.finite_dim_coefficients_finite_determining : ∀ (K W : Type) [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), ∃ S : Finset K, ∀ c ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, (∀ κ ∈ S, c κ = 0) → c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent | exact GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent | (intros; apply GlobalTheory.CompanionTheory.CTFin.UniSol.coeffSpan_unisolvent <;> assumption)
