import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotient
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiltrationUniqueSubquotient.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.filtration_unique_subquotient : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ) (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ t₀ : Fin N, (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) → (∀ t : Fin N, t ≠ t₀ → ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) → ∀ φ ψ : π.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  first | exact @GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | exact GlobalTheory.CompanionTheory.Filtration.intertwining_proportional | (intros; apply GlobalTheory.CompanionTheory.Filtration.intertwining_proportional <;> assumption)
