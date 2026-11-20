import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDominantHighestVectorOfLtStable
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Alc.exists_dominant_highest_vector_of_lt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsDominantHighestVectorOfLtStable.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable : ∀ (k : Type) [Field k] (N : ℕ) (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)), Good M → Good M' → M < M' → (∃ c : ℕ, ∀ f ∈ M', ∀ m ∈ f.support, ∑ a, rowDeg m a ≤ c) → ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), Antitone μ ∧ v ∈ M' ∧ v ∉ M ∧ IsWeightedHomogeneous (rowW N N) v μ ∧ ∀ a b, a < b → rowE k N N a b v ∈ M := by
  first | exact @GlobalTheory.Alc.exists_dominant_highest_vector_of_lt | exact GlobalTheory.Alc.exists_dominant_highest_vector_of_lt | (intros; apply GlobalTheory.Alc.exists_dominant_highest_vector_of_lt <;> assumption)
