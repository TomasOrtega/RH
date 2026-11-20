import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open Formalism.MainNotions.S Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.hilbert_schur` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FHilbertSchurUnitaryIrreducibleScalar.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.hilbert_schur_unitary_irreducible_scalar : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)), (∀ g v, ‖π g v‖ = ‖v‖) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, π g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ A : H →L[ℂ] H, (∀ g, π g * A = A * π g) → ∃ c : ℂ, A = c • (1 : H →L[ℂ] H) := by
  first | exact @GlobalTheory.hilbert_schur | exact GlobalTheory.hilbert_schur | (intros; apply GlobalTheory.hilbert_schur <;> assumption)
