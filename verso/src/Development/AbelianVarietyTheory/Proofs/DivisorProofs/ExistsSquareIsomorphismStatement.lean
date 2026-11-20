import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareIsomorphism
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSquareIsomorphism.lean&line=195#L195)
-/
theorem _root_.GlobalTheory.T.exists_square_isomorphism : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), IsFactor B τ (stdLat g) j → (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → IsRigidification B r → InducesPolarisation B τ (stdLat g) j → ∀ n : ℤ, ∃ φ, IsSquareIso B τ j r n φ := by
  first | exact @GlobalTheory.SquareIso.exists_squareIso | exact GlobalTheory.SquareIso.exists_squareIso | (intros; apply GlobalTheory.SquareIso.exists_squareIso <;> assumption)
