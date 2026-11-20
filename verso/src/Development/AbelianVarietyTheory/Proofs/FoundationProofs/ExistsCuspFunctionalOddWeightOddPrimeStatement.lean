import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrime
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsCuspFunctionalOddWeightOddPrime.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ ∧ IsLat 1 φ := by
  first | exact @GlobalTheory.ThEx.thex | exact GlobalTheory.ThEx.thex | (intros; apply GlobalTheory.ThEx.thex <;> assumption)
