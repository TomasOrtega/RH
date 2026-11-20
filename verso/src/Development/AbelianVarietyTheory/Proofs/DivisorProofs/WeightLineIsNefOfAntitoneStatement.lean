import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLineIsNefOfAntitone
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
open GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagZ.WtNef.wtLine_isNef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWeightLineIsNefOfAntitone.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.weight_line_isNef_of_antitone : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ) (lam : ι → Fin N → ℤ), (∀ τ (a b : Fin N), a ≤ b → lam τ b ≤ lam τ a) → (wtLine lam).IsNef (dimFl ι N) := by
  first | exact @GlobalTheory.FlagZ.WtNef.wtLine_isNef | exact GlobalTheory.FlagZ.WtNef.wtLine_isNef | (intros; apply GlobalTheory.FlagZ.WtNef.wtLine_isNef <;> assumption)
