import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterGrLineShiftCoordinate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
open GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagZ.isSelfInter_comb_grLine_shift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSelfInterGrLineShiftCoordinate.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.selfInter_grLine_shift_coordinate : Hypotheses2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι) (n : ι × Fin N → ℤ) (t : ℤ) (a : ℝ), (comb (grLine (ι := ι) (N := N)) n).IsSelfInter a → (comb (grLine (ι := ι) (N := N)) fun x => n x + if x.1 = τ then t else 0).IsSelfInter a := by
  first | exact @GlobalTheory.FlagZ.isSelfInter_comb_grLine_shift | exact GlobalTheory.FlagZ.isSelfInter_comb_grLine_shift | (intros; apply GlobalTheory.FlagZ.isSelfInter_comb_grLine_shift <;> assumption)
