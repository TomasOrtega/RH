import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardCrossingSetEqGrassmannianDim
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagCurve.card_crSet_eq_dimGr` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCardCrossingSetEqGrassmannianDim.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.card_crossing_set_eq_grassmannian_dim : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ), j ≤ N → (crSet ι N j).card = dimGr ι N j := by
  first | exact @GlobalTheory.FlagCurve.card_crSet_eq_dimGr | exact GlobalTheory.FlagCurve.card_crSet_eq_dimGr | (intros; apply GlobalTheory.FlagCurve.card_crSet_eq_dimGr <;> assumption)
