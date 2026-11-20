import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralMatricesSeparatingRationalPairing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsIntegralMatricesSeparatingRationalPairing.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.exists_integral_matrices_separating_rationalPairing : ∀ (D : D7) (W : HSp D) (r : ℕ), ∃ (n : ℕ) (X : Fin n → Matrix (Fin W.rank) (Fin r) D.host.E), (∀ j a b, IsIntegral ℤ (X j a b)) ∧ ∀ y y' : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ j, ratPair W y (X j) = ratPair W y' (X j)) → y = y' := by
  first | exact @GlobalTheory.RatPairSep.main | exact GlobalTheory.RatPairSep.main | (intros; apply GlobalTheory.RatPairSep.main <;> assumption)
