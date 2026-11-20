import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowerEmbedding
import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrobeniusPowerEmbedding.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.frobenius_power_embedding : ∀ (D : D7) (p : ℕ) [Fact p.Prime], UnramE D p → ∀ τ : Emb D p, phiPow D 1 τ = τ.comp (D.host.sigmaOf (frobG D p) : D.host.E →+* D.host.E) := by
  first | exact @GlobalTheory.FrobEmb.phiPow_one_eq | exact GlobalTheory.FrobEmb.phiPow_one_eq | (intros; apply GlobalTheory.FrobEmb.phiPow_one_eq <;> assumption)
