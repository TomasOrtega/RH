import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConcretePeriodDatumPadicFiniteExtension
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsConcretePeriodDatumPadicFiniteExtension.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.exists_concretePeriodDatum_padicFiniteExtension : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l), ∃ PD, IsRealPD C K PD := by
  first | exact @GlobalTheory.MemLoc.PdEx.exists_realPD | exact GlobalTheory.MemLoc.PdEx.exists_realPD | (intros; apply GlobalTheory.MemLoc.PdEx.exists_realPD <;> assumption)
