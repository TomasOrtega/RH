import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ScalarAnnih.exists_compact_of_annih` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsCompactAnnihilatorFiniteAdelesStdChar.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ O ∈ nhds (0 : Af D.host.F), ∃ K : Set (Af D.host.F), IsCompact K ∧ ∀ x : Af D.host.F, (∀ t ∈ O, ψ (pairA D.host.F 0 (t * x)) = 1) → x ∈ K := by
  first | exact @GlobalTheory.ScalarAnnih.exists_compact_of_annih | exact GlobalTheory.ScalarAnnih.exists_compact_of_annih | (intros; apply GlobalTheory.ScalarAnnih.exists_compact_of_annih <;> assumption)
