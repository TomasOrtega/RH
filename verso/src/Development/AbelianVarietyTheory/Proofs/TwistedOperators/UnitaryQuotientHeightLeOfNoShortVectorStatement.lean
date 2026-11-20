import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightLeOfNoShortVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VsizeNonneg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryQuotientHeightLeOfNoShortVector.lean&line=240#L240)
-/
theorem _root_.GlobalTheory.T.unitaryQuotientHeight_le_of_no_short_vector : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (b : ℕ), ∀ (g : GA D V) (t : ℝ), 0 < t → t ≤ 1 → (∀ ξ : Fin V.rank → D.host.E, ξ ≠ 0 → t ≤ GlobalTheory.HtOrth.vsize (GlobalTheory.HtOrth.seen V g ξ)) → GlobalTheory.Grow.quotHeight V g * t ^ b ≤ C := by
  first | exact @GlobalTheory.HtMahler.quotHeight_le_of_no_short | exact GlobalTheory.HtMahler.quotHeight_le_of_no_short | (intros; apply GlobalTheory.HtMahler.quotHeight_le_of_no_short <;> assumption)
