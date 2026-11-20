import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordBoxesAndSizes
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.Rec.recWord_wordBox` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTwistedDualSizeWordBoxesAndSizes.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.twistedDualSizeWord_boxesAndSizes : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_wordBox | exact GlobalTheory.HTW.Rec.recWord_wordBox | (intros; apply GlobalTheory.HTW.Rec.recWord_wordBox <;> assumption)
