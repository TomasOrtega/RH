import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordInertDichotomy
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTwistedDualSizeWordInertDichotomy.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.twistedDualSizeWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 11 ≤ l → ψ.1.2 = -1 → WordsNT (recWord L j ε g) ∨ ∃ d, WordsAT l (recWord L j ε g) d := by
  first | exact @GlobalTheory.HTW.Rec.recWord_dichotomy | exact GlobalTheory.HTW.Rec.recWord_dichotomy | (intros; apply GlobalTheory.HTW.Rec.recWord_dichotomy <;> assumption)
