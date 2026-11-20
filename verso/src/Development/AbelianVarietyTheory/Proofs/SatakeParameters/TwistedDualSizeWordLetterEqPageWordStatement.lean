import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWord
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTwistedDualSizeWordLetterEqPageWord.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ ψ : D.R.GG), Roomy L C → ∀ a : ZMod (orderOf ψ), (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a ∧ (recWord L j ε (letter τ ψ)).Mi a = (pageWord L j ε τ ψ).Mi a ∧ (recWord L j ε (letter τ ψ)).hi a = (pageWord L j ε τ ψ).hi a ∧ (ThickN (bHat L) (etaHat L) (recWord L j ε (letter τ ψ)).sz a ↔ (pageWord L j ε τ ψ).thick a) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | exact GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | (intros; apply GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord <;> assumption)
