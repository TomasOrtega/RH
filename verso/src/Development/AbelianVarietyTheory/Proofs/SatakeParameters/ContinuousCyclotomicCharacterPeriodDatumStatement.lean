import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCyclotomicCharacterPeriodDatum
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FContinuousCyclotomicCharacterPeriodDatum.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.continuous_cyclotomicCharacter_periodDatum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l), Continuous (fun s => ((cycLL (P.PD K) ↥LL.1 s : (↥LL.1)ˣ) : ↥LL.1)) := by
  first | exact @GlobalTheory.HTW.Rec.continuous_cycLL_period | exact GlobalTheory.HTW.Rec.continuous_cycLL_period | (intros; apply GlobalTheory.HTW.Rec.continuous_cycLL_period <;> assumption)
