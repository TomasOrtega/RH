import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClusterDepthAtPrimeEqLeastPowerDepth
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.Rec.jA_eq_depth` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FClusterDepthAtPrimeEqLeastPowerDepth.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.clusterDepthAtPrime_eq_leastPowerDepth : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), 11 ≤ l → (l : ℝ) < LevelStarExponents.lA L → jA L l = depth L l := by
  first | exact @GlobalTheory.HTW.Rec.jA_eq_depth | exact GlobalTheory.HTW.Rec.jA_eq_depth | (intros; apply GlobalTheory.HTW.Rec.jA_eq_depth <;> assumption)
