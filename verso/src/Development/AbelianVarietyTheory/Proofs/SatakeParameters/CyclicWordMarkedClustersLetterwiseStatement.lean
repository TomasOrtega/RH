import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordMarkedClustersLetterwise
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTW.Rec.clusters_letterwise` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCyclicWordMarkedClustersLetterwise.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.cyclicWordMarkedClusters_letterwise : ∀ {n : ℕ} (th : ZMod n → Prop) (j : ℕ), Clusters th j → ∀ t, th t → (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ th (t - k)) ∨ ∃ d : ℕ, 1 ≤ d ∧ d ≤ j ∧ th (t - d) ∧ ∀ k : ℕ, 1 ≤ k → k ≤ d + j → k ≠ d → ¬ th (t - k) := by
  first | exact @GlobalTheory.HTW.Rec.clusters_letterwise | exact GlobalTheory.HTW.Rec.clusters_letterwise | (intros; apply GlobalTheory.HTW.Rec.clusters_letterwise <;> assumption)
