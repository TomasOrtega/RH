import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceTowerFiniteEtaleHermitianPair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTraceTowerFiniteEtaleHermitianPair.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.trace_tower_finiteEtaleHermitianPair : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (z : A.L), Algebra.trace F A.K (Algebra.trace A.K A.L z) = Algebra.trace F E (Algebra.trace E A.L z) := by
  first | exact @GlobalTheory.trace_tower_et | exact GlobalTheory.trace_tower_et | (intros; apply GlobalTheory.trace_tower_et <;> assumption)
