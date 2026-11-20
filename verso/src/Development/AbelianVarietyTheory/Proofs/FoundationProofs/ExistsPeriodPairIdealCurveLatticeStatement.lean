import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CurveLattice.exists_periodPair_lamOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsPeriodPairIdealCurveLattice.lean&line=112#L112)
-/
theorem _root_.GlobalTheory.T.exists_periodPair_idealCurveLattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  first | exact @GlobalTheory.CurveLattice.exists_periodPair_lamOf | exact GlobalTheory.CurveLattice.exists_periodPair_lamOf | (intros; apply GlobalTheory.CurveLattice.exists_periodPair_lamOf <;> assumption)
