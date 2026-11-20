import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyHaarDetEqOneNearOne
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEventuallyHaarDetEqOneNearOne.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.eventually_haar_det_eq_one_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ᶠ g in nhds (1 : GL (Fin n) k), MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one | exact GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one | (intros; apply GlobalTheory.CompanionTheory.LocalModule.distribHaarChar_det_eventually_eq_one <;> assumption)
