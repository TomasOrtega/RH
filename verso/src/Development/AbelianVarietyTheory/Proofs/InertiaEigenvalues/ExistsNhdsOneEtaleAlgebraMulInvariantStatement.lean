import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneEtaleAlgebraMulInvariant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsNhdsOneEtaleAlgebraMulInvariant.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ : A.L → ℂ), IsTest φ → ∃ U ∈ 𝓝 (1 : A.K), ∀ s ∈ U, ∀ s' ∈ U, s * s' = 1 → ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
  first | exact @GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant | exact GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant | (intros; apply GlobalTheory.JR.MulInv.exists_nhds_one_mul_invariant <;> assumption)
