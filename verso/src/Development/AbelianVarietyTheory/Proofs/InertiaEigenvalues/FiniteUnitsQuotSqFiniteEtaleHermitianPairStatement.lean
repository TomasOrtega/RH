import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitsQuotSqFiniteEtaleHermitianPair
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteUnitsQuotSqFiniteEtaleHermitianPair.lean&line=156#L156)
-/
theorem _root_.GlobalTheory.T.finite_units_quot_sq_finiteEtaleHermitianPair : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Finite (A.Kˣ ⧸ (powMonoidHom 2 : A.Kˣ →* A.Kˣ).range) := by
  first | exact @GlobalTheory.Et.finite_units_quot_sq | exact GlobalTheory.Et.finite_units_quot_sq | (intros; apply GlobalTheory.Et.finite_units_quot_sq <;> assumption)
