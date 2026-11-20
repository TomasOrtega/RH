import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyCompanionMatrixEtaleGeneratorSeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCharpolyCompanionMatrixEtaleGeneratorSeparable.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.charpoly_companionMatrix_etaleGenerator_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → (companion p).charpoly.Separable := by
  first | exact @GlobalTheory.JR.LinDesc.charpoly_companion_separable | exact GlobalTheory.JR.LinDesc.charpoly_companion_separable | (intros; apply GlobalTheory.JR.LinDesc.charpoly_companion_separable <;> assumption)
