import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleHermitianPairIsGenCompanion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsEtaleHermitianPairIsGenCompanion.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.exists_etaleHermitianPair_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F), (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  first | exact @GlobalTheory.JR.exists_et_isGen_companion | exact GlobalTheory.JR.exists_et_isGen_companion | (intros; apply GlobalTheory.JR.exists_et_isGen_companion <;> assumption)
