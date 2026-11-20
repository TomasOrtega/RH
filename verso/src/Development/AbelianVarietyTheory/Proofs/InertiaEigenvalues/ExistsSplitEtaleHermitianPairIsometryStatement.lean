import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitEtaleHermitianPairIsometry
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.exists_split_et` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsSplitEtaleHermitianPairIsometry.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.exists_split_etaleHermitianPair_isometry : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  first | exact @GlobalTheory.JR.exists_split_et | exact GlobalTheory.JR.exists_split_et | (intros; apply GlobalTheory.JR.exists_split_et <;> assumption)
