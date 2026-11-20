import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FJacquetRallisInvKRegularIffIsUnit.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → Function.Bijective (fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a)) ∧ ∀ a : A.K, (∀ i : ℕ, mom (sec (A.invK τ p lam a)) i = Algebra.trace F A.K (τ ^ i * a)) ∧ (Delta (A.invK τ p lam a) ≠ 0 ↔ IsUnit a) := by
  first | exact @GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | exact GlobalTheory.JR.EtInv.invK_regular_iff_isUnit | (intros; apply GlobalTheory.JR.EtInv.invK_regular_iff_isUnit <;> assumption)
