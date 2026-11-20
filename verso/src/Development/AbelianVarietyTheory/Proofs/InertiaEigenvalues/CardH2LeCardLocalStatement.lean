import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LeCardLocal
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.card_H2_le_of_local_duality` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCardH2LeCardLocal.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.card_H2_le_card_local : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M), 0 < r → ContAction rho → Finite (H2 rho) ∧ Nat.card (H2 rho) ≤ Nat.card M := by
  first | exact @GlobalTheory.card_H2_le_of_local_duality | exact GlobalTheory.card_H2_le_of_local_duality | (intros; apply GlobalTheory.card_H2_le_of_local_duality <;> assumption)
