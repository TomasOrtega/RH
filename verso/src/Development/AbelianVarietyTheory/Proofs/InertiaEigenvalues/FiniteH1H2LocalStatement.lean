import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism.GaloisCohomology ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finite_H1_H2_of_localTateDuality` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFiniteH1H2Local.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.finite_H1_H2_local : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by
  first | exact @GlobalTheory.finite_H1_H2_of_localTateDuality | exact GlobalTheory.finite_H1_H2_of_localTateDuality | (intros; apply GlobalTheory.finite_H1_H2_of_localTateDuality <;> assumption)
