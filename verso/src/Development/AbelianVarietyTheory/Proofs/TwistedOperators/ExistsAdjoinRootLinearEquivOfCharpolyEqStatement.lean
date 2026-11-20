import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdjoinRootLinearEquivOfCharpolyEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsAdjoinRootLinearEquivOfCharpolyEq.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (P : PPol σ n) (A : Matrix (Fin n) (Fin n) E), A.charpoly = P.1 → ∃ φ : Fld P ≃ₗ[E] (Fin n → E), ∀ y, A *ᵥ φ y = φ (alpha P * y) := by
  first | exact @GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | exact GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly | (intros; apply GlobalTheory.TrEll.exists_linearEquiv_mulVec_of_charpoly <;> assumption)
