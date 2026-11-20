import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRationalDiagonalHomBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryRationalDiagonalHomBijective.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.unitaryRationalDiagonalHom_bijective : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Function.Bijective (diagH σ J F) := by
  first | exact @GlobalTheory.TwistRatBij.diagH_bijective | exact GlobalTheory.TwistRatBij.diagH_bijective | (intros; apply GlobalTheory.TwistRatBij.diagH_bijective <;> assumption)
