import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowerBasisCoordsIsTorusHermitianIsometry
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPowerBasisCoordsIsTorusHermitianIsometry.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.powerBasisCoords_isTorusHermitianIsometry : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k], IsIsom P k (GlobalTheory.TrUnitLat.gramOne P) 1 (GlobalTheory.TrUnitLat.coordEquiv P k) := by
  first | exact @GlobalTheory.TrUnitLat.isIsom_coordEquiv | exact GlobalTheory.TrUnitLat.isIsom_coordEquiv | (intros; apply GlobalTheory.TrUnitLat.isIsom_coordEquiv <;> assumption)
