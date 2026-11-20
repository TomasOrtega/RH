import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EllipticPart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrEllSum.ellipticPart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FEllipticPart.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.elliptic_part : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPart := by
  first | exact @GlobalTheory.TrEllSum.ellipticPart | exact GlobalTheory.TrEllSum.ellipticPart | (intros; apply GlobalTheory.TrEllSum.ellipticPart <;> assumption)
