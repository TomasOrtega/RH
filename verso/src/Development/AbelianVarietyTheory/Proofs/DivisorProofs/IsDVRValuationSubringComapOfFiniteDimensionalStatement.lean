import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDVRValuationSubringComapOfFiniteDimensional
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RestrictDVR.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsDVRValuationSubringComapOfFiniteDimensional.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.isDVR_valuationSubring_comap_of_finiteDimensional : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) := by
  first | exact @GlobalTheory.RestrictDVR.main | exact GlobalTheory.RestrictDVR.main | (intros; apply GlobalTheory.RestrictDVR.main <;> assumption)
