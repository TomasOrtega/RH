import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTraceEqFinsumGeometricPointsEtale
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsTraceEqFinsumGeometricPointsEtale.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_trace_eq_finsum_geometric_points_etale : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], Module.Finite R B → Algebra.Etale R B → ∀ b : B, ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), φ v = ∑ᶠ χ : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}, χ.1 b := by
  first | exact @GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum | exact GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum | (intros; apply GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum <;> assumption)
