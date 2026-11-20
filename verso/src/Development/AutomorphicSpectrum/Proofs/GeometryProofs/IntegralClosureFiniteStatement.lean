import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureFinite
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.finite_integralClosure_of_essFiniteType_int` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIntegralClosureFinite.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.integral_closure_finite : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.EssFiniteType ℤ A] (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.finite_integralClosure_of_essFiniteType_int | exact GlobalTheory.CompanionTheory.Ar.finite_integralClosure_of_essFiniteType_int | (intros; apply GlobalTheory.CompanionTheory.Ar.finite_integralClosure_of_essFiniteType_int <;> assumption)
