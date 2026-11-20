import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFiniteIntegralClosureOfEssFiniteTypeIntDomain.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.finite_integralClosure_of_essFiniteType_int_domain : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.EssFiniteType ℤ D], Module.Finite D (integralClosure D (FractionRing D)) := by
  first | exact @GlobalTheory.finite_integralClosure_of_essFiniteType_int | exact GlobalTheory.finite_integralClosure_of_essFiniteType_int | (intros; apply GlobalTheory.finite_integralClosure_of_essFiniteType_int <;> assumption)
