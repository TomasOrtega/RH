import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAdelicGLComplexConjCommutesOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.smooth_conj_commutes_act` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothAdelicGLComplexConjCommutesOperators.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.smooth_adelic_GL_complex_conj_commutes_operators : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ C : Sm E a ≃ₗ⋆[ℂ] Sm E a, (∀ φ g, (C φ).1 g = starRingEnd ℂ (φ.1 g)) ∧ ∀ o φ, act o (C φ) = C (act o φ) := by
  first | exact @GlobalTheory.smooth_conj_commutes_act | exact GlobalTheory.smooth_conj_commutes_act | (intros; apply GlobalTheory.smooth_conj_commutes_act <;> assumption)
