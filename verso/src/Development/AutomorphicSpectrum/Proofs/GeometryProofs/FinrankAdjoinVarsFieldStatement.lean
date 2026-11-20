import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsField
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFinrankAdjoinVarsField.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.finrank_adjoin_vars_field : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ), 0 < d → (letI := fn.toAlgebra; Module.finrank Ω₀ Ω = d) → letI := ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I => algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q))) (FractionRing (MvPolynomial I Ω)) = d := by
  first | exact @GlobalTheory.CompanionTheory.FieldDeg.finrank_adjoin_vars | exact GlobalTheory.CompanionTheory.FieldDeg.finrank_adjoin_vars | (intros; apply GlobalTheory.CompanionTheory.FieldDeg.finrank_adjoin_vars <;> assumption)
