import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicElementHomogRelation
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FAlgebraicElementHomogRelation.lean&line=223#L223)
-/
theorem _root_.GlobalTheory.T.algebraic_element_homog_relation : ∀ (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (i : Ω₀ →+* Ω) (α : Ω), Birational y₀ → (letI := i.toAlgebra; IsAlgebraic Ω₀ α) → ∃ (n : ℕ) (c : ℕ → MRing J₀) (a : K₀ → ℕ) (G : MRing J₀) (b : K₀ → ℕ), (∀ j, IsMultiHomog (c j) a) ∧ IsMultiHomog G b ∧ G ∉ mCoordIdeal y₀ ∧ (∑ j ∈ Finset.range (n + 1), i (aeval y₀ (c j)) * α ^ j = 0) ∧ ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) G) ≠ 0 → ∀ τ : ℂ, ∑ j ∈ Finset.range (n + 1), eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * eval w (map (Int.castRingHom ℂ) (c j)) * τ ^ (j - 1) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly | exact GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly | (intros; apply GlobalTheory.CompanionTheory.Ar.AlgPoly.algebraic_form_poly <;> assumption)
