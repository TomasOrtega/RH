import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSum
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Frames.existsUnique_eigen_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnitaryExistence%2FExistsUniqueCmEmbeddingEigenvectorSum.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.existsUnique_cmEmbedding_eigenvector_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (N : Type) [AddCommGroup N] [Module S N] (ρ : 𝓞 E →+* Module.End S N) (m : N), ∃! f : (E →+* ℂ) → N, (∀ τ a, ρ a (f τ) = algebraMap c.F S (embK c τ a) • f τ) ∧ ∑ τ, f τ = m := by
  first | exact @GlobalTheory.Frames.existsUnique_eigen_sum | exact GlobalTheory.Frames.existsUnique_eigen_sum | (intros; apply GlobalTheory.Frames.existsUnique_eigen_sum <;> assumption)
