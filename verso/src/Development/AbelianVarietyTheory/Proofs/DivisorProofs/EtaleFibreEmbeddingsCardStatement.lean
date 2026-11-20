import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFibreEmbeddingsCard
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaleFibre.encard_points_eq_finrank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEtaleFibreEmbeddingsCard.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.etale_fibre_embeddings_card : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] (f : A →+* B), f.Finite → f.Etale → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (letI := f.toAlgebra; Module.finrank A B : ℕ) := by
  first | exact @GlobalTheory.EtaleFibre.encard_points_eq_finrank | exact GlobalTheory.EtaleFibre.encard_points_eq_finrank | (intros; apply GlobalTheory.EtaleFibre.encard_points_eq_finrank <;> assumption)
