import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProperModelFinitelyGeneratedSubring
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSmoothProperModelFinitelyGeneratedSubring.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.exists_smooth_proper_model_finitelyGenerated_subring : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∃ (R : Subring k) (X₀ : Scheme.{0}) (f₀ : X₀ ⟶ Sp R) (π : X ⟶ X₀), Algebra.FiniteType ℤ R ∧ Smooth f₀ ∧ IsProper f₀ ∧ IsPullback π f f₀ (spMap R.subtype) := by
  first | exact @GlobalTheory.SmoothProperModel.exists_smooth_proper_model | exact GlobalTheory.SmoothProperModel.exists_smooth_proper_model | (intros; apply GlobalTheory.SmoothProperModel.exists_smooth_proper_model <;> assumption)
