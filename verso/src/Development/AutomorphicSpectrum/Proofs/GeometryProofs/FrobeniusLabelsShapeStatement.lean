import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusLabelsShape
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFrobeniusLabelsShape.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.frobenius_labels_shape : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E], (∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) → ∀ (H : Host E) (l : Level H) (c : Coeff l) [Fintype (CMType H)] [DecidableEq (CMType H)], ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p : ℕ, p.Prime → IsFrobLabels c p (φ p)) ∧ FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels | exact GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.exists_frob_labels <;> assumption)
