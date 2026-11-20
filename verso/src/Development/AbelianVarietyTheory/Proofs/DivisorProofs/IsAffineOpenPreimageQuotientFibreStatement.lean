import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibre
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsAffineOpenPreimageQuotientFibre.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_quotientFibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | exact GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | (intros; apply GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre <;> assumption)
