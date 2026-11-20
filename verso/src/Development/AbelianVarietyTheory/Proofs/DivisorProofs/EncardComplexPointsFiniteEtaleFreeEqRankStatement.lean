import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointsFiniteEtaleFreeEqRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCover
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEncardComplexPointsFiniteEtaleFreeEqRank.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.encard_complexPoints_finiteEtaleFree_eq_rank : ∀ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (δ : ℕ), f.Etale → f.Finite → (letI := f.toAlgebra; Module.Free A B ∧ Module.finrank A B = δ) → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (δ : ℕ∞) := by
  first | exact @GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank | (intros; apply GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank <;> assumption)
