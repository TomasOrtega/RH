import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTranslateLiftsSemiAbelianTripleMap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TransLift.lift_isTranslate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTangentTranslateLiftsSemiAbelianTripleMap.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.tangentTranslate_lifts_semiAbelianTripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (x : Sp R ⟶ X) (x' : Sp R' ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (u : Sp (DualNumber R) ⟶ t.G.left) (u' : Sp (DualNumber R') ⟶ t'.G.left), IsTanAtG t x u → IsTanAtG t' x' u' → u' ≫ m.φ = spMap (dualMap ψ) ≫ u → ∀ (S : Type) [CommRing S] (φS : R' →+* S) (g₀' : Sp S ⟶ t'.G.left), g₀' ≫ t'.G.hom = spMap φS ≫ x' → ∀ w : Sp (DualNumber S) ⟶ t.G.left, IsTranslate t (φS.comp ψ) (g₀' ≫ m.φ) u w → ∃ w' : Sp (DualNumber S) ⟶ t'.G.left, w' ≫ m.φ = w ∧ IsTranslate t' φS g₀' u' w' := by
  first | exact @GlobalTheory.TransLift.lift_isTranslate | exact GlobalTheory.TransLift.lift_isTranslate | (intros; apply GlobalTheory.TransLift.lift_isTranslate <;> assumption)
