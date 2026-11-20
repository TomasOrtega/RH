import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointInOpenOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGenericPointInOpenOfInjective.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.generic_point_in_open_of_injective : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X), Function.Injective (Scheme.stalkClosedPointTo ξ).hom → Set.range (jK R ≫ ξ) ⊆ Set.range Z.j := by
  first | exact @GlobalTheory.GenericRange.range_jK_comp_subset | exact GlobalTheory.GenericRange.range_jK_comp_subset | (intros; apply GlobalTheory.GenericRange.range_jK_comp_subset <;> assumption)
