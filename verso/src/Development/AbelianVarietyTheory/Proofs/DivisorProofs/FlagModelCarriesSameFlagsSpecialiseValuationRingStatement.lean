import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagModelCarriesSameFlagsSpecialiseValuationRing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagModelCarriesSameFlagsSpecialiseValuationRing.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X → ∀ (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (A : Type) [CommRing A] [IsDomain A] [ValuationRing A] (u : Sp A ⟶ X.YY) (v : Sp A ⟶ C.Y.X), u ≫ X.π = v ≫ C.π ≫ GlobalTheory.Toroidal.genι Y → GlobalTheory.VarFlag.Rel X.F C (spMap (algebraMap A (FractionRing A)) ≫ u) (spMap (algebraMap A (FractionRing A)) ≫ v) → GlobalTheory.VarFlag.Rel X.F C (spMap (IsLocalRing.residue A) ≫ u) (spMap (IsLocalRing.residue A) ≫ v) := by
  first | exact @GlobalTheory.VarFlag.rel_specialise | exact GlobalTheory.VarFlag.rel_specialise | (intros; apply GlobalTheory.VarFlag.rel_specialise <;> assumption)
