import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModuliObjectSpreadNormalDomain
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUnitaryModuliObjectSpreadNormalDomain.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.exists_unitaryModuliObject_spread_normal_domain : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (b : c.F →+* A) (t : SAB H (Sp A)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → GlobalTheory.TChart.TorsRat t.G l.M' → ∀ (K : Type) [Field K] (g : A →+* K) (sK : Sp K ⟶ Sp (KA l)) (oK : Obj D l (baseKA l) sK), sK = spMap g ≫ spMap (b.comp (IntermediateField.inclusion c.le).toRingHom) → SABMap oK.t t (spMap g) → ∃ o : Obj D l (baseKA l) (spMap (b.comp (IntermediateField.inclusion c.le).toRingHom)), o.t = t ∧ Nonempty (ObjMap oK o (spMap g)) := by
  first | exact @GlobalTheory.ObjSpread.exists_obj | exact GlobalTheory.ObjSpread.exists_obj | (intros; apply GlobalTheory.ObjSpread.exists_obj <;> assumption)
