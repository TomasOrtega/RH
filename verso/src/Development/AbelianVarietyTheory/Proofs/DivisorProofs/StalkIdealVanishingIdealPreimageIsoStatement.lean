import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkIdealVanishingIdealPreimageIso
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStalkIdealVanishingIdealPreimageIso.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.stalkIdeal_vanishingIdeal_preimage_iso : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (Z : TopologicalSpace.Closeds X) (Z' : TopologicalSpace.Closeds X'), (Z' : Set X') = f ⁻¹' (Z : Set X) → ∀ (U : X.affineOpens) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal Z') x = ((Scheme.IdealSheafData.vanishingIdeal Z).ideal U).map ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.comp (f.app U.1).hom) := by
  first | exact @GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage | exact GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage | (intros; apply GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage <;> assumption)
