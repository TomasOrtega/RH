import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UPel.HT.objMap_comp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHarrisTaylorObjectPullbackComp.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.harrisTaylorObjectPullback_comp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → Nonempty (ObjMap o₁ o₃ (f ≫ g)) := by
  first | exact @GlobalTheory.UPel.HT.objMap_comp | exact GlobalTheory.UPel.HT.objMap_comp | (intros; apply GlobalTheory.UPel.HT.objMap_comp <;> assumption)
