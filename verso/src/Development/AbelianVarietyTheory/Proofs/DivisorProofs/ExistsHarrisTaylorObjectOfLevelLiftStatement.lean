import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfLevelLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HTLift.exists_obj_of_isLift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHarrisTaylorObjectOfLevelLift.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.exists_harrisTaylorObject_of_levelLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S) (lv : D.La → (T ⟶ o.A)), IsLift o N' T lv → ∃ (o'' : Obj b N' (T.hom ≫ s)) (mm : ObjMap (o''.forget N hd hc) o T.hom), ∀ a, (o''.eta a).left ≫ mm.φ = (lv a).left := by
  first | exact @GlobalTheory.HTLift.exists_obj_of_isLift | exact GlobalTheory.HTLift.exists_obj_of_isLift | (intros; apply GlobalTheory.HTLift.exists_obj_of_isLift <;> assumption)
