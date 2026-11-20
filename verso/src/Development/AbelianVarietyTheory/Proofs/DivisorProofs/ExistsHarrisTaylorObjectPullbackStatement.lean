import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UPel.HT.BaseChange.exists_objMap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHarrisTaylorObjectPullback.lean&line=156#L156)
-/
theorem _root_.GlobalTheory.T.exists_harrisTaylorObjectPullback : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (f : S' ⟶ S), f ≫ s = s' → ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  first | exact @GlobalTheory.UPel.HT.BaseChange.exists_objMap | exact GlobalTheory.UPel.HT.BaseChange.exists_objMap | (intros; apply GlobalTheory.UPel.HT.BaseChange.exists_objMap <;> assumption)
