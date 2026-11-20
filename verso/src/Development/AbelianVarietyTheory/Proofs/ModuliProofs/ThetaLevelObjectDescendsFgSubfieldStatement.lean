import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FThetaLevelObjectDescendsFgSubfield.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.thetaLevel_object_descends_fg_subfield : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) := by
  first | exact @GlobalTheory.ThetaDescent.descends_to_fg_subfield | exact GlobalTheory.ThetaDescent.descends_to_fg_subfield | (intros; apply GlobalTheory.ThetaDescent.descends_to_fg_subfield <;> assumption)
